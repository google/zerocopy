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

/-! ## Part 1: Selected `KnownLayout` MIR Sealing-Marker Verification -/

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
      (idAt 0 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_0, Captured.Shard_000.body_0, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m01 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.UnitMarkerAt Captured.program 1
      (idAt 1 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_1, Captured.Shard_000.body_1, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m02 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.UnitMarkerAt Captured.program 2
      (idAt 2 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_2, Captured.Shard_000.body_2, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m03 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.UnitMarkerAt Captured.program 3
      (idAt 3 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_3, Captured.Shard_000.body_3, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m04 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.UnitMarkerAt Captured.program 4
      (idAt 4 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_4, Captured.Shard_000.body_4, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m05 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.UnitMarkerAt Captured.program 5
      (idAt 5 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_5, Captured.Shard_000.body_5, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m06 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.UnitMarkerAt Captured.program 6
      (idAt 6 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_6, Captured.Shard_000.body_6, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m07 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.UnitMarkerAt Captured.program 7
      (idAt 7 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_7, Captured.Shard_000.body_7, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m08 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.UnitMarkerAt Captured.program 8
      (idAt 8 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_8, Captured.Shard_000.body_8, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m09 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.UnitMarkerAt Captured.program 9
      (idAt 9 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_9, Captured.Shard_000.body_9, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.UnitMarkerAt Captured.program 10
      (idAt 10 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_10, Captured.Shard_001.body_0, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.UnitMarkerAt Captured.program 11
      (idAt 11 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_11, Captured.Shard_001.body_1, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.UnitMarkerAt Captured.program 12
      (idAt 12 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_12, Captured.Shard_001.body_2, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.UnitMarkerAt Captured.program 13
      (idAt 13 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_13, Captured.Shard_001.body_3, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.UnitMarkerAt Captured.program 14
      (idAt 14 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_14, Captured.Shard_001.body_4, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.UnitMarkerAt Captured.program 15
      (idAt 15 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_15, Captured.Shard_001.body_5, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.UnitMarkerAt Captured.program 16
      (idAt 16 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_16, Captured.Shard_001.body_6, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.UnitMarkerAt Captured.program 17
      (idAt 17 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_17, Captured.Shard_001.body_7, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.UnitMarkerAt Captured.program 18
      (idAt 18 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_18, Captured.Shard_001.body_8, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.UnitMarkerAt Captured.program 19
      (idAt 19 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_19, Captured.Shard_001.body_9, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.UnitMarkerAt Captured.program 20
      (idAt 20 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_20, Captured.Shard_002.body_0, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.UnitMarkerAt Captured.program 21
      (idAt 21 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_21, Captured.Shard_002.body_1, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.UnitMarkerAt Captured.program 22
      (idAt 22 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_22, Captured.Shard_002.body_2, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.UnitMarkerAt Captured.program 23
      (idAt 23 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_23, Captured.Shard_002.body_3, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.UnitMarkerAt Captured.program 24
      (idAt 24 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_24, Captured.Shard_002.body_4, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.UnitMarkerAt Captured.program 25
      (idAt 25 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_25, Captured.Shard_002.body_5, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.UnitMarkerAt Captured.program 26
      (idAt 26 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_26, Captured.Shard_002.body_6, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.UnitMarkerAt Captured.program 27
      (idAt 27 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_27, Captured.Shard_002.body_7, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.UnitMarkerAt Captured.program 28
      (idAt 28 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_28, Captured.Shard_002.body_8, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.UnitMarkerAt Captured.program 29
      (idAt 29 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_29, Captured.Shard_002.body_9, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.UnitMarkerAt Captured.program 30
      (idAt 30 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_30, Captured.Shard_002.body_10, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.UnitMarkerAt Captured.program 31
      (idAt 31 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_31, Captured.Shard_003.body_0, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.UnitMarkerAt Captured.program 32
      (idAt 32 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_32, Captured.Shard_003.body_1, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.UnitMarkerAt Captured.program 33
      (idAt 33 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_33, Captured.Shard_003.body_2, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.UnitMarkerAt Captured.program 34
      (idAt 34 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_34, Captured.Shard_003.body_3, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.UnitMarkerAt Captured.program 35
      (idAt 35 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_35, Captured.Shard_003.body_4, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.UnitMarkerAt Captured.program 36
      (idAt 36 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_36, Captured.Shard_003.body_5, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.UnitMarkerAt Captured.program 37
      (idAt 37 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_37, Captured.Shard_003.body_6, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.UnitMarkerAt Captured.program 38
      (idAt 38 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_38, Captured.Shard_004.body_0, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.UnitMarkerAt Captured.program 39
      (idAt 39 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_39, Captured.Shard_004.body_1, Spec.knownLayoutMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.UnitMarkerAt Captured.program 40
      (idAt 40 Spec.knownLayoutMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_40, Captured.Shard_004.body_2, Spec.knownLayoutMarkerIdentities,
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
  exact bodiesVerified_nil _

private theorem all_markers_at :
    AllMarkersAtFrom Captured.program 0 Spec.knownLayoutMarkerIdentities := by
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
  exact allMarkersAt_nil _

private theorem bodies_unique_identities :
    bodiesHaveUniqueIdentities Captured.program.bodies = true := rfl

/-! ## Part 2: Model-Side 64-Bit `DstLayout` / `TrailingSliceLayout` Proofs -/

private theorem bv64_eq_of_toNat_eq {a b : BitVec 64}
    (h : a.toNat = b.toNat) : a = b :=
  bitVec_eq_of_toNat_eq h

private theorem bv64_toNat_ofNat (n : Nat) :
    (BitVec.ofNat 64 n).toNat = n % 2 ^ 64 := rfl

private theorem bv64_toNat_add (a b : BitVec 64) :
    (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := rfl

private theorem bv64_toNat_sub (a b : BitVec 64) :
    (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 := rfl

private theorem bv64_toNat_sub_of_le {a b : BitVec 64}
    (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [bv64_toNat_sub]
  have hbLt : b.toNat < 2 ^ 64 := b.isLt
  have haLt : a.toNat < 2 ^ 64 := a.isLt
  have hSub : a.toNat - b.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) haLt
  have hSum : 2 ^ 64 - b.toNat + a.toNat = 2 ^ 64 + (a.toNat - b.toNat) := by
    have h1 : 2 ^ 64 - b.toNat + a.toNat =
        (2 ^ 64 - b.toNat + b.toNat) + (a.toNat - b.toNat) := by
      have hba : b.toNat + (a.toNat - b.toNat) = a.toNat :=
        Nat.add_sub_of_le h
      rw [Nat.add_assoc, hba]
    rw [h1, Nat.sub_add_cancel (Nat.le_of_lt hbLt)]
  rw [hSum, Nat.add_mod_left, Nat.mod_eq_of_lt hSub]

private theorem two_pow_64_val : (2 : Nat) ^ 64 = Nat.pow 2 64 := rfl

private theorem two_pow_succ (w : Nat) : 2 ^ (w + 1) = 2 * 2 ^ w := by
  rw [Nat.pow_succ, Nat.mul_comm]

private theorem two_pow_add (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b := by
  induction b with
  | zero => rw [Nat.add_zero]; exact (Nat.mul_one _).symm
  | succ b ih =>
    rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

private theorem pow2_le_of_le {i j : Nat} (h : i ≤ j) : 2 ^ i ≤ 2 ^ j :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

private theorem pow2_lt_64 {k : Nat} (hk : k < 64) : 2 ^ k < 2 ^ 64 := by
  have hk1 : k + 1 ≤ 64 := hk
  have hLe := pow2_le_of_le hk1
  rw [Nat.pow_succ] at hLe
  have hPos := Nat.two_pow_pos k
  have hLt2 : 2 ^ k < 2 ^ k * 2 := by
    change 2 ^ k < 2 ^ k * (1 + 1)
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.lt_add_of_pos_right hPos
  exact Nat.lt_of_lt_of_le hLt2 hLe

private theorem pow2_dvd_64 {k : Nat} (hk : k ≤ 64) : 2 ^ k ∣ 2 ^ 64 := by
  have hSum : k + (64 - k) = 64 := Nat.add_sub_of_le hk
  refine ⟨2 ^ (64 - k), ?_⟩
  rw [← two_pow_add, hSum]

private theorem nat_ble_true : ∀ (a b : Nat), a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | Nat.succ _, 0, h => nomatch h
  | Nat.succ a, Nat.succ b, h =>
      nat_ble_true a b (Nat.le_of_succ_le_succ h)

private theorem nat_ble_false : ∀ (a b : Nat), b < a → Nat.ble a b = false
  | 0, _, h => nomatch h
  | Nat.succ _, 0, _ => rfl
  | Nat.succ a, Nat.succ b, h =>
      nat_ble_false a b (Nat.lt_of_succ_lt_succ h)

private theorem nat_blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  nat_ble_true (a + 1) b h

private theorem nat_blt_false {a b : Nat} (h : b ≤ a) :
    Nat.blt a b = false :=
  nat_ble_false (a + 1) b (Nat.lt_succ_of_le h)

private theorem bool_bne_false : ∀ x : Bool, bne x false = x
  | false => rfl
  | true => rfl

private theorem nat_dvd_refl (a : Nat) : a ∣ a := ⟨1, (Nat.mul_one a).symm⟩

private theorem nat_dvd_zero (a : Nat) : a ∣ 0 := ⟨0, (Nat.mul_zero a).symm⟩

private theorem nat_dvd_mul_right (a b : Nat) : a ∣ a * b := ⟨b, rfl⟩

private theorem nat_dvd_mul_left_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) :
    a ∣ c * b := by
  let ⟨q, hq⟩ := h
  refine ⟨c * q, ?_⟩
  rw [hq, Nat.mul_left_comm]

private theorem nat_dvd_add {d a b : Nat} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ a + b := by
  let ⟨qa, hqa⟩ := ha
  let ⟨qb, hqb⟩ := hb
  exact ⟨qa + qb, by rw [hqa, hqb, Nat.mul_add]⟩

private theorem nat_dvd_of_mod_eq_zero {a b : Nat} (h : a % b = 0) :
    b ∣ a := by
  refine ⟨a / b, ?_⟩
  have h1 := Nat.div_add_mod a b
  rw [h, Nat.add_zero] at h1
  exact h1.symm

private theorem nat_lt_of_mul_lt_mul_right {a b c : Nat}
    (h : a * c < b * c) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge =>
    exact False.elim (Nat.not_lt_of_ge (Nat.mul_le_mul_right c hge) h)

private theorem nat_lt_of_add_lt_add_left {k a b : Nat}
    (h : k + a < k + b) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge =>
    exact False.elim (Nat.not_lt_of_ge (Nat.add_le_add_left hge k) h)

private theorem nat_mod_add_mod (a b d : Nat) :
    (a % d + b) % d = (a + b) % d := by
  calc (a % d + b) % d
      = (d * (a / d) + (a % d + b)) % d :=
          (Nat.mul_add_mod_self_left d (a / d) _).symm
    _ = ((d * (a / d) + a % d) + b) % d := by rw [Nat.add_assoc]
    _ = (a + b) % d := by rw [Nat.div_add_mod]

private theorem nat_add_mod_mod (a b d : Nat) :
    (a + b % d) % d = (a + b) % d := by
  rw [Nat.add_comm a (b % d), nat_mod_add_mod, Nat.add_comm b a]

private theorem nat_add_mod (a b d : Nat) :
    (a + b) % d = (a % d + b % d) % d :=
  (nat_add_mod_mod a b d).symm.trans (nat_mod_add_mod a (b % d) d).symm

private theorem nat_mod_mod (a d : Nat) : (a % d) % d = a % d := by
  have h := nat_mod_add_mod a 0 d
  rw [Nat.add_zero, Nat.add_zero] at h
  exact h

private theorem nat_mul_mod_mod (a b d : Nat) :
    (a * (b % d)) % d = (a * b) % d := by
  have hB : b = d * (b / d) + b % d := (Nat.div_add_mod b d).symm
  calc (a * (b % d)) % d
      = (d * (a * (b / d)) + a * (b % d)) % d :=
          (Nat.mul_add_mod_self_left d (a * (b / d)) _).symm
    _ = (a * (d * (b / d) + b % d)) % d := by
          rw [Nat.mul_add, Nat.mul_left_comm d a (b / d)]
    _ = (a * b) % d := by rw [← hB]

private theorem nat_mod_mod_of_dvd (a : Nat) {m n : Nat} (h : m ∣ n) :
    (a % n) % m = a % m := by
  let ⟨q, hq⟩ := h
  calc (a % n) % m
      = (m * (q * (a / n)) + a % n) % m :=
          (Nat.mul_add_mod_self_left m (q * (a / n)) _).symm
    _ = ((m * q) * (a / n) + a % n) % m := by rw [Nat.mul_assoc]
    _ = (n * (a / n) + a % n) % m := by rw [← hq]
    _ = a % m := by rw [Nat.div_add_mod]

private theorem mod_twoPow_of_add_mul {x y d : Nat} (hd : d ∣ x) :
    (x + y) % d = y % d := by
  let ⟨q, hq⟩ := hd
  rw [hq, Nat.mul_add_mod_self_left]

private theorem nat_sub_eq_of_eq_add {a b c : Nat} (h : a = b + c) :
    a - c = b := by
  rw [h, Nat.add_sub_cancel]

private theorem bool_and_true_iff {a b : Bool} :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem bool_and_false_left {b : Bool} : (false && b) = false := rfl

private theorem bool_and_false_right {a : Bool} : (a && false) = false := by
  cases a <;> rfl

/-! ### Bit-Extensionality Core over `Spec.bitwiseNatRec` and `Spec.nthBit` -/

private theorem bitwiseNatRec_succ (f : Bool → Bool → Bool) (w a b : Nat) :
    Spec.bitwiseNatRec f (w + 1) a b =
      2 * Spec.bitwiseNatRec f w (a / 2) (b / 2) +
        if f (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1)
        then 1 else 0 := rfl

private theorem bitwiseNatRec_lt (f : Bool → Bool → Bool) :
    ∀ (w a b : Nat), Spec.bitwiseNatRec f w a b < 2 ^ w
  | 0, _, _ => Nat.zero_lt_one
  | w + 1, a, b => by
    rw [bitwiseNatRec_succ, two_pow_succ]
    have ih := bitwiseNatRec_lt f w (a / 2) (b / 2)
    have h1 : Spec.bitwiseNatRec f w (a / 2) (b / 2) + 1 ≤ 2 ^ w := ih
    cases f (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with
    | false =>
      have h0 : (if false = true then 1 else 0) = 0 := rfl
      rw [h0, Nat.add_zero]
      exact Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 2)
    | true =>
      have hT : (if true = true then 1 else 0) = 1 := rfl
      rw [hT]
      have hMul : 2 * Spec.bitwiseNatRec f w (a / 2) (b / 2) + 2 ≤
          2 * 2 ^ w := by
        calc 2 * Spec.bitwiseNatRec f w (a / 2) (b / 2) + 2
            = 2 * Spec.bitwiseNatRec f w (a / 2) (b / 2) + 2 * 1 := rfl
          _ = 2 * (Spec.bitwiseNatRec f w (a / 2) (b / 2) + 1) :=
              (Nat.mul_add 2 _ 1).symm
          _ ≤ 2 * 2 ^ w := Nat.mul_le_mul_left 2 h1
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hMul

private theorem div_twoPow_succ (a i : Nat) :
    a / 2 ^ (i + 1) = (a / 2) / 2 ^ i := by
  rw [two_pow_succ, Nat.div_div_eq_div_mul]

private theorem mod2_eq_of_nthBit_eq {a b : Nat}
    (h0 : Spec.nthBit a 0 = Spec.nthBit b 0) : a % 2 = b % 2 := by
  unfold Spec.nthBit at h0
  have hd1 : (2 : Nat) ^ 0 = 1 := rfl
  rw [hd1, Nat.div_one, Nat.div_one] at h0
  have ha := Nat.mod_lt a (by decide : 0 < 2)
  have hb := Nat.mod_lt b (by decide : 0 < 2)
  cases ma : a % 2 with
  | zero =>
    cases mb : b % 2 with
    | zero => rfl
    | succ kb =>
      cases kb with
      | zero => rw [ma, mb] at h0; cases h0
      | succ k =>
        rw [mb] at hb
        cases Nat.not_lt_of_le (Nat.le_add_left 2 k) hb
  | succ ka =>
    cases ka with
    | zero =>
      cases mb : b % 2 with
      | zero => rw [ma, mb] at h0; cases h0
      | succ kb =>
        cases kb with
        | zero => rfl
        | succ k =>
          rw [mb] at hb
          cases Nat.not_lt_of_le (Nat.le_add_left 2 k) hb
    | succ k =>
      rw [ma] at ha
      cases Nat.not_lt_of_le (Nat.le_add_left 2 k) ha

private theorem nat_eq_of_nthBit_eq :
    ∀ (w a b : Nat), a < 2 ^ w → b < 2 ^ w →
      (∀ i, i < w → Spec.nthBit a i = Spec.nthBit b i) → a = b
  | 0, a, b, ha, hb, _ => by
    have ha0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    have hb0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb)
    rw [ha0, hb0]
  | w + 1, a, b, ha, hb, hBits => by
    rw [Nat.pow_succ] at ha hb
    have hDivA : a / 2 < 2 ^ w :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr ha
    have hDivB : b / 2 < 2 ^ w :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr hb
    have hSub : ∀ i, i < w →
        Spec.nthBit (a / 2) i = Spec.nthBit (b / 2) i := by
      intro i hi
      have hs := hBits (i + 1) (Nat.succ_lt_succ hi)
      unfold Spec.nthBit at hs ⊢
      rw [div_twoPow_succ, div_twoPow_succ] at hs
      exact hs
    have hDivEq := nat_eq_of_nthBit_eq w (a / 2) (b / 2) hDivA hDivB hSub
    have hModEq := mod2_eq_of_nthBit_eq (hBits 0 (Nat.zero_lt_succ w))
    rw [← Nat.div_add_mod a 2, ← Nat.div_add_mod b 2, hDivEq, hModEq]

private theorem nthBit_bitwiseNatRec (f : Bool → Bool → Bool) :
    ∀ (w i a b : Nat), i < w →
      Spec.nthBit (Spec.bitwiseNatRec f w a b) i =
        f (Spec.nthBit a i) (Spec.nthBit b i)
  | 0, i, _, _, hi => False.elim (Nat.not_lt_zero i hi)
  | _ + 1, 0, a, b, _ => by
    rw [bitwiseNatRec_succ]
    unfold Spec.nthBit
    have hp : (2 : Nat) ^ 0 = 1 := rfl
    rw [hp, Nat.div_one, Nat.div_one, Nat.div_one, Nat.mul_add_mod_self_left]
    cases f (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) <;> rfl
  | w + 1, i + 1, a, b, hi => by
    have hDiv : (2 * Spec.bitwiseNatRec f w (a / 2) (b / 2) +
        if f (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) then 1 else 0) / 2 =
        Spec.bitwiseNatRec f w (a / 2) (b / 2) := by
      rw [Nat.add_comm]
      cases f (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with
      | false =>
        have h0 : (if false = true then 1 else 0) = 0 := rfl
        rw [h0, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
        exact Nat.zero_add _
      | true =>
        have h1 : (if true = true then 1 else 0) = 1 := rfl
        rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
        exact Nat.zero_add _
    have hHead : Spec.nthBit (Spec.bitwiseNatRec f (w + 1) a b) (i + 1) =
        Spec.nthBit (Spec.bitwiseNatRec f w (a / 2) (b / 2)) i := by
      unfold Spec.nthBit
      rw [bitwiseNatRec_succ, div_twoPow_succ, hDiv]
    have hIh := nthBit_bitwiseNatRec f w i (a / 2) (b / 2)
      (Nat.lt_of_succ_lt_succ hi)
    rw [hHead, hIh]
    unfold Spec.nthBit
    rw [div_twoPow_succ, div_twoPow_succ]

private theorem nthBit_zero (i : Nat) : Spec.nthBit 0 i = false := by
  unfold Spec.nthBit
  rw [Nat.zero_div]
  rfl

private theorem nthBit_eq_false_of_lt {a i : Nat} (h : a < 2 ^ i) :
    Spec.nthBit a i = false := by
  unfold Spec.nthBit
  rw [Nat.div_eq_of_lt h]
  rfl

private theorem nthBit_pow2 (k i : Nat) :
    Spec.nthBit (2 ^ k) i = Nat.beq i k := by
  cases Nat.lt_or_ge i k with
  | inl hLt =>
    have hd : k = i + ((k - i - 1) + 1) := by
      have h1 : 1 ≤ k - i := Nat.sub_pos_of_lt hLt
      have h2 : (k - i - 1) + 1 = k - i := Nat.sub_add_cancel h1
      rw [h2, Nat.add_sub_of_le (Nat.le_of_lt hLt)]
    have hNe : Nat.beq i k = false := by
      cases hEq : Nat.beq i k with
      | false => rfl
      | true =>
        have he := Nat.eq_of_beq_eq_true hEq
        subst he
        exact False.elim (Nat.lt_irrefl _ hLt)
    rw [hNe]
    unfold Spec.nthBit
    rw [hd, two_pow_add, Nat.mul_div_right _ (Nat.two_pow_pos i),
      two_pow_succ, Nat.mul_mod_right]
    rfl
  | inr hGe =>
    cases Nat.eq_or_lt_of_le hGe with
    | inl hEq =>
      subst hEq
      have hSelf : Nat.beq k k = true := Anneal.InitLemmas.nat_beq_refl k
      rw [hSelf]
      unfold Spec.nthBit
      rw [Nat.div_self (Nat.two_pow_pos k)]
      rfl
    | inr hGt =>
      have hNe : Nat.beq i k = false := by
        cases hEq : Nat.beq i k with
        | false => rfl
        | true =>
          have he := Nat.eq_of_beq_eq_true hEq
          subst he
          exact False.elim (Nat.lt_irrefl _ hGt)
      rw [hNe]
      have hLtPow : 2 ^ k < 2 ^ i := by
        have hk1 : k + 1 ≤ i := hGt
        have hLe := pow2_le_of_le hk1
        rw [Nat.pow_succ] at hLe
        have hLt2 : 2 ^ k < 2 ^ k * 2 := by
          change 2 ^ k < 2 ^ k * (1 + 1)
          rw [Nat.mul_add, Nat.mul_one]
          exact Nat.lt_add_of_pos_right (Nat.two_pow_pos k)
        exact Nat.lt_of_lt_of_le hLt2 hLe
      exact nthBit_eq_false_of_lt hLtPow

private theorem nthBit_pow2_sub_one (k i : Nat) :
    Spec.nthBit (2 ^ k - 1) i = decide (i < k) := by
  cases Nat.lt_or_ge i k with
  | inl hLt =>
    rw [decide_eq_true hLt]
    have hDPos : 0 < k - i := Nat.sub_pos_of_lt hLt
    have hDecomp : 2 ^ k - 1 = (2 ^ (k - i) - 1) * 2 ^ i + (2 ^ i - 1) := by
      have hPi := Nat.two_pow_pos i
      have hPd := Nat.two_pow_pos (k - i)
      have hPowSplit : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
        rw [← two_pow_add, Nat.sub_add_cancel (Nat.le_of_lt hLt)]
      have hLeft : 2 ^ (k - i) * 2 ^ i =
          (2 ^ (k - i) - 1) * 2 ^ i + 2 ^ i := by
        have hSub : 2 ^ (k - i) = (2 ^ (k - i) - 1) + 1 :=
          (Nat.sub_add_cancel hPd).symm
        calc 2 ^ (k - i) * 2 ^ i
            = ((2 ^ (k - i) - 1) + 1) * 2 ^ i := by rw [← hSub]
          _ = (2 ^ (k - i) - 1) * 2 ^ i + 2 ^ i := by
              rw [Nat.add_mul, Nat.one_mul]
      rw [hPowSplit, hLeft, Nat.add_sub_assoc hPi]
    unfold Spec.nthBit
    rw [hDecomp]
    have hPi := Nat.two_pow_pos i
    have hRemLt : 2 ^ i - 1 < 2 ^ i := Nat.sub_lt hPi Nat.zero_lt_one
    have hDivEq : ((2 ^ (k - i) - 1) * 2 ^ i + (2 ^ i - 1)) / 2 ^ i =
        2 ^ (k - i) - 1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hPi, Nat.div_eq_of_lt hRemLt,
        Nat.zero_add]
    rw [hDivEq]
    have hD1 : k - i = (k - i - 1) + 1 := (Nat.sub_add_cancel hDPos).symm
    rw [hD1, two_pow_succ]
    have hPowD := Nat.two_pow_pos (k - i - 1)
    have hSplitPow : 2 * 2 ^ (k - i - 1) =
        2 * (2 ^ (k - i - 1) - 1) + 2 := by
      have hSub := Nat.sub_add_cancel hPowD
      calc 2 * 2 ^ (k - i - 1)
          = 2 * ((2 ^ (k - i - 1) - 1) + 1) := by rw [hSub]
        _ = 2 * (2 ^ (k - i - 1) - 1) + 2 := by rw [Nat.mul_add, Nat.mul_one]
    rw [hSplitPow, show 2 * (2 ^ (k - i - 1) - 1) + 2 - 1 =
        2 * (2 ^ (k - i - 1) - 1) + 1 from rfl, Nat.mul_add_mod_self_left]
    rfl
  | inr hGe =>
    rw [decide_eq_false (Nat.not_lt_of_ge hGe)]
    have hLtPow : 2 ^ k - 1 < 2 ^ i :=
      Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) Nat.zero_lt_one)
        (pow2_le_of_le hGe)
    exact nthBit_eq_false_of_lt hLtPow

private theorem nthBit_mod_twoPow (a k i : Nat) :
    Spec.nthBit (a % 2 ^ k) i =
      if Nat.blt i k then Spec.nthBit a i else false := by
  cases Nat.lt_or_ge i k with
  | inl hLt =>
    have hBlt : Nat.blt i k = true := nat_blt_true hLt
    rw [ite_bool_true hBlt]
    have hDPos : 0 < k - i := Nat.sub_pos_of_lt hLt
    have hEven : 2 ∣ 2 ^ (k - i) := by
      have hD1 : k - i = (k - i - 1) + 1 := (Nat.sub_add_cancel hDPos).symm
      rw [hD1, two_pow_succ]
      exact nat_dvd_mul_right 2 _
    have hSplitA : a = (a / 2 ^ k) * 2 ^ k + (a % 2 ^ k) := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod a (2 ^ k)).symm
    have hDecompDiv : a / 2 ^ i =
        (a / 2 ^ k) * 2 ^ (k - i) + (a % 2 ^ k) / 2 ^ i := by
      have hA := congrArg (fun z => z / 2 ^ i) hSplitA
      have hPowSplit : (a / 2 ^ k) * 2 ^ k =
          ((a / 2 ^ k) * 2 ^ (k - i)) * 2 ^ i := by
        rw [Nat.mul_assoc, ← two_pow_add, Nat.sub_add_cancel (Nat.le_of_lt hLt)]
      rw [hPowSplit, Nat.add_comm _ (a % 2 ^ k),
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos i),
        Nat.add_comm ((a % 2 ^ k) / 2 ^ i)] at hA
      exact hA
    unfold Spec.nthBit
    rw [hDecompDiv, mod_twoPow_of_add_mul (nat_dvd_mul_left_of_dvd hEven _)]
  | inr hGe =>
    have hBlt : Nat.blt i k = false := nat_blt_false hGe
    rw [ite_bool_false hBlt]
    have hLtPow : a % 2 ^ k < 2 ^ i :=
      Nat.lt_of_lt_of_le (Nat.mod_lt a (Nat.two_pow_pos k)) (pow2_le_of_le hGe)
    exact nthBit_eq_false_of_lt hLtPow

private theorem bit_sub_of_lt_two_pow {w a : Nat} (ha : a < 2 ^ w) :
    Spec.bitwiseNatRec (fun x _ => !x) w a 0 + a = 2 ^ w - 1 := by
  induction w generalizing a with
  | zero =>
    have ha0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    rw [ha0]; rfl
  | succ w ih =>
    have hDivLt : a / 2 < 2 ^ w := by
      rw [two_pow_succ, Nat.mul_comm] at ha
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr ha
    have hRec := ih hDivLt
    have hStep : Spec.bitwiseNatRec (fun x _ => !x) (w + 1) a 0 =
        2 * Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0 +
          if !(Nat.beq (a % 2) 1) then 1 else 0 := rfl
    rw [hStep]
    have hModLt := Nat.mod_lt a (by decide : 0 < 2)
    have hBit : (if !(Nat.beq (a % 2) 1) then 1 else 0) + a % 2 = 1 := by
      cases hm : a % 2 with
      | zero => rfl
      | succ k =>
        cases k with
        | zero => rfl
        | succ m =>
          rw [hm] at hModLt
          cases Nat.not_lt_of_le (Nat.le_add_left 2 m) hModLt
    have hSplitA : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
    have hSum :
        2 * Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0 +
            (if !(Nat.beq (a % 2) 1) then 1 else 0) +
            (2 * (a / 2) + a % 2) =
        2 * (Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0 + a / 2) +
            ((if !(Nat.beq (a % 2) 1) then 1 else 0) + a % 2) := by
      rw [Nat.mul_add]
      rw [Nat.add_assoc (2 * Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0)]
      rw [Nat.add_left_comm (if !(Nat.beq (a % 2) 1) then 1 else 0)
        (2 * (a / 2)) (a % 2)]
      rw [← Nat.add_assoc (2 * Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0)
        (2 * (a / 2))]
    have hp := Nat.two_pow_pos w
    have hSplitPow : 2 ^ w = (2 ^ w - 1) + 1 := (Nat.sub_add_cancel hp).symm
    calc 2 * Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0 +
            (if !(Nat.beq (a % 2) 1) then 1 else 0) + a
        = 2 * Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0 +
            (if !(Nat.beq (a % 2) 1) then 1 else 0) +
            (2 * (a / 2) + a % 2) := congrArg _ hSplitA
      _ = 2 * (Spec.bitwiseNatRec (fun x _ => !x) w (a / 2) 0 + a / 2) +
            ((if !(Nat.beq (a % 2) 1) then 1 else 0) + a % 2) := hSum
      _ = 2 * (2 ^ w - 1) + 1 := by rw [hRec, hBit]
      _ = 2 * (2 ^ w - 1) + 2 - 1 :=
          (Nat.add_sub_assoc (by decide : 1 ≤ 2) _).symm
      _ = 2 * ((2 ^ w - 1) + 1) - 1 :=
          congrArg (fun z => z - 1) (Nat.mul_add 2 (2 ^ w - 1) 1).symm
      _ = 2 * 2 ^ w - 1 := by rw [← hSplitPow]
      _ = 2 ^ (w + 1) - 1 := by rw [two_pow_succ]

private theorem bv64Not_toNat (x : BitVec 64) :
    (Spec.bv64Not x).toNat = 2 ^ 64 - 1 - x.toNat := by
  have hLt := bitwiseNatRec_lt (fun a _ => !a) 64 x.toNat 0
  have hMod : (Spec.bv64Not x).toNat =
      Spec.bitwiseNatRec (fun a _ => !a) 64 x.toNat 0 :=
    Nat.mod_eq_of_lt hLt
  rw [hMod]
  exact (nat_sub_eq_of_eq_add (bit_sub_of_lt_two_pow x.isLt).symm).symm

private theorem nthBit_bv64Not (x : BitVec 64) {i : Nat} (hi : i < 64) :
    Spec.nthBit (Spec.bv64Not x).toNat i = !Spec.nthBit x.toNat i := by
  have hLt := bitwiseNatRec_lt (fun a _ => !a) 64 x.toNat 0
  have hMod : (Spec.bv64Not x).toNat =
      Spec.bitwiseNatRec (fun a _ => !a) 64 x.toNat 0 :=
    Nat.mod_eq_of_lt hLt
  rw [hMod, nthBit_bitwiseNatRec _ 64 i x.toNat 0 hi]

private theorem nthBit_bv64And (x y : BitVec 64) {i : Nat} (hi : i < 64) :
    Spec.nthBit (Spec.bv64And x y).toNat i =
      (Spec.nthBit x.toNat i && Spec.nthBit y.toNat i) := by
  have hMod : (Spec.bv64And x y).toNat =
      Spec.bitwiseNatRec and 64 x.toNat y.toNat :=
    Nat.mod_eq_of_lt (bitwiseNatRec_lt and 64 x.toNat y.toNat)
  rw [hMod, nthBit_bitwiseNatRec and 64 i x.toNat y.toNat hi]

private theorem nthBit_bv64Or (x y : BitVec 64) {i : Nat} (hi : i < 64) :
    Spec.nthBit (Spec.bv64Or x y).toNat i =
      (Spec.nthBit x.toNat i || Spec.nthBit y.toNat i) := by
  have hMod : (Spec.bv64Or x y).toNat =
      Spec.bitwiseNatRec or 64 x.toNat y.toNat :=
    Nat.mod_eq_of_lt (bitwiseNatRec_lt or 64 x.toNat y.toNat)
  rw [hMod, nthBit_bitwiseNatRec or 64 i x.toNat y.toNat hi]

private theorem nthBit_bv64Xor (x y : BitVec 64) {i : Nat} (hi : i < 64) :
    Spec.nthBit (Spec.bv64Xor x y).toNat i =
      bne (Spec.nthBit x.toNat i) (Spec.nthBit y.toNat i) := by
  have hMod : (Spec.bv64Xor x y).toNat =
      Spec.bitwiseNatRec bne 64 x.toNat y.toNat :=
    Nat.mod_eq_of_lt (bitwiseNatRec_lt bne 64 x.toNat y.toNat)
  rw [hMod, nthBit_bitwiseNatRec bne 64 i x.toNat y.toNat hi]

private theorem bv64_eq_of_nthBit_eq {a b : BitVec 64}
    (h : ∀ i, i < 64 → Spec.nthBit a.toNat i = Spec.nthBit b.toNat i) :
    a = b :=
  bv64_eq_of_toNat_eq (nat_eq_of_nthBit_eq 64 a.toNat b.toNat a.isLt b.isLt h)

private theorem bv64And_zero_left (y : BitVec 64) :
    Spec.bv64And (BitVec.ofNat 64 0) y = BitVec.ofNat 64 0 := by
  apply bv64_eq_of_nthBit_eq
  intro i hi
  rw [nthBit_bv64And _ _ hi, show (BitVec.ofNat 64 0).toNat = 0 from rfl,
    nthBit_zero, bool_and_false_left]

private theorem bv64And_lowMask (x : BitVec 64) {k : Nat} (hk : k ≤ 64) :
    (Spec.bv64And x (BitVec.ofNat 64 (2 ^ k - 1))).toNat =
      x.toNat % 2 ^ k := by
  have hMaskLt : 2 ^ k - 1 < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) Nat.zero_lt_one)
      (pow2_le_of_le hk)
  have hModLt : x.toNat % 2 ^ k < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt x.toNat (Nat.two_pow_pos k))
      (pow2_le_of_le hk)
  apply nat_eq_of_nthBit_eq 64 _ _ (Spec.bv64And x _).isLt hModLt
  intro i hi
  rw [nthBit_bv64And _ _ hi]
  have hMaskNat : (BitVec.ofNat 64 (2 ^ k - 1)).toNat = 2 ^ k - 1 :=
    Nat.mod_eq_of_lt hMaskLt
  rw [hMaskNat, nthBit_pow2_sub_one, nthBit_mod_twoPow]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    have hb : Nat.blt i k = true := nat_blt_true hlt
    rw [decide_eq_true hlt, ite_bool_true hb, Bool.and_true]
  | inr hge =>
    have hb : Nat.blt i k = false := nat_blt_false hge
    rw [decide_eq_false (Nat.not_lt_of_ge hge), ite_bool_false hb,
      bool_and_false_right]

private theorem nthBit_div_mul_pow2 (n k i : Nat) :
    Spec.nthBit ((n / 2 ^ k) * 2 ^ k) i =
      if Nat.blt i k then false else Spec.nthBit n i := by
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    have hb : Nat.blt i k = true := nat_blt_true hlt
    rw [ite_bool_true hb]
    have h1 : 1 ≤ k - i := Nat.sub_pos_of_lt hlt
    have hPow : 2 ^ k = (2 * 2 ^ (k - i - 1)) * 2 ^ i := by
      rw [← two_pow_succ, ← two_pow_add, Nat.sub_add_cancel h1,
        Nat.add_comm (k - i) i, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
    unfold Spec.nthBit
    rw [hPow, ← Nat.mul_assoc, Nat.mul_div_left _ (Nat.two_pow_pos i),
      ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.mul_assoc, Nat.mul_mod_right]
    rfl
  | inr hge =>
    have hb : Nat.blt i k = false := nat_blt_false hge
    rw [ite_bool_false hb]
    have hd : i = k + (i - k) := (Nat.add_sub_of_le hge).symm
    unfold Spec.nthBit
    rw [hd, two_pow_add, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_left _ (Nat.two_pow_pos k), Nat.div_div_eq_div_mul]

private theorem mul_pow2_lt_64 {n k : Nat} (hn : n < 2 ^ 64) :
    (n / 2 ^ k) * 2 ^ k < 2 ^ 64 := by
  rw [Nat.mul_comm]
  exact Nat.lt_of_le_of_lt (Nat.mul_div_le n (2 ^ k)) hn

private theorem disjoint_add_lt_of_pow2 {hi lo k w : Nat}
    (hk : k ≤ w) (hHiLt : hi < 2 ^ w) (hMod : hi % 2 ^ k = 0)
    (hLo : lo < 2 ^ k) :
    hi + lo < 2 ^ w := by
  have hPowW : 2 ^ w = 2 ^ (w - k) * 2 ^ k := by
    rw [← two_pow_add, Nat.sub_add_cancel hk]
  have hQ : hi = (hi / 2 ^ k) * 2 ^ k := by
    have hD := Nat.div_add_mod hi (2 ^ k)
    rw [hMod, Nat.add_zero, Nat.mul_comm] at hD
    exact hD.symm
  have hQLt : hi / 2 ^ k < 2 ^ (w - k) := by
    rw [hPowW] at hHiLt
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr hHiLt
  have hQ1 : hi / 2 ^ k + 1 ≤ 2 ^ (w - k) := hQLt
  calc hi + lo
      < (hi / 2 ^ k) * 2 ^ k + 2 ^ k := by
          rw [← hQ]; exact Nat.add_lt_add_left hLo hi
    _ = (hi / 2 ^ k + 1) * 2 ^ k := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 2 ^ (w - k) * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) hQ1
    _ = 2 ^ w := hPowW.symm

private theorem nthBit_disjoint_add {hi lo k i : Nat}
    (hMod : hi % 2 ^ k = 0) (hLo : lo < 2 ^ k) :
    Spec.nthBit (hi + lo) i = (Spec.nthBit hi i || Spec.nthBit lo i) ∧
    Spec.nthBit lo i = bne (Spec.nthBit (hi + lo) i) (Spec.nthBit hi i) := by
  have hHi : hi = (hi / 2 ^ k) * 2 ^ k := by
    have hD := Nat.div_add_mod hi (2 ^ k)
    rw [hMod, Nat.add_zero, Nat.mul_comm] at hD
    exact hD.symm
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    have hb : Nat.blt i k = true := nat_blt_true hlt
    have hHiFalse : Spec.nthBit hi i = false := by
      rw [hHi, nthBit_div_mul_pow2, ite_bool_true hb]
    have hDPos : 0 < k - i := Nat.sub_pos_of_lt hlt
    have hEven : 2 ∣ 2 ^ (k - i) := by
      have hD1 : k - i = (k - i - 1) + 1 := (Nat.sub_add_cancel hDPos).symm
      rw [hD1, two_pow_succ]
      exact nat_dvd_mul_right 2 _
    have hDivSum : (hi + lo) / 2 ^ i =
        (hi / 2 ^ k) * 2 ^ (k - i) + lo / 2 ^ i := by
      have hMulK : (hi / 2 ^ k) * 2 ^ k =
          ((hi / 2 ^ k) * 2 ^ (k - i)) * 2 ^ i := by
        rw [Nat.mul_assoc, ← two_pow_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      calc (hi + lo) / 2 ^ i
          = (lo + hi) / 2 ^ i := by rw [Nat.add_comm]
        _ = (lo + ((hi / 2 ^ k) * 2 ^ (k - i)) * 2 ^ i) / 2 ^ i := by
              rw [congrArg (fun z => lo + z) (hHi.trans hMulK)]
        _ = lo / 2 ^ i + (hi / 2 ^ k) * 2 ^ (k - i) :=
              Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)
        _ = (hi / 2 ^ k) * 2 ^ (k - i) + lo / 2 ^ i := Nat.add_comm _ _
    have hSumBit : Spec.nthBit (hi + lo) i = Spec.nthBit lo i := by
      unfold Spec.nthBit
      rw [hDivSum, mod_twoPow_of_add_mul (nat_dvd_mul_left_of_dvd hEven _)]
    rw [hSumBit, hHiFalse, Bool.false_or]
    exact ⟨rfl, (bool_bne_false _).symm⟩
  | inr hge =>
    have hLoFalse : Spec.nthBit lo i = false :=
      nthBit_eq_false_of_lt (Nat.lt_of_lt_of_le hLo (pow2_le_of_le hge))
    have hd : i = k + (i - k) := (Nat.add_sub_of_le hge).symm
    have hDivHiLo : (hi + lo) / 2 ^ k = hi / 2 ^ k := by
      rw [hHi, Nat.add_comm _ lo,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
        Nat.div_eq_of_lt hLo, Nat.zero_add,
        Nat.mul_div_left _ (Nat.two_pow_pos k)]
    have hDivI : (hi + lo) / 2 ^ i = hi / 2 ^ i := by
      rw [hd, two_pow_add, ← Nat.div_div_eq_div_mul, hDivHiLo,
        Nat.div_div_eq_div_mul]
    have hSumBit : Spec.nthBit (hi + lo) i = Spec.nthBit hi i := by
      unfold Spec.nthBit
      rw [hDivI]
    rw [hSumBit, hLoFalse, Bool.or_false, bne_self_eq_false]
    exact ⟨rfl, rfl⟩

private theorem bv64Or_disjoint_add {hi lo : BitVec 64} {k : Nat}
    (hk : k ≤ 64) (hMod : hi.toNat % 2 ^ k = 0) (hLo : lo.toNat < 2 ^ k) :
    Spec.bv64Or hi lo = hi + lo ∧
    (Spec.bv64Or hi lo).toNat = hi.toNat + lo.toNat ∧
    Spec.bv64Xor (Spec.bv64Or hi lo) hi = lo := by
  have hSumLt := disjoint_add_lt_of_pow2 hk hi.isLt hMod hLo
  have hOrNat : Spec.bv64Or hi lo = hi + lo := by
    apply bv64_eq_of_nthBit_eq
    intro i hi64
    have hAddNat : (hi + lo).toNat = hi.toNat + lo.toNat :=
      Nat.mod_eq_of_lt hSumLt
    rw [nthBit_bv64Or _ _ hi64, hAddNat]
    exact (nthBit_disjoint_add hMod hLo).1.symm
  have hToNat : (Spec.bv64Or hi lo).toNat = hi.toNat + lo.toNat := by
    rw [hOrNat]
    exact Nat.mod_eq_of_lt hSumLt
  have hXor : Spec.bv64Xor (Spec.bv64Or hi lo) hi = lo := by
    apply bv64_eq_of_nthBit_eq
    intro i hi64
    rw [nthBit_bv64Xor _ _ hi64, hToNat]
    exact (nthBit_disjoint_add hMod hLo).2.symm
  exact ⟨hOrNat, hToNat, hXor⟩

/-! ### Cluster 1 Proofs: Power-of-Two & `RoundingAlignAndPhase` -/

private theorem bv64Shl_one_toNat {k : Nat} (hk : k < 64) :
    (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat = 2 ^ k := by
  unfold Spec.bv64Shl
  rw [bv64_toNat_ofNat, show (BitVec.ofNat 64 1).toNat = 1 from rfl,
    show Nat.shiftLeft 1 k = 1 * 2 ^ k from Nat.shiftLeft_eq 1 k, Nat.one_mul]
  exact Nat.mod_eq_of_lt (pow2_lt_64 hk)

private theorem leadingZerosAux_le :
    ∀ (n w : Nat), Spec.leadingZerosAux n w ≤ w
  | _, 0 => Nat.le_refl 0
  | n, w + 1 => by
    change (if Spec.nthBit n w then 0 else 1 + Spec.leadingZerosAux n w) ≤
      w + 1
    cases Spec.nthBit n w with
    | true => exact Nat.zero_le (w + 1)
    | false =>
      change 1 + Spec.leadingZerosAux n w ≤ w + 1
      rw [Nat.add_comm 1]
      exact Nat.succ_le_succ (leadingZerosAux_le n w)

private theorem leadingZerosAux_spec :
    ∀ (w n : Nat), 0 < n → n < 2 ^ w →
      let lz := Spec.leadingZerosAux n w
      let k := (w - 1) - lz
      lz < w ∧
      k < w ∧
      Spec.nthBit n k = true ∧
      (∀ i, k < i → i < w → Spec.nthBit n i = false) := by
  intro w
  induction w with
  | zero =>
    intro n hn hLt
    have h0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hLt)
    rw [h0] at hn
    cases hn
  | succ w ih =>
    intro n hn hLt
    dsimp only
    cases hb : Spec.nthBit n w with
    | true =>
      have hlz : Spec.leadingZerosAux n (w + 1) = 0 := by
        change (if Spec.nthBit n w then 0 else 1 + Spec.leadingZerosAux n w) =
          0
        rw [hb]
        rfl
      have hkEq : (w + 1 - 1) - Spec.leadingZerosAux n (w + 1) = w := by
        rw [hlz]; rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hlz]; exact Nat.zero_lt_succ w
      · rw [hkEq]; exact Nat.lt_succ_self w
      · rw [hkEq]; exact hb
      · intro i hiK hiW
        rw [hkEq] at hiK
        have hGe : w + 1 ≤ i := hiK
        exact False.elim (Nat.not_lt_of_ge hGe hiW)
    | false =>
      have hDivLt2 : n / 2 ^ w < 2 := by
        rw [two_pow_succ] at hLt
        exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w)).mpr hLt
      have hDiv0 : n / 2 ^ w = 0 := by
        unfold Spec.nthBit at hb
        cases hd : n / 2 ^ w with
        | zero => rfl
        | succ k =>
          cases k with
          | zero => rw [hd] at hb; cases hb
          | succ m =>
            rw [hd] at hDivLt2
            cases Nat.not_lt_of_le (Nat.le_add_left 2 m) hDivLt2
      have hLtW : n < 2 ^ w := by
        rw [← Nat.div_add_mod n (2 ^ w), hDiv0, Nat.mul_zero, Nat.zero_add]
        exact Nat.mod_lt n (Nat.two_pow_pos w)
      let sub := ih n hn hLtW
      have hlz : Spec.leadingZerosAux n (w + 1) =
          1 + Spec.leadingZerosAux n w := by
        change (if Spec.nthBit n w then 0 else 1 + Spec.leadingZerosAux n w) =
          1 + Spec.leadingZerosAux n w
        rw [hb]
        rfl
      have hlzLt : Spec.leadingZerosAux n (w + 1) < w + 1 := by
        rw [hlz, Nat.add_comm 1]
        exact Nat.succ_lt_succ sub.1
      have hkEq : (w + 1 - 1) - Spec.leadingZerosAux n (w + 1) =
          (w - 1) - Spec.leadingZerosAux n w := by
        rw [hlz]
        change w - (1 + Spec.leadingZerosAux n w) =
          (w - 1) - Spec.leadingZerosAux n w
        exact (Nat.sub_sub w 1 _).symm
      refine ⟨hlzLt, ?_, ?_, ?_⟩
      · rw [hkEq]
        exact Nat.lt_trans sub.2.1 (Nat.lt_succ_self w)
      · rw [hkEq]
        exact sub.2.2.1
      · intro i hiK hiW
        rw [hkEq] at hiK
        cases Nat.lt_or_ge i w with
        | inl hiSmall => exact sub.2.2.2 i hiK hiSmall
        | inr hiGe =>
          have hiEq : i = w := Nat.le_antisymm (Nat.le_of_lt_succ hiW) hiGe
          subst hiEq
          exact hb

private theorem lt_twoPow_of_high_bits_false :
    ∀ (w k n : Nat), n < 2 ^ w → k ≤ w →
      (∀ i, k ≤ i → i < w → Spec.nthBit n i = false) →
      n < 2 ^ k := by
  intro w
  induction w with
  | zero =>
    intro k n hn hk _
    have hk0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    exact hn
  | succ w ih =>
    intro k n hn hk hBits
    cases Nat.eq_or_lt_of_le hk with
    | inl hEq =>
      subst hEq
      exact hn
    | inr hLt =>
      have hkW : k ≤ w := Nat.le_of_lt_succ hLt
      have hTopFalse := hBits w hkW (Nat.lt_succ_self w)
      have hDivLt2 : n / 2 ^ w < 2 := by
        rw [two_pow_succ] at hn
        exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos w)).mpr hn
      have hDiv0 : n / 2 ^ w = 0 := by
        unfold Spec.nthBit at hTopFalse
        cases hd : n / 2 ^ w with
        | zero => rfl
        | succ m =>
          cases m with
          | zero => rw [hd] at hTopFalse; cases hTopFalse
          | succ m' =>
            rw [hd] at hDivLt2
            cases Nat.not_lt_of_le (Nat.le_add_left 2 m') hDivLt2
      have hLtW : n < 2 ^ w := by
        rw [← Nat.div_add_mod n (2 ^ w), hDiv0, Nat.mul_zero, Nat.zero_add]
        exact Nat.mod_lt n (Nat.two_pow_pos w)
      exact ih k n hLtW hkW (fun i hik hiw =>
        hBits i hik (Nat.lt_trans hiw (Nat.lt_succ_self w)))

private theorem leadingZerosAux_of_pow2_bounds
    (w k n : Nat) (hk : k < w) (hLo : 2 ^ k ≤ n) (hHi : n < 2 ^ (k + 1)) :
    (w - 1) - Spec.leadingZerosAux n w = k := by
  have hPos : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos k) hLo
  have hNW : n < 2 ^ w := Nat.lt_of_lt_of_le hHi (pow2_le_of_le hk)
  let s := leadingZerosAux_spec w n hPos hNW
  let j := (w - 1) - Spec.leadingZerosAux n w
  have hjLt : j < w := s.2.1
  have hjBit : Spec.nthBit n j = true := s.2.2.1
  have hNotGt : ¬ (k < j) := by
    intro hGt
    have hjFalse : Spec.nthBit n j = false :=
      nthBit_eq_false_of_lt (Nat.lt_of_lt_of_le hHi (pow2_le_of_le hGt))
    rw [hjBit] at hjFalse
    cases hjFalse
  have hNotLt : ¬ (j < k) := by
    intro hLt
    have hnBound := lt_twoPow_of_high_bits_false w (j + 1) n hNW
      (Nat.le_trans hLt (Nat.le_of_lt hk)) (fun i hij hiw => s.2.2.2 i hij hiw)
    have hKGe : 2 ^ (j + 1) ≤ 2 ^ k := pow2_le_of_le hLt
    exact Nat.not_lt_of_ge (Nat.le_trans hKGe hLo) hnBound
  cases Nat.lt_or_ge j k with
  | inl h => exact False.elim (hNotLt h)
  | inr h =>
    cases Nat.eq_or_lt_of_le h with
    | inl he => exact he.symm
    | inr hgt => exact False.elim (hNotGt hgt)

private theorem highestSetBit64_bounds (encoded : BitVec 64)
    (hPos : 0 < encoded.toNat) :
    let k := Spec.highestSetBit64 encoded
    k < 64 ∧ 2 ^ k ≤ encoded.toNat ∧ encoded.toNat < 2 ^ (k + 1) ∧
    (encoded.toNat - 2 ^ k) < 2 ^ k ∧
    Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k) =
      BitVec.ofNat 64 (encoded.toNat - 2 ^ k) := by
  let s := leadingZerosAux_spec 64 encoded.toNat hPos encoded.isLt
  let k := Spec.highestSetBit64 encoded
  have hkLt : k < 64 := s.2.1
  have hkBit : Spec.nthBit encoded.toNat k = true := s.2.2.1
  have hLtSucc : encoded.toNat < 2 ^ (k + 1) :=
    lt_twoPow_of_high_bits_false 64 (k + 1) encoded.toNat encoded.isLt hkLt
      (fun i hik hi64 => s.2.2.2 i hik hi64)
  have hDivLt2 : encoded.toNat / 2 ^ k < 2 := by
    rw [two_pow_succ] at hLtSucc
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr hLtSucc
  have hDiv1 : encoded.toNat / 2 ^ k = 1 := by
    unfold Spec.nthBit at hkBit
    cases hd : encoded.toNat / 2 ^ k with
    | zero => rw [hd] at hkBit; cases hkBit
    | succ m =>
      cases m with
      | zero => rfl
      | succ m' =>
        rw [hd] at hDivLt2
        cases Nat.not_lt_of_le (Nat.le_add_left 2 m') hDivLt2
  have hSplit : encoded.toNat = 2 ^ k + encoded.toNat % 2 ^ k := by
    have hD := Nat.div_add_mod encoded.toNat (2 ^ k)
    rw [hDiv1, Nat.mul_one] at hD
    exact hD.symm
  have hGe : 2 ^ k ≤ encoded.toNat := by
    rw [hSplit]
    exact Nat.le_add_right _ _
  have hSubEq : encoded.toNat - 2 ^ k = encoded.toNat % 2 ^ k := by
    calc encoded.toNat - 2 ^ k
        = (2 ^ k + encoded.toNat % 2 ^ k) - 2 ^ k :=
            congrArg (fun z => z - 2 ^ k) hSplit
      _ = encoded.toNat % 2 ^ k := Nat.add_sub_cancel_left _ _
  have hRemLt : encoded.toNat - 2 ^ k < 2 ^ k := by
    rw [hSubEq]
    exact Nat.mod_lt _ (Nat.two_pow_pos k)
  have hMod0 : ((BitVec.ofNat 64 (2 ^ k)).toNat) % 2 ^ k = 0 := by
    rw [bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt), Nat.mod_self]
  have hShlEq : Spec.bv64Shl (BitVec.ofNat 64 1) k = BitVec.ofNat 64 (2 ^ k) :=
    bv64_eq_of_toNat_eq (by
      rw [bv64Shl_one_toNat hkLt, bv64_toNat_ofNat,
        Nat.mod_eq_of_lt (pow2_lt_64 hkLt)])
  have hRemBitLt : encoded.toNat - 2 ^ k < 2 ^ 64 :=
    Nat.lt_trans hRemLt (pow2_lt_64 hkLt)
  have hEncodedRebuilt : encoded =
      Spec.bv64Or (BitVec.ofNat 64 (2 ^ k))
        (BitVec.ofNat 64 (encoded.toNat - 2 ^ k)) := by
    let p := bv64Or_disjoint_add (Nat.le_of_lt hkLt) hMod0
      (by rw [bv64_toNat_ofNat, Nat.mod_eq_of_lt hRemBitLt]; exact hRemLt)
    apply bv64_eq_of_toNat_eq
    rw [p.2.1, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt),
      bv64_toNat_ofNat, Nat.mod_eq_of_lt hRemBitLt, Nat.add_comm,
      Nat.sub_add_cancel hGe]
  have hXor : Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k) =
      BitVec.ofNat 64 (encoded.toNat - 2 ^ k) := by
    let p := bv64Or_disjoint_add (Nat.le_of_lt hkLt) hMod0
      (by rw [bv64_toNat_ofNat, Nat.mod_eq_of_lt hRemBitLt]; exact hRemLt)
    rw [hShlEq]
    have hXorEq := congrArg (fun z => Spec.bv64Xor z (BitVec.ofNat 64 (2 ^ k)))
      hEncodedRebuilt
    exact hXorEq.trans p.2.2
  exact ⟨hkLt, hGe, hLtSucc, hRemLt, hXor⟩

private theorem isPowerOfTwo64_of_pow2 {k : Nat} (hk : k < 64) :
    Spec.isPowerOfTwo64 (BitVec.ofNat 64 (2 ^ k)) := by
  have hPowPos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hNat : (BitVec.ofNat 64 (2 ^ k)).toNat = 2 ^ k :=
    Nat.mod_eq_of_lt (pow2_lt_64 hk)
  refine ⟨by rw [hNat]; exact hPowPos, ?_⟩
  have hSub :
      (BitVec.ofNat 64 (2 ^ k) - BitVec.ofNat 64 1).toNat = 2 ^ k - 1 := by
    rw [bv64_toNat_sub_of_le (by
      show 1 ≤ (BitVec.ofNat 64 (2 ^ k)).toNat
      rw [hNat]
      exact hPowPos), hNat]
    rfl
  apply bv64_eq_of_nthBit_eq
  intro i hi
  rw [nthBit_bv64And _ _ hi, hNat, hSub, nthBit_pow2, nthBit_pow2_sub_one,
    show (BitVec.ofNat 64 0).toNat = 0 from rfl, nthBit_zero]
  cases Nat.lt_or_ge i k with
  | inl hlt =>
    have hNe : Nat.beq i k = false := by
      cases he : Nat.beq i k with
      | false => rfl
      | true =>
        have hEq := Nat.eq_of_beq_eq_true he
        subst hEq
        exact False.elim (Nat.lt_irrefl _ hlt)
    rw [hNe, Bool.false_and]
  | inr hge =>
    rw [decide_eq_false (Nat.not_lt_of_ge hge), Bool.and_false]

private theorem isPowerOfTwo64_iff (align : BitVec 64) :
    Spec.isPowerOfTwo64 align ↔
      ∃ k : Nat, k < 64 ∧ align = BitVec.ofNat 64 (2 ^ k) := by
  constructor
  · intro ⟨hPos, hAndZero⟩
    let hb := highestSetBit64_bounds align hPos
    let k := Spec.highestSetBit64 align
    have hkLt : k < 64 := hb.1
    have hRemLt : align.toNat - 2 ^ k < 2 ^ k := hb.2.2.2.1
    have hPhaseZero : align.toNat - 2 ^ k = 0 := by
      cases hRem : align.toNat - 2 ^ k with
      | zero => rfl
      | succ m =>
        have hGe1 : (BitVec.ofNat 64 1).toNat ≤ align.toNat :=
          Nat.le_trans (Nat.two_pow_pos k) hb.2.1
        have hSub1 : (align - BitVec.ofNat 64 1).toNat = align.toNat - 1 := by
          rw [bv64_toNat_sub_of_le hGe1]
          rfl
        have hSplitSub : align.toNat - 1 = 2 ^ k + m := by
          have hSplitA : align.toNat = 2 ^ k + (m + 1) := by
            rw [← hRem, Nat.add_sub_of_le hb.2.1]
          rw [hSplitA, ← Nat.add_assoc]
          exact Nat.add_sub_cancel _ 1
        have hmLt : m < 2 ^ k := by
          have h1 : m + 1 < 2 ^ k := by rw [← hRem]; exact hRemLt
          exact Nat.lt_trans (Nat.lt_succ_self m) h1
        have hLoBit :
            Spec.nthBit (align - BitVec.ofNat 64 1).toNat k = true := by
          rw [hSub1, hSplitSub,
            (nthBit_disjoint_add (Nat.mod_self (2 ^ k)) hmLt).1,
            nthBit_pow2, Anneal.InitLemmas.nat_beq_refl, Bool.true_or]
        have hHiBit : Spec.nthBit align.toNat k = true :=
          (leadingZerosAux_spec 64 align.toNat hPos align.isLt).2.2.1
        have hZeroBit := congrArg (fun x => Spec.nthBit x.toNat k) hAndZero
        rw [nthBit_bv64And _ _ hkLt, hHiBit, hLoBit,
          show (BitVec.ofNat 64 0).toNat = 0 from rfl, nthBit_zero]
          at hZeroBit
        cases hZeroBit
    refine ⟨k, hkLt, bv64_eq_of_toNat_eq ?_⟩
    have hEq := Nat.add_sub_of_le hb.2.1
    rw [hPhaseZero, Nat.add_zero] at hEq
    rw [bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
    exact hEq.symm
  · intro ⟨k, hk, hEq⟩
    subst hEq
    exact isPowerOfTwo64_of_pow2 hk

private theorem rounding_new_roundtrip (k : Nat) (phase : BitVec 64)
    (hk : k < 64)
    (hPh : phase.toNat < (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat) :
    let align := Spec.bv64Shl (BitVec.ofNat 64 1) k
    let encoded := Spec.roundingNew64 align phase
    Spec.isPowerOfTwo64 align ∧
    align.toNat = 2 ^ k ∧
    encoded = align + phase ∧
    encoded.toNat = align.toNat + phase.toNat ∧
    0 < encoded.toNat ∧
    Spec.highestSetBit64 encoded = k ∧
    Spec.bv64Shl (BitVec.ofNat 64 1) (Spec.highestSetBit64 encoded) = align ∧
    Spec.bv64Xor encoded align = phase ∧
    Spec.roundingComponents64 encoded = (align, phase) ∧
    Spec.roundingAlign64 encoded = align := by
  have hAlignNat : (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat = 2 ^ k :=
    bv64Shl_one_toNat hk
  have hAlignPow :
      Spec.isPowerOfTwo64 (Spec.bv64Shl (BitVec.ofNat 64 1) k) := by
    have hEq : Spec.bv64Shl (BitVec.ofNat 64 1) k = BitVec.ofNat 64 (2 ^ k) :=
      bv64_eq_of_toNat_eq (by
        rw [hAlignNat, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hk)])
    rw [hEq]
    exact isPowerOfTwo64_of_pow2 hk
  have hMod0 : (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat % 2 ^ k = 0 := by
    rw [hAlignNat, Nat.mod_self]
  have hPhLt : phase.toNat < 2 ^ k := by rw [← hAlignNat]; exact hPh
  let d := bv64Or_disjoint_add (Nat.le_of_lt hk) hMod0 hPhLt
  have hEncPos : 0 < (Spec.roundingNew64
      (Spec.bv64Shl (BitVec.ofNat 64 1) k) phase).toNat := by
    unfold Spec.roundingNew64
    rw [d.2.1, hAlignNat]
    exact Nat.lt_of_lt_of_le (Nat.two_pow_pos k) (Nat.le_add_right _ _)
  have hEncBounds :
      2 ^ k ≤ (Spec.roundingNew64
        (Spec.bv64Shl (BitVec.ofNat 64 1) k) phase).toNat ∧
      (Spec.roundingNew64
        (Spec.bv64Shl (BitVec.ofNat 64 1) k) phase).toNat < 2 ^ (k + 1) := by
    unfold Spec.roundingNew64
    rw [d.2.1, hAlignNat, two_pow_succ, show 2 * 2 ^ k = 2 ^ k + 2 ^ k from
      (Nat.two_mul _)]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hPhLt _⟩
  have hHs : Spec.highestSetBit64
      (Spec.roundingNew64 (Spec.bv64Shl (BitVec.ofNat 64 1) k) phase) = k :=
    leadingZerosAux_of_pow2_bounds 64 k _ hk hEncBounds.1 hEncBounds.2
  have hComp : Spec.roundingComponents64
      (Spec.roundingNew64 (Spec.bv64Shl (BitVec.ofNat 64 1) k) phase) =
      (Spec.bv64Shl (BitVec.ofNat 64 1) k, phase) := by
    unfold Spec.roundingComponents64
    dsimp only
    rw [hHs, show Spec.bv64Xor
        (Spec.roundingNew64 (Spec.bv64Shl (BitVec.ofNat 64 1) k) phase)
        (Spec.bv64Shl (BitVec.ofNat 64 1) k) = phase from d.2.2]
  exact ⟨hAlignPow, hAlignNat, d.1, d.2.1, hEncPos, hHs,
    congrArg (Spec.bv64Shl (BitVec.ofNat 64 1)) hHs, d.2.2, hComp,
    congrArg Prod.fst hComp⟩

private theorem rounding_components_kani (encoded : BitVec 64)
    (hPos : 0 < encoded.toNat) :
    let (align, phase) := Spec.roundingComponents64 encoded
    Spec.isPowerOfTwo64 align ∧
    phase.toNat < align.toNat ∧
    Spec.checkedAdd64 align phase = some encoded ∧
    Spec.bv64Or align phase = encoded ∧
    align.toNat ≤ encoded.toNat ∧
    encoded.toNat - align.toNat < align.toNat := by
  let hb := highestSetBit64_bounds encoded hPos
  let k := Spec.highestSetBit64 encoded
  have hkLt : k < 64 := hb.1
  have hShlEq :
      Spec.bv64Shl (BitVec.ofNat 64 1) k = BitVec.ofNat 64 (2 ^ k) :=
    bv64_eq_of_toNat_eq (by
      rw [bv64Shl_one_toNat hkLt, bv64_toNat_ofNat,
        Nat.mod_eq_of_lt (pow2_lt_64 hkLt)])
  have hAlignPow :
      Spec.isPowerOfTwo64 (Spec.bv64Shl (BitVec.ofNat 64 1) k) := by
    rw [hShlEq]; exact isPowerOfTwo64_of_pow2 hkLt
  have hAlignNat : (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat = 2 ^ k :=
    bv64Shl_one_toNat hkLt
  have hRemLt64 : encoded.toNat - 2 ^ k < 2 ^ 64 :=
    Nat.lt_trans hb.2.2.2.1 (pow2_lt_64 hkLt)
  have hPhNat :
      (Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k)).toNat =
        encoded.toNat - 2 ^ k := by
    rw [hb.2.2.2.2, bv64_toNat_ofNat, Nat.mod_eq_of_lt hRemLt64]
  have hPhLt :
      (Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k)).toNat <
        (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat := by
    rw [hPhNat, hAlignNat]
    exact hb.2.2.2.1
  have hSumNat : (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat +
      (Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k)).toNat =
      encoded.toNat := by
    rw [hAlignNat, hPhNat, Nat.add_comm, Nat.sub_add_cancel hb.2.1]
  have hSumLe : (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat +
      (Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k)).toNat ≤
      Spec.usizeMaxNat := by
    rw [hSumNat]
    exact Nat.le_pred_of_lt encoded.isLt
  have hAddEq : Spec.bv64Shl (BitVec.ofNat 64 1) k +
      Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k) = encoded :=
    bv64_eq_of_toNat_eq (by
      rw [bv64_toNat_add, hSumNat]
      exact Nat.mod_eq_of_lt encoded.isLt)
  have hChecked : Spec.checkedAdd64 (Spec.bv64Shl (BitVec.ofNat 64 1) k)
      (Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k)) =
      some encoded := by
    unfold Spec.checkedAdd64
    rw [nat_ble_true _ _ hSumLe, hAddEq]
    rfl
  have hMod0 : (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat % 2 ^ k = 0 := by
    rw [hAlignNat, Nat.mod_self]
  let d := bv64Or_disjoint_add (Nat.le_of_lt hkLt) hMod0
    (by rw [← hAlignNat]; exact hPhLt)
  have hOrEq : Spec.bv64Or (Spec.bv64Shl (BitVec.ofNat 64 1) k)
      (Spec.bv64Xor encoded (Spec.bv64Shl (BitVec.ofNat 64 1) k)) =
      encoded := by
    rw [d.1, hAddEq]
  have hLeEnc : (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat ≤ encoded.toNat := by
    rw [hAlignNat]; exact hb.2.1
  have hSubLtAlign :
      encoded.toNat - (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat <
        (Spec.bv64Shl (BitVec.ofNat 64 1) k).toNat := by
    rw [hAlignNat]; exact hb.2.2.2.1
  exact ⟨hAlignPow, hPhLt, hChecked, hOrEq, hLeEnc, hSubLtAlign⟩

private theorem roundDown64_spec (n align : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) :
    (Spec.roundDown64 n align).toNat = (n.toNat / align.toNat) * align.toNat ∧
    (Spec.roundDown64 n align).toNat ≤ n.toNat ∧
    (Spec.roundDown64 n align).toNat % align.toNat = 0 ∧
    n.toNat < (Spec.roundDown64 n align).toNat + align.toNat := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hEq : (Spec.roundDown64 n align).toNat =
      (n.toNat / 2 ^ k) * 2 ^ k := by
    unfold Spec.roundDown64
    have hMulLt : (n.toNat / 2 ^ k) * 2 ^ k < 2 ^ 64 :=
      mul_pow2_lt_64 n.isLt
    apply nat_eq_of_nthBit_eq 64 _ _ (BitVec.isLt _) hMulLt
    intro i hi
    have hSub1 : (align - BitVec.ofNat 64 1).toNat = 2 ^ k - 1 := by
      rw [bv64_toNat_sub_of_le (by
        show 1 ≤ align.toNat
        rw [hAlNat]
        exact Nat.two_pow_pos k), hAlNat]
      rfl
    rw [nthBit_bv64And _ _ hi, nthBit_bv64Not _ hi, hSub1,
      nthBit_pow2_sub_one, nthBit_div_mul_pow2]
    cases Nat.lt_or_ge i k with
    | inl hlt =>
      have hb : Nat.blt i k = true := nat_blt_true hlt
      rw [decide_eq_true hlt, ite_bool_true hb, Bool.not_true,
        bool_and_false_right]
    | inr hge =>
      have hb : Nat.blt i k = false := nat_blt_false hge
      rw [decide_eq_false (Nat.not_lt_of_ge hge), ite_bool_false hb,
        Bool.not_false, Bool.and_true]
  rw [hEq, hAlNat]
  refine ⟨rfl, ?_, Nat.mul_mod_left _ _, ?_⟩
  · rw [Nat.mul_comm]; exact Nat.mul_div_le n.toNat (2 ^ k)
  · have hRem := Nat.mod_lt n.toNat (Nat.two_pow_pos k)
    have hSplit : n.toNat = (n.toNat / 2 ^ k) * 2 ^ k + n.toNat % 2 ^ k := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod n.toNat (2 ^ k)).symm
    have hSum := Nat.add_lt_add_left hRem ((n.toNat / 2 ^ k) * 2 ^ k)
    rw [← hSplit] at hSum
    exact hSum

private theorem sizeOffset64_spec (sizeBase align phase : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) (hPh : phase.toNat < align.toNat) :
    Spec.sizeOffset64 sizeBase align phase =
      Spec.roundDown64 sizeBase align + phase ∧
    (Spec.sizeOffset64 sizeBase align phase).toNat =
      (Spec.roundDown64 sizeBase align).toNat + phase.toNat := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hMod0 : (Spec.roundDown64 sizeBase align).toNat % 2 ^ k = 0 := by
    rw [← hAlNat]
    exact (roundDown64_spec sizeBase align hPow).2.2.1
  have hPhLt : phase.toNat < 2 ^ k := by rw [← hAlNat]; exact hPh
  let d := bv64Or_disjoint_add (Nat.le_of_lt hkLt) hMod0 hPhLt
  exact ⟨d.1, d.2.1⟩

/-! ### Abelian Group Laws for `BitVec 64` Addition/Subtraction -/

private def bv64Neg (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ 64 - x.toNat)

private theorem bv64_sub_eq_add_neg (a b : BitVec 64) :
    a - b = bv64Neg b + a := by
  apply bv64_eq_of_toNat_eq
  rw [bv64_toNat_sub, bv64_toNat_add]
  unfold bv64Neg
  rw [bv64_toNat_ofNat, two_pow_64_val, nat_mod_add_mod]

private theorem bv64_add_comm (a b : BitVec 64) : a + b = b + a := by
  apply bv64_eq_of_toNat_eq
  rw [bv64_toNat_add, bv64_toNat_add, Nat.add_comm]

private theorem bv64_add_assoc (a b c : BitVec 64) :
    (a + b) + c = a + (b + c) := by
  apply bv64_eq_of_toNat_eq
  rw [bv64_toNat_add, bv64_toNat_add, bv64_toNat_add, bv64_toNat_add,
    nat_mod_add_mod, nat_add_mod_mod, Nat.add_assoc]

private theorem bv64_add_zero (a : BitVec 64) :
    a + BitVec.ofNat 64 0 = a := by
  apply bv64_eq_of_toNat_eq
  rw [bv64_toNat_add, bv64_toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.isLt

private theorem bv64_zero_add (a : BitVec 64) :
    BitVec.ofNat 64 0 + a = a := by
  rw [bv64_add_comm]
  exact bv64_add_zero a

private theorem bv64_add_neg_self (a : BitVec 64) :
    a + bv64Neg a = BitVec.ofNat 64 0 := by
  apply bv64_eq_of_toNat_eq
  rw [bv64_toNat_add]
  unfold bv64Neg
  rw [bv64_toNat_ofNat, two_pow_64_val, nat_add_mod_mod,
    Nat.add_sub_of_le (Nat.le_of_lt a.isLt), Nat.mod_self]
  rfl

private theorem bv64_neg_add_self (a : BitVec 64) :
    bv64Neg a + a = BitVec.ofNat 64 0 := by
  rw [bv64_add_comm]
  exact bv64_add_neg_self a

private theorem bv64_eq_neg_of_add_eq_zero {x y : BitVec 64}
    (h : x + y = BitVec.ofNat 64 0) : y = bv64Neg x := by
  calc y = BitVec.ofNat 64 0 + y := (bv64_zero_add y).symm
    _ = (bv64Neg x + x) + y := by rw [bv64_neg_add_self]
    _ = bv64Neg x + (x + y) := bv64_add_assoc _ _ _
    _ = bv64Neg x + BitVec.ofNat 64 0 := by rw [h]
    _ = bv64Neg x := bv64_add_zero _

private theorem bv64_neg_add (a b : BitVec 64) :
    bv64Neg (a + b) = bv64Neg a + bv64Neg b := by
  refine (bv64_eq_neg_of_add_eq_zero ?_).symm
  calc (a + b) + (bv64Neg a + bv64Neg b)
      = a + (b + (bv64Neg a + bv64Neg b)) := bv64_add_assoc _ _ _
    _ = a + ((bv64Neg a + b) + bv64Neg b) := by
        rw [← bv64_add_assoc b (bv64Neg a) (bv64Neg b),
          bv64_add_comm b (bv64Neg a)]
    _ = a + (bv64Neg a + (b + bv64Neg b)) := by rw [bv64_add_assoc]
    _ = (a + bv64Neg a) + (b + bv64Neg b) := (bv64_add_assoc _ _ _).symm
    _ = BitVec.ofNat 64 0 + BitVec.ofNat 64 0 := by
        rw [bv64_add_neg_self, bv64_add_neg_self]
    _ = BitVec.ofNat 64 0 := bv64_add_zero _

private theorem bv64_sub_add_cancel_right (a b c : BitVec 64) :
    (a + c) - (b + c) = a - b := by
  rw [bv64_sub_eq_add_neg, bv64_sub_eq_add_neg, bv64_neg_add]
  calc (bv64Neg b + bv64Neg c) + (a + c)
      = bv64Neg b + (bv64Neg c + (c + a)) := by
          rw [bv64_add_assoc, bv64_add_comm a c]
    _ = bv64Neg b + ((bv64Neg c + c) + a) := by
          rw [← bv64_add_assoc (bv64Neg c) c a]
    _ = bv64Neg b + a := by rw [bv64_neg_add_self, bv64_zero_add]

private theorem bv64_sub_add_cancel_self (a b : BitVec 64) :
    a + (b - a) = b := by
  rw [bv64_sub_eq_add_neg, ← bv64_add_assoc, bv64_add_neg_self, bv64_zero_add]

/-! ### Cluster 2 Proofs: `padding_needed_for`, `round_down`,
`padding_for_elems` -/

private theorem mod_pow2_mod64 (x : Nat) {k : Nat} (hk : k ≤ 64) :
    (x % 2 ^ 64) % 2 ^ k = x % 2 ^ k :=
  nat_mod_mod_of_dvd x (pow2_dvd_64 hk)

private theorem bv64_mod_pow2_add (a b : BitVec 64) {k : Nat}
    (hk : k ≤ 64) :
    (a + b).toNat % 2 ^ k = (a.toNat + b.toNat) % 2 ^ k := by
  rw [bv64_toNat_add, mod_pow2_mod64 _ hk]

private theorem bv64_mod_pow2_mul (a b : BitVec 64) {k : Nat}
    (hk : k ≤ 64) :
    (Spec.bv64Mul a b).toNat % 2 ^ k = (a.toNat * b.toNat) % 2 ^ k := by
  unfold Spec.bv64Mul
  rw [bv64_toNat_ofNat, mod_pow2_mod64 _ hk]

private theorem paddingNeededFor64_spec (len align : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) :
    (Spec.paddingNeededFor64 len align).toNat =
      (if len.toNat % align.toNat = 0 then 0
        else align.toNat - len.toNat % align.toNat) ∧
    (len + Spec.paddingNeededFor64 len align).toNat % align.toNat = 0 ∧
    (Spec.paddingNeededFor64 len align).toNat < align.toNat := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hPk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hAlPos : 0 < align.toNat := by rw [hAlNat]; exact hPk
  have hSubMask : (align - BitVec.ofNat 64 1).toNat = 2 ^ k - 1 := by
    rw [bv64_toNat_sub_of_le (by show 1 ≤ align.toNat; exact hAlPos), hAlNat]
    rfl
  have hMEq : align - BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ k - 1) :=
    bv64_eq_of_toNat_eq (by
      rw [hSubMask, bv64_toNat_ofNat, Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le (Nat.sub_lt hPk Nat.zero_lt_one)
          (pow2_le_of_le (Nat.le_of_lt hkLt)))])
  let u := len - BitVec.ofNat 64 1
  have huLt : u.toNat < 2 ^ 64 := u.isLt
  have hPow64Decomp : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by
    rw [← two_pow_add, Nat.sub_add_cancel (Nat.le_of_lt hkLt)]
  have hP64Pos : 0 < 2 ^ (64 - k) := Nat.two_pow_pos (64 - k)
  have h64Split : 2 ^ 64 - 1 =
      (2 ^ (64 - k) - 1) * 2 ^ k + (2 ^ k - 1) := by
    calc 2 ^ 64 - 1
        = ((2 ^ (64 - k) - 1) + 1) * 2 ^ k - 1 := by
            rw [Nat.sub_add_cancel hP64Pos, hPow64Decomp]
      _ = (2 ^ (64 - k) - 1) * 2 ^ k + 2 ^ k - 1 := by
            rw [Nat.add_mul, Nat.one_mul]
      _ = (2 ^ (64 - k) - 1) * 2 ^ k + (2 ^ k - 1) :=
            Nat.add_sub_assoc hPk _
  have hPadNat :
      (Spec.paddingNeededFor64 len align).toNat =
        (2 ^ k - 1) - u.toNat % 2 ^ k := by
    unfold Spec.paddingNeededFor64
    dsimp only
    rw [hMEq, bv64And_lowMask _ (Nat.le_of_lt hkLt), bv64Not_toNat]
    have hQ1 : u.toNat / 2 ^ k + 1 ≤ 2 ^ (64 - k) := by
      rw [hPow64Decomp] at huLt
      exact (Nat.div_lt_iff_lt_mul hPk).mpr huLt
    have hQLe : u.toNat / 2 ^ k ≤ 2 ^ (64 - k) - 1 := Nat.le_pred_of_lt hQ1
    have hRemLe : u.toNat % 2 ^ k ≤ 2 ^ k - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ hPk)
    have hUSplit : u.toNat = (u.toNat / 2 ^ k) * 2 ^ k + u.toNat % 2 ^ k := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod u.toNat (2 ^ k)).symm
    have hDiffEq : 2 ^ 64 - 1 - u.toNat =
        (2 ^ (64 - k) - 1 - u.toNat / 2 ^ k) * 2 ^ k +
          ((2 ^ k - 1) - u.toNat % 2 ^ k) := by
      apply nat_sub_eq_of_eq_add
      calc 2 ^ 64 - 1
          = (2 ^ (64 - k) - 1) * 2 ^ k + (2 ^ k - 1) := h64Split
        _ = ((2 ^ (64 - k) - 1 - u.toNat / 2 ^ k) + u.toNat / 2 ^ k) * 2 ^ k +
              (((2 ^ k - 1) - u.toNat % 2 ^ k) + u.toNat % 2 ^ k) := by
              rw [Nat.sub_add_cancel hQLe, Nat.sub_add_cancel hRemLe]
        _ = ((2 ^ (64 - k) - 1 - u.toNat / 2 ^ k) * 2 ^ k +
                (u.toNat / 2 ^ k) * 2 ^ k) +
              (((2 ^ k - 1) - u.toNat % 2 ^ k) + u.toNat % 2 ^ k) := by
              rw [Nat.add_mul]
        _ = ((2 ^ (64 - k) - 1 - u.toNat / 2 ^ k) * 2 ^ k +
                ((2 ^ k - 1) - u.toNat % 2 ^ k)) +
              ((u.toNat / 2 ^ k) * 2 ^ k + u.toNat % 2 ^ k) :=
              Anneal.InitLemmas.add_four_rearrange _ _ _ _
        _ = ((2 ^ (64 - k) - 1 - u.toNat / 2 ^ k) * 2 ^ k +
                ((2 ^ k - 1) - u.toNat % 2 ^ k)) + u.toNat := by
              rw [← hUSplit]
    rw [hDiffEq, Nat.mul_comm _ (2 ^ k), Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.sub_lt hPk Nat.zero_lt_one))
  cases hMod : Nat.beq (len.toNat % 2 ^ k) 0 with
  | true =>
    have h0 := Nat.eq_of_beq_eq_true hMod
    have h0Al : len.toNat % align.toNat = 0 := by rw [hAlNat]; exact h0
    have huMod : u.toNat % 2 ^ k = 2 ^ k - 1 := by
      cases hLen : len.toNat with
      | zero =>
        have hLen0 : len = BitVec.ofNat 64 0 := bv64_eq_of_toNat_eq hLen
        have hu64 : u.toNat = 2 ^ 64 - 1 := by
          change (len - BitVec.ofNat 64 1).toNat = 2 ^ 64 - 1
          rw [hLen0]
          rfl
        rw [hu64, h64Split, Nat.mul_comm _ (2 ^ k), Nat.mul_add_mod_self_left]
        exact Nat.mod_eq_of_lt (Nat.sub_lt hPk Nat.zero_lt_one)
      | succ m =>
        have hLenPos : (BitVec.ofNat 64 1).toNat ≤ len.toNat := by
          rw [hLen]; exact Nat.zero_lt_succ m
        have huSub : u.toNat = len.toNat - 1 := by
          change (len - BitVec.ofNat 64 1).toNat = len.toNat - 1
          rw [bv64_toNat_sub_of_le hLenPos]
          rfl
        have hLenMul : len.toNat = (len.toNat / 2 ^ k) * 2 ^ k := by
          have hD := (Nat.div_add_mod len.toNat (2 ^ k)).symm
          rw [h0, Nat.add_zero, Nat.mul_comm] at hD
          exact hD
        have hQPos : 0 < len.toNat / 2 ^ k := by
          cases hq : len.toNat / 2 ^ k with
          | zero =>
            rw [hq, Nat.zero_mul] at hLenMul
            rw [hLenMul] at hLenPos
            cases hLenPos
          | succ q' => exact Nat.zero_lt_succ q'
        have hLenSub : len.toNat - 1 =
            (len.toNat / 2 ^ k - 1) * 2 ^ k + (2 ^ k - 1) := by
          calc len.toNat - 1
              = ((len.toNat / 2 ^ k - 1) + 1) * 2 ^ k - 1 := by
                  rw [Nat.sub_add_cancel hQPos, ← hLenMul]
            _ = (len.toNat / 2 ^ k - 1) * 2 ^ k + 2 ^ k - 1 := by
                  rw [Nat.add_mul, Nat.one_mul]
            _ = (len.toNat / 2 ^ k - 1) * 2 ^ k + (2 ^ k - 1) :=
                  Nat.add_sub_assoc hPk _
        rw [huSub, hLenSub, Nat.mul_comm _ (2 ^ k), Nat.mul_add_mod_self_left]
        exact Nat.mod_eq_of_lt (Nat.sub_lt hPk Nat.zero_lt_one)
    have hP0 : (Spec.paddingNeededFor64 len align).toNat = 0 := by
      rw [hPadNat, huMod, Nat.sub_self]
    refine ⟨by rw [ite_prop_true h0Al, hP0], ?_, by rw [hP0]; exact hAlPos⟩
    rw [hAlNat, bv64_mod_pow2_add _ _ (Nat.le_of_lt hkLt), hP0, Nat.add_zero,
      h0]
  | false =>
    have hNe : len.toNat % 2 ^ k ≠ 0 := fun h => by rw [h] at hMod; cases hMod
    have hNeAl : len.toNat % align.toNat ≠ 0 := by rw [hAlNat]; exact hNe
    have hRemPos : 0 < len.toNat % 2 ^ k := Nat.pos_of_ne_zero hNe
    have hLenPos : (BitVec.ofNat 64 1).toNat ≤ len.toNat := by
      cases hLen : len.toNat with
      | zero =>
        rw [hLen, Nat.zero_mod] at hRemPos
        cases hRemPos
      | succ m => exact Nat.zero_lt_succ m
    have huSub : u.toNat = len.toNat - 1 := by
      change (len - BitVec.ofNat 64 1).toNat = len.toNat - 1
      rw [bv64_toNat_sub_of_le hLenPos]
      rfl
    have hLenSplit : len.toNat =
        (len.toNat / 2 ^ k) * 2 ^ k + len.toNat % 2 ^ k := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod len.toNat (2 ^ k)).symm
    have huSplit : u.toNat =
        (len.toNat / 2 ^ k) * 2 ^ k + (len.toNat % 2 ^ k - 1) := by
      calc u.toNat
          = len.toNat - 1 := huSub
        _ = ((len.toNat / 2 ^ k) * 2 ^ k + len.toNat % 2 ^ k) - 1 :=
              congrArg (fun z => z - 1) hLenSplit
        _ = (len.toNat / 2 ^ k) * 2 ^ k + (len.toNat % 2 ^ k - 1) :=
              Nat.add_sub_assoc hRemPos _
    have huMod : u.toNat % 2 ^ k = len.toNat % 2 ^ k - 1 := by
      rw [huSplit, Nat.mul_comm _ (2 ^ k), Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ 1)
        (Nat.mod_lt _ hPk))
    have hPVal : (Spec.paddingNeededFor64 len align).toNat =
        2 ^ k - len.toNat % 2 ^ k := by
      rw [hPadNat, huMod, Nat.sub_sub, Nat.add_sub_of_le hRemPos]
    have hAddMod0 :
        (len + Spec.paddingNeededFor64 len align).toNat % align.toNat = 0 := by
      rw [hAlNat, bv64_mod_pow2_add _ _ (Nat.le_of_lt hkLt), hPVal]
      have hSumEq : len.toNat + (2 ^ k - len.toNat % 2 ^ k) =
          (len.toNat / 2 ^ k + 1) * 2 ^ k := by
        calc len.toNat + (2 ^ k - len.toNat % 2 ^ k)
            = ((len.toNat / 2 ^ k) * 2 ^ k + len.toNat % 2 ^ k) +
                (2 ^ k - len.toNat % 2 ^ k) :=
                congrArg (fun z => z + (2 ^ k - len.toNat % 2 ^ k)) hLenSplit
          _ = (len.toNat / 2 ^ k) * 2 ^ k +
                (len.toNat % 2 ^ k + (2 ^ k - len.toNat % 2 ^ k)) :=
                Nat.add_assoc _ _ _
          _ = (len.toNat / 2 ^ k) * 2 ^ k + 2 ^ k := by
                rw [Nat.add_sub_of_le (Nat.le_of_lt (Nat.mod_lt _ hPk))]
          _ = (len.toNat / 2 ^ k + 1) * 2 ^ k := by
                rw [Nat.add_mul, Nat.one_mul]
      rw [hSumEq, Nat.mul_mod_left]
    refine ⟨by rw [ite_prop_false hNeAl, hPVal, hAlNat], hAddMod0, ?_⟩
    rw [hAlNat, hPVal]
    exact Nat.sub_lt hPk hRemPos

private theorem bv64_roundUp_eq_add_pad (x align : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) :
    Spec.roundDown64 (x + (align - BitVec.ofNat 64 1)) align =
      x + Spec.paddingNeededFor64 x align := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hPk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hAlPos : (BitVec.ofNat 64 1).toNat ≤ align.toNat := by
    rw [hAlNat]; exact hPk
  have hMaskNat : (align - BitVec.ofNat 64 1).toNat = 2 ^ k - 1 := by
    rw [bv64_toNat_sub_of_le hAlPos, hAlNat]
    rfl
  let p := Spec.paddingNeededFor64 x align
  have pSpec := paddingNeededFor64_spec x align hPow
  have hRd := (roundDown64_spec (x + (align - BitVec.ofNat 64 1)) align hPow).1
  rw [hAlNat, bv64_toNat_add, hMaskNat] at hRd
  have hPow64 : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by
    rw [← two_pow_add, Nat.sub_add_cancel (Nat.le_of_lt hkLt)]
  let q := x.toNat / 2 ^ k
  let r := x.toNat % 2 ^ k
  have hxSplit : x.toNat = q * 2 ^ k + r := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod x.toNat (2 ^ k)).symm
  have hQLt : q < 2 ^ (64 - k) := by
    have hx64 := x.isLt
    rw [hPow64] at hx64
    exact (Nat.div_lt_iff_lt_mul hPk).mpr hx64
  have hQ1Le : q + 1 ≤ 2 ^ (64 - k) := hQLt
  apply bv64_eq_of_toNat_eq
  rw [hRd, bv64_toNat_add]
  cases hr : Nat.beq r 0 with
  | true =>
    have hr0 := Nat.eq_of_beq_eq_true hr
    have hxMod0 : x.toNat % align.toNat = 0 := by rw [hAlNat]; exact hr0
    have hp0 : p.toNat = 0 := by rw [pSpec.1, ite_prop_true hxMod0]
    have hxQ : x.toNat = q * 2 ^ k := by rw [hxSplit, hr0, Nat.add_zero]
    have hSumLt64 : x.toNat + (2 ^ k - 1) < 2 ^ 64 := by
      calc x.toNat + (2 ^ k - 1)
          < q * 2 ^ k + 2 ^ k := by
              rw [hxQ]
              exact Nat.add_lt_add_left (Nat.sub_lt hPk Nat.zero_lt_one) _
        _ = (q + 1) * 2 ^ k := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ 2 ^ (64 - k) * 2 ^ k := Nat.mul_le_mul_right _ hQ1Le
        _ = 2 ^ 64 := hPow64.symm
    have hDivQ : (x.toNat + (2 ^ k - 1)) % 2 ^ 64 / 2 ^ k = q := by
      rw [Nat.mod_eq_of_lt hSumLt64, hxQ, Nat.add_comm (q * 2 ^ k),
        Nat.mul_comm q _, Nat.add_mul_div_left _ _ hPk,
        Nat.div_eq_of_lt (Nat.sub_lt hPk Nat.zero_lt_one), Nat.zero_add]
    rw [hDivQ, hp0, Nat.add_zero, ← hxQ, Nat.mod_eq_of_lt x.isLt]
  | false =>
    have hrNe : r ≠ 0 := fun h => by rw [h] at hr; cases hr
    have hrPos : 0 < r := Nat.pos_of_ne_zero hrNe
    have hrLt : r < 2 ^ k := Nat.mod_lt _ hPk
    have hxNe : x.toNat % align.toNat ≠ 0 := by rw [hAlNat]; exact hrNe
    have hpVal : p.toNat = 2 ^ k - r := by
      rw [pSpec.1, ite_prop_false hxNe, hAlNat]
    have hSumX : x.toNat + p.toNat = (q + 1) * 2 ^ k := by
      calc x.toNat + p.toNat
          = (q * 2 ^ k + r) + (2 ^ k - r) := by rw [hxSplit, hpVal]
        _ = q * 2 ^ k + (r + (2 ^ k - r)) := Nat.add_assoc _ _ _
        _ = q * 2 ^ k + 2 ^ k := by rw [Nat.add_sub_of_le (Nat.le_of_lt hrLt)]
        _ = (q + 1) * 2 ^ k := by rw [Nat.add_mul, Nat.one_mul]
    have hS : x.toNat + (2 ^ k - 1) = (q + 1) * 2 ^ k + (r - 1) := by
      calc x.toNat + (2 ^ k - 1)
          = q * 2 ^ k + r + (2 ^ k - 1) := by rw [hxSplit]
        _ = q * 2 ^ k + (2 ^ k + (r - 1)) := by
              have hRr : r + (2 ^ k - 1) = 2 ^ k + (r - 1) := by
                have hr1 : r = 1 + (r - 1) := (Nat.add_sub_of_le hrPos).symm
                calc r + (2 ^ k - 1)
                    = (1 + (r - 1)) + (2 ^ k - 1) := by
                        exact congrArg (fun z => z + (2 ^ k - 1)) hr1
                  _ = (1 + (2 ^ k - 1)) + (r - 1) := by
                        rw [Nat.add_assoc, Nat.add_comm (r - 1),
                          ← Nat.add_assoc]
                  _ = 2 ^ k + (r - 1) := by
                        rw [Nat.add_comm 1 (2 ^ k - 1), Nat.sub_add_cancel hPk]
              rw [Nat.add_assoc, hRr]
        _ = (q + 1) * 2 ^ k + (r - 1) := by
              have hMulQ : (q + 1) * 2 ^ k = q * 2 ^ k + 2 ^ k := by
                rw [Nat.add_mul, Nat.one_mul]
              rw [← Nat.add_assoc, hMulQ]
    cases Nat.eq_or_lt_of_le hQ1Le with
    | inl hEqM =>
      have hModR : (x.toNat + (2 ^ k - 1)) % 2 ^ 64 = r - 1 := by
        rw [hS, hEqM, ← hPow64, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_of_le_of_lt
          (Nat.sub_le _ 1) hrLt) (pow2_lt_64 hkLt))
      have hDiv0 : (x.toNat + (2 ^ k - 1)) % 2 ^ 64 / 2 ^ k = 0 := by
        rw [hModR]
        exact Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ 1) hrLt)
      rw [hDiv0, Nat.zero_mul, hSumX, hEqM, ← hPow64, Nat.mod_self]
    | inr hLtM =>
      have hSLt64 : x.toNat + (2 ^ k - 1) < 2 ^ 64 := by
        have hMulQ1 : (q + 1) * 2 ^ k + 2 ^ k = ((q + 1) + 1) * 2 ^ k := by
          have h := Nat.add_mul (q + 1) 1 (2 ^ k)
          rw [Nat.one_mul] at h
          exact h.symm
        calc x.toNat + (2 ^ k - 1)
            = (q + 1) * 2 ^ k + (r - 1) := hS
          _ < (q + 1) * 2 ^ k + 2 ^ k :=
              Nat.add_lt_add_left (Nat.lt_of_le_of_lt (Nat.sub_le _ 1) hrLt) _
          _ = ((q + 1) + 1) * 2 ^ k := hMulQ1
          _ ≤ 2 ^ (64 - k) * 2 ^ k := Nat.mul_le_mul_right _ hLtM
          _ = 2 ^ 64 := hPow64.symm
      have hSumLt64 : x.toNat + p.toNat < 2 ^ 64 := by
        have hMulQ1 : (q + 1) * 2 ^ k + 2 ^ k = ((q + 1) + 1) * 2 ^ k := by
          have h := Nat.add_mul (q + 1) 1 (2 ^ k)
          rw [Nat.one_mul] at h
          exact h.symm
        calc x.toNat + p.toNat
            = (q + 1) * 2 ^ k := hSumX
          _ < 2 ^ (64 - k) * 2 ^ k := by
              have hPos : 0 < 2 ^ k := hPk
              calc (q + 1) * 2 ^ k
                  < (q + 1) * 2 ^ k + 2 ^ k := Nat.lt_add_of_pos_right hPos
                _ = ((q + 1) + 1) * 2 ^ k := hMulQ1
                _ ≤ 2 ^ (64 - k) * 2 ^ k := Nat.mul_le_mul_right _ hLtM
          _ = 2 ^ 64 := hPow64.symm
      have hDivQ1 : (x.toNat + (2 ^ k - 1)) % 2 ^ 64 / 2 ^ k = q + 1 := by
        rw [Nat.mod_eq_of_lt hSLt64, hS, Nat.add_comm ((q + 1) * 2 ^ k),
          Nat.mul_comm (q + 1) _, Nat.add_mul_div_left _ _ hPk,
          Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ 1) hrLt),
          Nat.zero_add]
      rw [hDivQ1, Nat.mod_eq_of_lt hSumLt64, hSumX]

private theorem padding_for_elems_equiv
    (sizeBase offset elemSize align phase elems : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) (_hPh : phase.toNat < align.toNat) :
    Spec.paddingForElemsFast sizeBase offset elemSize align phase elems =
      Spec.paddingForElemsNaive sizeBase offset elemSize align phase elems ∧
    (elemSize.toNat % align.toNat = 0 →
      Spec.paddingForElemsFast sizeBase offset elemSize align phase elems =
        Spec.paddingForElemsFast sizeBase offset elemSize align phase
          (BitVec.ofNat 64 0)) := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hAlPos : (BitVec.ofNat 64 1).toNat ≤ align.toNat := by
    rw [hAlNat]; exact Nat.two_pow_pos k
  have hMaskNat : (align - BitVec.ofNat 64 1).toNat = 2 ^ k - 1 := by
    rw [bv64_toNat_sub_of_le hAlPos, hAlNat]
    rfl
  have hMEq : align - BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ k - 1) :=
    bv64_eq_of_toNat_eq (by
      rw [hMaskNat, bv64_toNat_ofNat, Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) Nat.zero_lt_one)
          (pow2_le_of_le (Nat.le_of_lt hkLt)))])
  let trailingBytes := Spec.bv64Mul elems elemSize
  let roundingInputNaive := phase + trailingBytes
  let elemRem := Spec.bv64And elemSize (align - BitVec.ofNat 64 1)
  let trailingRem := Spec.bv64And (Spec.bv64Mul elems elemRem)
    (align - BitVec.ofNat 64 1)
  let roundingInputFast := phase + trailingRem
  have hElemRemNat : elemRem.toNat = elemSize.toNat % 2 ^ k := by
    change (Spec.bv64And elemSize (align - BitVec.ofNat 64 1)).toNat = _
    rw [hMEq, bv64And_lowMask elemSize (Nat.le_of_lt hkLt)]
  have hTrailRemNat : trailingRem.toNat =
      (elems.toNat * elemSize.toNat) % 2 ^ k := by
    change (Spec.bv64And (Spec.bv64Mul elems elemRem)
        (align - BitVec.ofNat 64 1)).toNat = _
    rw [hMEq, bv64And_lowMask _ (Nat.le_of_lt hkLt),
      bv64_mod_pow2_mul elems elemRem (Nat.le_of_lt hkLt), hElemRemNat]
    exact nat_mul_mod_mod _ _ _
  have hModAgree : roundingInputFast.toNat % align.toNat =
      roundingInputNaive.toNat % align.toNat := by
    rw [hAlNat]
    show (phase + trailingRem).toNat % 2 ^ k =
      (phase + trailingBytes).toNat % 2 ^ k
    rw [bv64_mod_pow2_add phase trailingRem (Nat.le_of_lt hkLt),
      bv64_mod_pow2_add phase trailingBytes (Nat.le_of_lt hkLt),
      hTrailRemNat, nat_add_mod_mod]
    rw [← nat_add_mod_mod phase.toNat trailingBytes.toNat (2 ^ k)]
    change (phase.toNat + elems.toNat * elemSize.toNat) % 2 ^ k =
      (phase.toNat + (Spec.bv64Mul elems elemSize).toNat % 2 ^ k) % 2 ^ k
    rw [bv64_mod_pow2_mul elems elemSize (Nat.le_of_lt hkLt), nat_add_mod_mod]
  have hPadEq : Spec.paddingNeededFor64 roundingInputFast align =
      Spec.paddingNeededFor64 roundingInputNaive align := by
    apply bv64_eq_of_toNat_eq
    rw [(paddingNeededFor64_spec roundingInputFast align hPow).1,
      (paddingNeededFor64_spec roundingInputNaive align hPow).1, hModAgree]
  have hNaiveEq :
      Spec.paddingForElemsNaive sizeBase offset elemSize align phase elems =
      ((sizeBase + phase) - offset) +
        Spec.paddingNeededFor64 roundingInputNaive align := by
    unfold Spec.paddingForElemsNaive
    dsimp only
    change (sizeBase + Spec.roundDown64 (roundingInputNaive +
        (align - BitVec.ofNat 64 1)) align) -
        (offset + trailingBytes) =
      ((sizeBase + phase) - offset) +
        Spec.paddingNeededFor64 roundingInputNaive align
    rw [bv64_roundUp_eq_add_pad roundingInputNaive align hPow]
    let pad := Spec.paddingNeededFor64 roundingInputNaive align
    calc (sizeBase + (roundingInputNaive + pad)) - (offset + trailingBytes)
        = (sizeBase + ((phase + trailingBytes) + pad)) -
            (offset + trailingBytes) := rfl
      _ = ((sizeBase + (phase + pad)) + trailingBytes) -
            (offset + trailingBytes) := by
          rw [bv64_add_assoc phase trailingBytes pad,
            bv64_add_comm trailingBytes pad,
            ← bv64_add_assoc phase pad trailingBytes,
            ← bv64_add_assoc sizeBase (phase + pad) trailingBytes]
      _ = (sizeBase + (phase + pad)) - offset :=
          bv64_sub_add_cancel_right _ _ trailingBytes
      _ = ((sizeBase + phase) - offset) + pad := by
          rw [← bv64_add_assoc sizeBase phase pad,
            bv64_sub_eq_add_neg, bv64_sub_eq_add_neg,
            ← bv64_add_assoc (bv64Neg offset) (sizeBase + phase) pad]
  have hFastEq :
      Spec.paddingForElemsFast sizeBase offset elemSize align phase elems =
      Spec.paddingForElemsNaive sizeBase offset elemSize align phase elems := by
    unfold Spec.paddingForElemsFast
    dsimp only
    rw [hNaiveEq]
    change ((sizeBase + phase) - offset) +
        Spec.paddingNeededFor64 roundingInputFast align =
      ((sizeBase + phase) - offset) +
        Spec.paddingNeededFor64 roundingInputNaive align
    rw [hPadEq]
  refine ⟨hFastEq, fun hDvd => ?_⟩
  unfold Spec.paddingForElemsFast
  dsimp only
  have hER0 : Spec.bv64And elemSize (align - BitVec.ofNat 64 1) =
      BitVec.ofNat 64 0 := by
    apply bv64_eq_of_toNat_eq
    rw [show Spec.bv64And elemSize (align - BitVec.ofNat 64 1) = elemRem
        from rfl, hElemRemNat, ← hAlNat, hDvd]
    rfl
  have hZeroMul1 : Spec.bv64Mul elems (BitVec.ofNat 64 0) =
      BitVec.ofNat 64 0 := by
    apply bv64_eq_of_toNat_eq
    unfold Spec.bv64Mul
    rw [show (BitVec.ofNat 64 0).toNat = 0 from rfl, Nat.mul_zero]
    rfl
  have hZeroMul0 : Spec.bv64Mul (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) =
      BitVec.ofNat 64 0 := by
    apply bv64_eq_of_toNat_eq
    unfold Spec.bv64Mul
    rw [show (BitVec.ofNat 64 0).toNat = 0 from rfl, Nat.zero_mul]
    rfl
  rw [hER0, hZeroMul1, bv64And_zero_left, hZeroMul0, bv64And_zero_left]

/-! ### Cluster 3 Proofs: `max_trailing_bytes` Iff Optimality -/

private theorem roundUpNat_zero (a : Nat) : Spec.roundUpNat 0 a = 0 := by
  unfold Spec.roundUpNat
  rw [ite_prop_true (Nat.zero_mod a)]

private theorem roundUpNat_of_lt {x a : Nat} (hx : 0 < x) (hlt : x < a) :
    Spec.roundUpNat x a = a := by
  unfold Spec.roundUpNat
  have hMod : x % a = x := Nat.mod_eq_of_lt hlt
  have hNe : x % a ≠ 0 := by rw [hMod]; exact Nat.ne_of_gt hx
  rw [ite_prop_false hNe, hMod]
  exact Nat.add_sub_of_le (Nat.le_of_lt hlt)

private theorem roundUpNat_dvd (x : Nat) {a : Nat} (ha : 0 < a) :
    a ∣ Spec.roundUpNat x a ∧ x ≤ Spec.roundUpNat x a := by
  unfold Spec.roundUpNat
  cases hm : Nat.beq (x % a) 0 with
  | true =>
    have h0 := Nat.eq_of_beq_eq_true hm
    rw [ite_prop_true h0]
    exact ⟨nat_dvd_of_mod_eq_zero h0, Nat.le_refl _⟩
  | false =>
    have hNe : x % a ≠ 0 := fun h => by rw [h] at hm; cases hm
    rw [ite_prop_false hNe]
    have hSplit : x = (x / a) * a + x % a := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod x a).symm
    have hSum : x + (a - x % a) = (x / a + 1) * a := by
      calc x + (a - x % a)
          = ((x / a) * a + x % a) + (a - x % a) :=
              congrArg (fun z => z + (a - x % a)) hSplit
        _ = (x / a) * a + (x % a + (a - x % a)) := Nat.add_assoc _ _ _
        _ = (x / a) * a + a := by
              rw [Nat.add_sub_of_le (Nat.le_of_lt (Nat.mod_lt x ha))]
        _ = (x / a + 1) * a := by rw [Nat.add_mul, Nat.one_mul]
    exact ⟨⟨x / a + 1, by rw [hSum, Nat.mul_comm]⟩, Nat.le_add_right _ _⟩

private theorem roundUpNat_le_iff_of_dvd {x M a : Nat} (ha : 0 < a)
    (hDvd : a ∣ M) :
    Spec.roundUpNat x a ≤ M ↔ x ≤ M := by
  constructor
  · intro hLe
    exact Nat.le_trans (roundUpNat_dvd x ha).2 hLe
  · intro hLe
    cases hm : Nat.beq (x % a) 0 with
    | true =>
      have h0 := Nat.eq_of_beq_eq_true hm
      unfold Spec.roundUpNat
      rw [ite_prop_true h0]
      exact hLe
    | false =>
      have hNe : x % a ≠ 0 := fun h => by rw [h] at hm; cases hm
      unfold Spec.roundUpNat
      rw [ite_prop_false hNe]
      have hRemPos : 0 < x % a := Nat.pos_of_ne_zero hNe
      let ⟨m, hmEq⟩ := hDvd
      have hSplit : x = (x / a) * a + x % a := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod x a).symm
      have hSum : x + (a - x % a) = (x / a + 1) * a := by
        calc x + (a - x % a)
            = ((x / a) * a + x % a) + (a - x % a) :=
                congrArg (fun z => z + (a - x % a)) hSplit
          _ = (x / a) * a + (x % a + (a - x % a)) := Nat.add_assoc _ _ _
          _ = (x / a) * a + a := by
                rw [Nat.add_sub_of_le (Nat.le_of_lt (Nat.mod_lt x ha))]
          _ = (x / a + 1) * a := by rw [Nat.add_mul, Nat.one_mul]
      have hStrict : (x / a) * a < m * a := by
        calc (x / a) * a
            < (x / a) * a + x % a := Nat.lt_add_of_pos_right hRemPos
          _ = x := hSplit.symm
          _ ≤ M := hLe
          _ = m * a := by rw [hmEq, Nat.mul_comm]
      have hQLt : x / a < m := nat_lt_of_mul_lt_mul_right hStrict
      rw [hSum, hmEq, Nat.mul_comm a m]
      exact Nat.mul_le_mul_right a hQLt

private theorem objectSizeNat_zero_eq (sb al ph : Nat) (hPh : ph < al) :
    Spec.objectSizeNat sb al ph 0 =
      sb + (if ph = 0 then 0 else al) := by
  unfold Spec.objectSizeNat
  rw [Nat.add_zero]
  cases hp : Nat.beq ph 0 with
  | true =>
    have h0 := Nat.eq_of_beq_eq_true hp
    rw [ite_prop_true h0, h0, roundUpNat_zero]
  | false =>
    have hNe : ph ≠ 0 := fun h => by rw [h] at hp; cases hp
    rw [ite_prop_false hNe, roundUpNat_of_lt (Nat.pos_of_ne_zero hNe) hPh]

private theorem checkedAdd64_of_le (a b : BitVec 64)
    (hLe : a.toNat + b.toNat ≤ Spec.usizeMaxNat) :
    Spec.checkedAdd64 a b = some (a + b) ∧
    (a + b).toNat = a.toNat + b.toNat := by
  unfold Spec.checkedAdd64
  rw [nat_ble_true _ _ hLe]
  have hLt : a.toNat + b.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hLe (by decide)
  exact ⟨rfl, by rw [bv64_toNat_add]; exact Nat.mod_eq_of_lt hLt⟩

private theorem checkedAdd64_none_of_gt (a b : BitVec 64)
    (hGt : Spec.usizeMaxNat < a.toNat + b.toNat) :
    Spec.checkedAdd64 a b = none := by
  unfold Spec.checkedAdd64
  rw [nat_ble_false _ _ hGt]
  rfl

private theorem checkedSub64_of_le (a b : BitVec 64) (hLe : b.toNat ≤ a.toNat) :
    Spec.checkedSub64 a b = some (a - b) ∧
    (a - b).toNat = a.toNat - b.toNat := by
  unfold Spec.checkedSub64
  rw [nat_ble_true _ _ hLe]
  exact ⟨rfl, bv64_toNat_sub_of_le hLe⟩

private theorem checkedSub64_none_of_gt (a b : BitVec 64)
    (hGt : a.toNat < b.toNat) :
    Spec.checkedSub64 a b = none := by
  unfold Spec.checkedSub64
  rw [nat_ble_false _ _ hGt]
  rfl

private theorem checkedMul64_of_le (a b : BitVec 64)
    (hLe : a.toNat * b.toNat ≤ Spec.usizeMaxNat) :
    Spec.checkedMul64 a b = some (Spec.bv64Mul a b) ∧
    (Spec.bv64Mul a b).toNat = a.toNat * b.toNat := by
  unfold Spec.checkedMul64 Spec.bv64Mul
  rw [nat_ble_true _ _ hLe]
  have hLt : a.toNat * b.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hLe (by decide)
  exact ⟨rfl, by rw [bv64_toNat_ofNat]; exact Nat.mod_eq_of_lt hLt⟩

private theorem checkedMul64_none_of_gt (a b : BitVec 64)
    (hGt : Spec.usizeMaxNat < a.toNat * b.toNat) :
    Spec.checkedMul64 a b = none := by
  unfold Spec.checkedMul64
  rw [nat_ble_false _ _ hGt]
  rfl

private theorem maxTrailingBytes_spec
    (sizeBase align phase available : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) (hPh : phase.toNat < align.toNat) :
    Spec.maxTrailingBytesImpl64 sizeBase align phase available =
      Spec.maxTrailingBytesKaniSpec64 sizeBase align phase available ∧
    ((∃ m, Spec.maxTrailingBytesImpl64 sizeBase align phase available =
        some m) ↔
      Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat 0 ≤
        available.toNat) ∧
    (∀ m : BitVec 64,
      Spec.maxTrailingBytesImpl64 sizeBase align phase available = some m →
      (let rp :=
        if phase == BitVec.ofNat 64 0 then BitVec.ofNat 64 0 else align
       let eb := available - (sizeBase + rp)
       let ab := Spec.roundDown64 eb align
       let ip := rp - phase
       Spec.bv64Or ab ip = ab + ip ∧ ab.toNat + ip.toNat = m.toNat) ∧
      (∀ tb : Nat,
        Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat tb ≤
          available.toNat ↔
          tb ≤ m.toNat)) := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hAlPos : 0 < align.toNat := by rw [hAlNat]; exact Nat.two_pow_pos k
  let rp := if phase == BitVec.ofNat 64 0 then BitVec.ofNat 64 0 else align
  have hRpEq : (if phase == BitVec.ofNat 64 0 then BitVec.ofNat 64 0
      else align) = rp := rfl
  have hRpNat : rp.toNat = if phase.toNat = 0 then 0 else align.toNat := by
    cases hz : (phase == BitVec.ofNat 64 0) with
    | true =>
      have hPh0 : phase.toNat = 0 := by
        have hb : phase = BitVec.ofNat 64 0 := eq_of_beq hz
        rw [hb]; rfl
      have hrp0 : rp = BitVec.ofNat 64 0 := by
        change (if (phase == BitVec.ofNat 64 0) = true
          then BitVec.ofNat 64 0 else align) = BitVec.ofNat 64 0
        rw [hz]
        rfl
      rw [hrp0, ite_prop_true hPh0]; rfl
    | false =>
      have hNe : phase.toNat ≠ 0 := fun h0 => by
        have hb : phase = BitVec.ofNat 64 0 := bv64_eq_of_toNat_eq h0
        rw [hb, beq_self_eq_true] at hz
        cases hz
      have hrpAl : rp = align := by
        change (if (phase == BitVec.ofNat 64 0) = true
          then BitVec.ofNat 64 0 else align) = align
        rw [hz]
        rfl
      rw [hrpAl, ite_prop_false hNe]
  have hObj0 : Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat 0 =
      sizeBase.toNat + rp.toNat := by
    rw [objectSizeNat_zero_eq _ _ _ hPh, hRpNat]
  have hRpDvd : align.toNat ∣ rp.toNat := by
    rw [hRpNat]
    cases hp : Nat.beq phase.toNat 0 with
    | true =>
      rw [ite_prop_true (Nat.eq_of_beq_eq_true hp)]
      exact nat_dvd_zero _
    | false =>
      have hNe : phase.toNat ≠ 0 := fun h => by rw [h] at hp; cases hp
      rw [ite_prop_false hNe]
      exact nat_dvd_refl _
  have hPhLeRp : phase.toNat ≤ rp.toNat := by
    rw [hRpNat]
    cases hp : Nat.beq phase.toNat 0 with
    | true =>
      have h0 := Nat.eq_of_beq_eq_true hp
      rw [ite_prop_true h0, h0]
      exact Nat.le_refl 0
    | false =>
      have hNe : phase.toNat ≠ 0 := fun h => by rw [h] at hp; cases hp
      rw [ite_prop_false hNe]
      exact Nat.le_of_lt hPh
  have hRpSubPhLt : rp.toNat - phase.toNat < align.toNat := by
    rw [hRpNat]
    cases hp : Nat.beq phase.toNat 0 with
    | true =>
      have h0 := Nat.eq_of_beq_eq_true hp
      rw [ite_prop_true h0, h0, Nat.sub_self]
      exact hAlPos
    | false =>
      have hNe : phase.toNat ≠ 0 := fun h => by rw [h] at hp; cases hp
      rw [ite_prop_false hNe]
      exact Nat.sub_lt hAlPos (Nat.pos_of_ne_zero hNe)
  cases Nat.lt_or_ge available.toNat (sizeBase.toNat + rp.toNat) with
  | inl hTooBig =>
    have hImplNone :
        Spec.maxTrailingBytesImpl64 sizeBase align phase available = none := by
      unfold Spec.maxTrailingBytesImpl64
      dsimp only
      rw [hRpEq]
      cases Nat.lt_or_ge Spec.usizeMaxNat (sizeBase.toNat + rp.toNat) with
      | inl hOv =>
        rw [checkedAdd64_none_of_gt sizeBase rp hOv]
      | inr hFit =>
        let cAdd := checkedAdd64_of_le sizeBase rp hFit
        rw [cAdd.1]
        dsimp only
        have hAvLt : available.toNat < (sizeBase + rp).toNat := by
          rw [cAdd.2]; exact hTooBig
        rw [checkedSub64_none_of_gt available _ hAvLt]
    have hKaniNone :
        Spec.maxTrailingBytesKaniSpec64 sizeBase align phase available =
          none := by
      unfold Spec.maxTrailingBytesKaniSpec64
      cases Nat.lt_or_ge available.toNat sizeBase.toNat with
      | inl hAvSb => rw [checkedSub64_none_of_gt available sizeBase hAvSb]
      | inr hSbAv =>
        let cSub := checkedSub64_of_le available sizeBase hSbAv
        rw [cSub.1]
        dsimp only
        have hPhPos : 0 < phase.toNat := by
          cases hp : Nat.beq phase.toNat 0 with
          | true =>
            have h0 := Nat.eq_of_beq_eq_true hp
            have hRp0 : rp.toNat = 0 := by rw [hRpNat, ite_prop_true h0]
            rw [hRp0, Nat.add_zero] at hTooBig
            exact False.elim (Nat.not_le_of_gt hTooBig hSbAv)
          | false =>
            exact Nat.pos_of_ne_zero (fun h => by rw [h] at hp; cases hp)
        have hRpAl : rp.toNat = align.toNat := by
          rw [hRpNat]
          exact ite_prop_false (Nat.ne_of_gt hPhPos)
        have hRemLtAl : (available - sizeBase).toNat < align.toNat := by
          rw [cSub.2]
          rw [hRpAl] at hTooBig
          have h1 := Nat.sub_lt_sub_right hSbAv hTooBig
          rw [Nat.add_comm, Nat.add_sub_cancel] at h1
          exact h1
        have hRd0 :
            (Spec.roundDown64 (available - sizeBase) align).toNat = 0 := by
          rw [(roundDown64_spec (available - sizeBase) align hPow).1,
            Nat.div_eq_of_lt hRemLtAl, Nat.zero_mul]
        have hGtRd : (Spec.roundDown64 (available - sizeBase) align).toNat <
            phase.toNat := by
          rw [hRd0]; exact hPhPos
        rw [checkedSub64_none_of_gt _ phase hGtRd]
    rw [hImplNone, hKaniNone, hObj0]
    refine ⟨rfl,
      ⟨(fun h => by let ⟨_, hs⟩ := h; cases hs),
        (fun h => False.elim (Nat.not_lt_of_ge h hTooBig))⟩,
      (fun _ h => by cases h)⟩
  | inr hFits =>
    have hSumLeMax : sizeBase.toNat + rp.toNat ≤ Spec.usizeMaxNat :=
      Nat.le_trans hFits (Nat.le_pred_of_lt available.isLt)
    let cAdd := checkedAdd64_of_le sizeBase rp hSumLeMax
    let minSize := sizeBase + rp
    have hMinLe : minSize.toNat ≤ available.toNat := by
      rw [cAdd.2]; exact hFits
    let cSub := checkedSub64_of_le available minSize hMinLe
    let eb := available - minSize
    let ab := Spec.roundDown64 eb align
    let ip := rp - phase
    let rdAb := roundDown64_spec eb align hPow
    have hAbMod : ab.toNat % 2 ^ k = 0 := by
      rw [← hAlNat]; exact rdAb.2.2.1
    have hIpNat : ip.toNat = rp.toNat - phase.toNat :=
      bv64_toNat_sub_of_le hPhLeRp
    have hIpLt2k : ip.toNat < 2 ^ k := by
      rw [← hAlNat, hIpNat]; exact hRpSubPhLt
    let d := bv64Or_disjoint_add (Nat.le_of_lt hkLt) hAbMod hIpLt2k
    let m := Spec.bv64Or ab ip
    have hImplSome :
        Spec.maxTrailingBytesImpl64 sizeBase align phase available =
          some m := by
      unfold Spec.maxTrailingBytesImpl64
      dsimp only
      rw [hRpEq, cAdd.1]
      dsimp only
      rw [cSub.1]
    have hSbLeAv : sizeBase.toNat ≤ available.toNat :=
      Nat.le_trans (Nat.le_add_right _ _) hFits
    let cSubAvSb := checkedSub64_of_le available sizeBase hSbLeAv
    let bytes := available - sizeBase
    let rdBytes := Spec.roundDown64 bytes align
    have hBytesSplit : bytes.toNat = rp.toNat + eb.toNat := by
      rw [cSubAvSb.2, cSub.2, cAdd.2]
      have hAdd := Nat.add_sub_of_le hFits
      rw [Nat.add_assoc] at hAdd
      exact ((congrArg (fun z => z - sizeBase.toNat) hAdd).symm.trans
        (Nat.add_sub_cancel_left _ _))
    let ⟨qRp, hqRp⟩ := hRpDvd
    have hRdBytesEq : rdBytes.toNat = rp.toNat + ab.toNat := by
      rw [(roundDown64_spec bytes align hPow).1, hBytesSplit, hqRp,
        Nat.add_comm _ eb.toNat, Nat.add_mul_div_left _ _ hAlPos,
        Nat.add_mul, Nat.add_comm, Nat.mul_comm qRp align.toNat, ← hqRp,
        rdAb.1]
    have hPhLeRdBytes : phase.toNat ≤ rdBytes.toNat := by
      rw [hRdBytesEq]
      exact Nat.le_trans hPhLeRp (Nat.le_add_right _ _)
    let cSubKani := checkedSub64_of_le rdBytes phase hPhLeRdBytes
    have hMNat : m.toNat = ab.toNat + (rp.toNat - phase.toNat) := by
      rw [d.2.1, hIpNat]
    have hKaniEqM : rdBytes - phase = m := by
      apply bv64_eq_of_toNat_eq
      rw [cSubKani.2, hMNat, hRdBytesEq, Nat.add_comm rp.toNat ab.toNat,
        ← Nat.add_sub_assoc hPhLeRp]
    have hKaniSome :
        Spec.maxTrailingBytesKaniSpec64 sizeBase align phase available =
          some m := by
      unfold Spec.maxTrailingBytesKaniSpec64
      rw [cSubAvSb.1]
      dsimp only
      rw [cSubKani.1, hKaniEqM]
    have hOpt : ∀ tb : Nat,
        Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat tb ≤
          available.toNat ↔ tb ≤ m.toNat := by
      intro tb
      let M := rp.toNat + ab.toNat
      have hMDvd : align.toNat ∣ M :=
        nat_dvd_add hRpDvd (nat_dvd_of_mod_eq_zero rdAb.2.2.1)
      have hMLo : sizeBase.toNat + M ≤ available.toNat := by
        have hAbLe : ab.toNat ≤ eb.toNat := rdAb.2.1
        calc sizeBase.toNat + M
            = (sizeBase.toNat + rp.toNat) + ab.toNat :=
                (Nat.add_assoc _ _ _).symm
          _ ≤ (sizeBase.toNat + rp.toNat) + eb.toNat :=
                Nat.add_le_add_left hAbLe _
          _ = available.toNat := by
                rw [cSub.2, cAdd.2, Nat.add_sub_of_le hFits]
      have hMHi : available.toNat < sizeBase.toNat + M + align.toNat := by
        have hEbLt := rdAb.2.2.2
        calc available.toNat
            = (sizeBase.toNat + rp.toNat) + eb.toNat := by
                rw [cSub.2, cAdd.2, Nat.add_sub_of_le hFits]
          _ < (sizeBase.toNat + rp.toNat) + (ab.toNat + align.toNat) :=
                Nat.add_lt_add_left hEbLt _
          _ = sizeBase.toNat + M + align.toNat := by
                rw [Nat.add_assoc,
                  ← Nat.add_assoc rp.toNat ab.toNat align.toNat,
                  ← Nat.add_assoc sizeBase.toNat M align.toNat]
      unfold Spec.objectSizeNat
      have hStep1 :
          sizeBase.toNat + Spec.roundUpNat (phase.toNat + tb) align.toNat ≤
            available.toNat ↔
          Spec.roundUpNat (phase.toNat + tb) align.toNat ≤ M := by
        constructor
        · intro hOb
          have hRuDvd : align.toNat ∣
              Spec.roundUpNat (phase.toNat + tb) align.toNat :=
            (roundUpNat_dvd _ hAlPos).1
          let ⟨u, hu⟩ := hRuDvd
          let ⟨q, hq⟩ := hMDvd
          have hSumLt : sizeBase.toNat + u * align.toNat <
              sizeBase.toNat + (q + 1) * align.toNat := by
            calc sizeBase.toNat + u * align.toNat
                = sizeBase.toNat +
                    Spec.roundUpNat (phase.toNat + tb) align.toNat := by
                    rw [hu, Nat.mul_comm]
              _ ≤ available.toNat := hOb
              _ < sizeBase.toNat + M + align.toNat := hMHi
              _ = sizeBase.toNat + (q + 1) * align.toNat := by
                    rw [hq, Nat.mul_comm align.toNat q, Nat.add_assoc,
                      Nat.add_mul, Nat.one_mul]
          have hMulLt : u * align.toNat < (q + 1) * align.toNat :=
            nat_lt_of_add_lt_add_left hSumLt
          have hULe : u ≤ q := Nat.le_of_lt_succ
            (nat_lt_of_mul_lt_mul_right hMulLt)
          rw [hu, hq, Nat.mul_comm align.toNat u, Nat.mul_comm align.toNat q]
          exact Nat.mul_le_mul_right align.toNat hULe
        · intro hRuM
          exact Nat.le_trans (Nat.add_le_add_left hRuM _) hMLo
      have hStep2 :
          Spec.roundUpNat (phase.toNat + tb) align.toNat ≤ M ↔
            phase.toNat + tb ≤ M :=
        roundUpNat_le_iff_of_dvd hAlPos hMDvd
      have hStep3 : phase.toNat + tb ≤ M ↔ tb ≤ m.toNat := by
        have hEqM : M = phase.toNat + m.toNat := by
          calc M
              = rp.toNat + ab.toNat := rfl
            _ = (phase.toNat + (rp.toNat - phase.toNat)) + ab.toNat := by
                  rw [Nat.add_sub_of_le hPhLeRp]
            _ = phase.toNat + (ab.toNat + (rp.toNat - phase.toNat)) := by
                  rw [Nat.add_assoc, Nat.add_comm (rp.toNat - phase.toNat)]
            _ = phase.toNat + m.toNat := by rw [← hMNat]
        rw [hEqM]
        exact ⟨fun h => Nat.le_of_add_le_add_left h,
          fun h => Nat.add_le_add_left h _⟩
      exact Iff.trans hStep1 (Iff.trans hStep2 hStep3)
    rw [hImplSome, hKaniSome, hObj0]
    refine ⟨rfl, ⟨fun _ => hFits, fun _ => ⟨m, rfl⟩⟩, fun m' hm => ?_⟩
    injection hm with hmEq
    subst hmEq
    change (Spec.bv64Or ab ip = ab + ip ∧ ab.toNat + ip.toNat = m.toNat) ∧ _
    exact ⟨⟨d.1, d.2.1.symm⟩, hOpt⟩

/-! ### Cluster 4 Proofs: `size_for_elems` & `size_for_elems_unchecked` -/

private theorem sliceDstSizeForTrailingBytes64_iff
    (sizeBase align phase ts : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) (_hPh : phase.toNat < align.toNat) :
    ((∃ s,
        Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts = some s) ↔
      Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat ts.toNat ≤
        Spec.usizeMaxNat) ∧
    (∀ s, Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts = some s →
      s.toNat =
        Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat ts.toNat ∧
      s = sizeBase + ((phase + ts) +
        Spec.paddingNeededFor64 (phase + ts) align)) := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hAlPos : 0 < align.toNat := by rw [hAlNat]; exact Nat.two_pow_pos k
  let x := phase.toNat + ts.toNat
  have hXLeRu : x ≤ Spec.roundUpNat x align.toNat :=
    (roundUpNat_dvd x hAlPos).2
  have hRuLeObj : Spec.roundUpNat x align.toNat ≤
      Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat ts.toNat :=
    Nat.le_add_left _ _
  have hPadFormula : ∀ (w : BitVec 64), w.toNat = x →
      w.toNat + (Spec.paddingNeededFor64 w align).toNat =
        Spec.roundUpNat x align.toNat := by
    intro w hw
    rw [(paddingNeededFor64_spec w align hPow).1, hw]
    unfold Spec.roundUpNat
    cases hm : Nat.beq (x % align.toNat) 0 with
    | true =>
      have h0 := Nat.eq_of_beq_eq_true hm
      rw [ite_prop_true h0, ite_prop_true h0, Nat.add_zero]
    | false =>
      have hNe : x % align.toNat ≠ 0 := fun h => by rw [h] at hm; cases hm
      rw [ite_prop_false hNe, ite_prop_false hNe]
  cases Nat.lt_or_ge Spec.usizeMaxNat x with
  | inl hxOv =>
    have hObjGt : Spec.usizeMaxNat <
        Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat
          ts.toNat :=
      Nat.lt_of_lt_of_le hxOv (Nat.le_trans hXLeRu hRuLeObj)
    have hNone :
        Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts =
          none := by
      unfold Spec.sliceDstSizeForTrailingBytes64
      rw [checkedAdd64_none_of_gt phase ts hxOv]
    rw [hNone]
    exact ⟨⟨(fun h => by let ⟨_, hs⟩ := h; cases hs),
        (fun h => False.elim (Nat.not_lt_of_ge h hObjGt))⟩,
      (fun _ h => by cases h)⟩
  | inr hxFit =>
    let c1 := checkedAdd64_of_le phase ts hxFit
    let w := phase + ts
    have hwNat : w.toNat = x := c1.2
    let p := Spec.paddingNeededFor64 w align
    have hSumPad : w.toNat + p.toNat = Spec.roundUpNat x align.toNat :=
      hPadFormula w hwNat
    cases Nat.lt_or_ge Spec.usizeMaxNat (w.toNat + p.toNat) with
    | inl hpOv =>
      have hObjGt : Spec.usizeMaxNat <
          Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat
            ts.toNat := by
        rw [hSumPad] at hpOv
        exact Nat.lt_of_lt_of_le hpOv hRuLeObj
      have hNone :
          Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts =
            none := by
        unfold Spec.sliceDstSizeForTrailingBytes64
        rw [c1.1]
        dsimp only
        rw [checkedAdd64_none_of_gt w p hpOv]
      rw [hNone]
      exact ⟨⟨(fun h => by let ⟨_, hs⟩ := h; cases hs),
          (fun h => False.elim (Nat.not_lt_of_ge h hObjGt))⟩,
        (fun _ h => by cases h)⟩
    | inr hpFit =>
      let c2 := checkedAdd64_of_le w p hpFit
      let rounded := w + p
      have hRdNat : rounded.toNat = Spec.roundUpNat x align.toNat := by
        rw [c2.2, hSumPad]
      have hObjEq : sizeBase.toNat + rounded.toNat =
          Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat
            ts.toNat := by
        rw [hRdNat]; rfl
      cases Nat.lt_or_ge Spec.usizeMaxNat (sizeBase.toNat + rounded.toNat) with
      | inl hsOv =>
        rw [hObjEq] at hsOv
        have hNone :
            Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts =
              none := by
          unfold Spec.sliceDstSizeForTrailingBytes64
          rw [c1.1]
          dsimp only
          rw [c2.1]
          dsimp only
          rw [checkedAdd64_none_of_gt sizeBase rounded
            (by rw [← hObjEq] at hsOv; exact hsOv)]
        rw [hNone]
        exact ⟨⟨(fun h => by let ⟨_, hs⟩ := h; cases hs),
            (fun h => False.elim (Nat.not_lt_of_ge h hsOv))⟩,
          (fun _ h => by cases h)⟩
      | inr hsFit =>
        let c3 := checkedAdd64_of_le sizeBase rounded hsFit
        let s := sizeBase + rounded
        have hSome :
            Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts =
              some s := by
          unfold Spec.sliceDstSizeForTrailingBytes64
          rw [c1.1]
          dsimp only
          rw [c2.1]
          dsimp only
          exact c3.1
        rw [hSome]
        refine ⟨⟨fun _ => by rw [← hObjEq]; exact hsFit,
          fun _ => ⟨s, rfl⟩⟩, ?_⟩
        intro s' hs'
        injection hs' with hEq
        subst hEq
        exact ⟨by rw [c3.2, hObjEq], rfl⟩

private theorem size_for_elems_spec
    (sizeBase offset elemSize align phase elems : BitVec 64)
    (hPow : Spec.isPowerOfTwo64 align) (hPh : phase.toNat < align.toNat) :
    Spec.sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
      Spec.sizeForElemsKaniSpec64 sizeBase elemSize align phase elems ∧
    ((∃ s, Spec.sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
        some s) ↔
      (elems.toNat * elemSize.toNat ≤ Spec.usizeMaxNat ∧
       Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat
         (elems.toNat * elemSize.toNat) ≤ Spec.usizeMaxNat)) ∧
    (∀ s : BitVec 64,
      Spec.sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
        some s →
      s.toNat = Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat
        (elems.toNat * elemSize.toNat)) ∧
    (∀ (trailingSize trailingEnd s : BitVec 64),
      Spec.checkedMul64 elems elemSize = some trailingSize →
      Spec.checkedAdd64 offset trailingSize = some trailingEnd →
      Spec.sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
        some s →
      trailingEnd ≤ s →
      let pad :=
        Spec.paddingForElemsFast sizeBase offset elemSize align phase elems
      elems.toNat * elemSize.toNat = trailingSize.toNat ∧
      trailingSize.toNat ≤ Spec.usizeMaxNat ∧
      offset.toNat + trailingSize.toNat = trailingEnd.toNat ∧
      trailingEnd.toNat ≤ Spec.usizeMaxNat ∧
      trailingEnd.toNat + pad.toNat = s.toNat ∧
      trailingEnd + pad = s) := by
  let ⟨k, hkLt, hAlEq⟩ := (isPowerOfTwo64_iff align).mp hPow
  have hAlNat : align.toNat = 2 ^ k := by
    rw [hAlEq, bv64_toNat_ofNat, Nat.mod_eq_of_lt (pow2_lt_64 hkLt)]
  have hAlPos : 0 < align.toNat := by rw [hAlNat]; exact Nat.two_pow_pos k
  let mt := maxTrailingBytes_spec sizeBase align phase Spec.usizeMax64 hPow hPh
  have hMax64Nat : Spec.usizeMax64.toNat = Spec.usizeMaxNat := by decide
  have hMulComm : elems.toNat * elemSize.toNat = elemSize.toNat * elems.toNat :=
    Nat.mul_comm _ _
  have hMulBvComm :
      Spec.bv64Mul elemSize elems = Spec.bv64Mul elems elemSize := by
    apply bv64_eq_of_toNat_eq
    unfold Spec.bv64Mul
    rw [hMulComm]
  cases Nat.lt_or_ge Spec.usizeMaxNat (elems.toNat * elemSize.toNat) with
  | inl hMulOv =>
    have hMulOv' : Spec.usizeMaxNat < elemSize.toNat * elems.toNat := by
      rw [← hMulComm]; exact hMulOv
    have hKaniNone :
        Spec.sizeForElemsKaniSpec64 sizeBase elemSize align phase elems =
          none := by
      unfold Spec.sizeForElemsKaniSpec64
      rw [checkedMul64_none_of_gt elems elemSize hMulOv]
    have hImplNone :
        Spec.sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
          none := by
      unfold Spec.sizeForElemsImpl64
      cases hMt : Spec.maxTrailingBytesImpl64 sizeBase align phase
          Spec.usizeMax64 with
      | none => rfl
      | some _ =>
        dsimp only
        rw [checkedMul64_none_of_gt elemSize elems hMulOv']
    rw [hImplNone, hKaniNone]
    refine ⟨rfl, ⟨(fun h => by let ⟨_, hs⟩ := h; cases hs),
        (fun h => False.elim (Nat.not_lt_of_ge h.1 hMulOv))⟩,
      (fun _ h => by cases h),
      (fun _ _ _ hCm => by
        rw [checkedMul64_none_of_gt elems elemSize hMulOv] at hCm
        cases hCm)⟩
  | inr hMulFit =>
    have hMulFit' : elemSize.toNat * elems.toNat ≤ Spec.usizeMaxNat := by
      rw [← hMulComm]; exact hMulFit
    let cm := checkedMul64_of_le elems elemSize hMulFit
    let cm' := checkedMul64_of_le elemSize elems hMulFit'
    let ts := Spec.bv64Mul elems elemSize
    have hTsNat : ts.toNat = elems.toNat * elemSize.toNat := cm.2
    let sd :=
      sliceDstSizeForTrailingBytes64_iff sizeBase align phase ts hPow hPh
    have hKaniEqSd :
        Spec.sizeForElemsKaniSpec64 sizeBase elemSize align phase elems =
          Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts := by
      unfold Spec.sizeForElemsKaniSpec64
      rw [cm.1]
    have hObjMono :
        Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat ts.toNat ≤
          Spec.usizeMaxNat →
        Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat 0 ≤
          Spec.usizeMaxNat := by
      intro hObjLe
      have hRuMono :
          Spec.roundUpNat (phase.toNat + 0) align.toNat ≤
            Spec.roundUpNat (phase.toNat + ts.toNat) align.toNat := by
        apply (roundUpNat_le_iff_of_dvd hAlPos (roundUpNat_dvd _ hAlPos).1).mpr
        rw [Nat.add_zero]
        exact Nat.le_trans (Nat.le_add_right _ _) (roundUpNat_dvd _ hAlPos).2
      exact Nat.le_trans (Nat.add_le_add_left hRuMono _) hObjLe
    have hObjCond :
        (Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat ts.toNat ≤
          Spec.usizeMaxNat) ↔
        ∃ maxTb,
          Spec.maxTrailingBytesImpl64 sizeBase align phase Spec.usizeMax64 =
            some maxTb ∧
          ts.toNat ≤ maxTb.toNat := by
      constructor
      · intro hObjLe
        have hObj0 :
            Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat 0 ≤
              Spec.usizeMax64.toNat := by
          rw [hMax64Nat]; exact hObjMono hObjLe
        let ⟨maxTb, hMt⟩ := mt.2.1.mpr hObj0
        refine ⟨maxTb, hMt, ?_⟩
        rw [← (mt.2.2 maxTb hMt).2 ts.toNat, hMax64Nat]
        exact hObjLe
      · intro ⟨maxTb, hMt, hLeTb⟩
        rw [← hMax64Nat, (mt.2.2 maxTb hMt).2 ts.toNat]
        exact hLeTb
    have hPadIdent :
        (offset + ts) +
          Spec.paddingForElemsFast sizeBase offset elemSize align phase elems =
        sizeBase +
          ((phase + ts) + Spec.paddingNeededFor64 (phase + ts) align) := by
      rw [(padding_for_elems_equiv sizeBase offset elemSize align phase
        elems hPow hPh).1]
      unfold Spec.paddingForElemsNaive
      dsimp only
      change (offset + ts) +
          ((sizeBase + Spec.roundDown64
            ((phase + ts) + (align - BitVec.ofNat 64 1)) align) -
            (offset + ts)) = _
      rw [bv64_sub_add_cancel_self (offset + ts) _,
        bv64_roundUp_eq_add_pad (phase + ts) align hPow]
    cases Nat.lt_or_ge Spec.usizeMaxNat
        (Spec.objectSizeNat sizeBase.toNat align.toNat phase.toNat
          ts.toNat) with
    | inl hObjOv =>
      have hKaniNone :
          Spec.sizeForElemsKaniSpec64 sizeBase elemSize align phase elems =
            none := by
        rw [hKaniEqSd]
        cases hSd :
            Spec.sliceDstSizeForTrailingBytes64 sizeBase align phase ts with
        | none => rfl
        | some s =>
          have hLe := sd.1.mp ⟨s, hSd⟩
          exact False.elim (Nat.not_lt_of_ge hLe hObjOv)
      have hImplNone :
          Spec.sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
            none := by
        unfold Spec.sizeForElemsImpl64
        cases hMt : Spec.maxTrailingBytesImpl64 sizeBase align phase
            Spec.usizeMax64 with
        | none => rfl
        | some maxTb =>
          dsimp only
          rw [cm'.1]
          dsimp only
          have hGt : maxTb.toNat < (Spec.bv64Mul elemSize elems).toNat := by
            rw [hMulBvComm]
            cases Nat.lt_or_ge maxTb.toNat ts.toNat with
            | inl h => exact h
            | inr hLe =>
              have hOk := hObjCond.mpr ⟨maxTb, hMt, hLe⟩
              exact False.elim (Nat.not_lt_of_ge hOk hObjOv)
          rw [ite_prop_true hGt]
      rw [hImplNone, hKaniNone]
      refine ⟨rfl, ⟨(fun h => by let ⟨_, hs⟩ := h; cases hs),
          (fun h => False.elim (Nat.not_lt_of_ge h.2
            (by rw [← hTsNat]; exact hObjOv)))⟩,
        (fun _ h => by cases h),
        (fun _ _ _ _ _ hIm => by cases hIm)⟩
    | inr hObjFit =>
      let ⟨s, hSdSome⟩ := sd.1.mpr hObjFit
      let sEq := sd.2 s hSdSome
      let ⟨maxTb, hMtSome, hTsLeMax⟩ := hObjCond.mp hObjFit
      have hImplSome :
          Spec.sizeForElemsImpl64 sizeBase offset elemSize align phase elems =
            some s := by
        unfold Spec.sizeForElemsImpl64
        rw [hMtSome]
        dsimp only
        rw [cm'.1]
        dsimp only
        have hNotGt :
            ¬ (maxTb.toNat < (Spec.bv64Mul elemSize elems).toNat) := by
          rw [hMulBvComm]
          exact Nat.not_lt_of_ge hTsLeMax
        rw [ite_prop_false hNotGt, hMulBvComm, hPadIdent, ← sEq.2]
      have hKaniSome :
          Spec.sizeForElemsKaniSpec64 sizeBase elemSize align phase elems =
            some s := by
        rw [hKaniEqSd, hSdSome]
      rw [hImplSome, hKaniSome]
      refine ⟨rfl, ⟨fun _ => ⟨hMulFit, by rw [← hTsNat]; exact hObjFit⟩,
          fun _ => ⟨s, rfl⟩⟩, ?_, ?_⟩
      · intro s' hs'
        injection hs' with hEq
        subst hEq
        rw [← hTsNat]
        exact sEq.1
      · intro trailingSize trailingEnd s' hCm hCa hIm hLeEnd
        injection hIm with hsEq
        subst hsEq
        rw [cm.1] at hCm
        injection hCm with hTsEq
        subst hTsEq
        cases Nat.lt_or_ge Spec.usizeMaxNat (offset.toNat + ts.toNat) with
        | inl hEndOv =>
          rw [checkedAdd64_none_of_gt offset ts hEndOv] at hCa
          cases hCa
        | inr hEndFit =>
          let ca := checkedAdd64_of_le offset ts hEndFit
          rw [ca.1] at hCa
          injection hCa with hEndEq
          subst hEndEq
          have hAddPadEq : (offset + ts) +
              Spec.paddingForElemsFast sizeBase offset elemSize align
                phase elems = s := by
            rw [hPadIdent, ← sEq.2]
          have hPadEq :
              Spec.paddingForElemsFast sizeBase offset elemSize align
                phase elems = s - (offset + ts) := by
            let x :=
              Spec.paddingForElemsFast sizeBase offset elemSize align
                phase elems
            have hX : (offset + ts) + x = s := hAddPadEq
            have hSub := congrArg (fun z => z - (offset + ts)) hX
            rw [bv64_sub_eq_add_neg ((offset + ts) + x), ← bv64_add_assoc,
              bv64_neg_add_self, bv64_zero_add] at hSub
            exact hSub
          have hLeNat : (offset + ts).toNat ≤ s.toNat := hLeEnd
          have hPadNat :
              (Spec.paddingForElemsFast sizeBase offset elemSize align
                phase elems).toNat = s.toNat - (offset + ts).toNat := by
            rw [hPadEq]
            exact bv64_toNat_sub_of_le hLeNat
          refine ⟨hTsNat.symm, (by rw [hTsNat]; exact hMulFit), ca.2.symm,
            (by rw [ca.2]; exact hEndFit), ?_, hAddPadEq⟩
          rw [hPadNat]
          exact Nat.add_sub_of_le hLeNat

private theorem dst_layout_spec : Spec.DstLayoutSpec :=
  ⟨⟨rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩,
    isPowerOfTwo64_iff,
    rounding_new_roundtrip,
    rounding_components_kani,
    sizeOffset64_spec,
    paddingNeededFor64_spec,
    roundDown64_spec,
    padding_for_elems_equiv,
    maxTrailingBytes_spec,
    size_for_elems_spec⟩

/-! ## Top-Level Proof-Unit Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, bodies_unique_identities, ?_, ?_⟩
  · intro defId body found
    have hSub := bodiesVerified_getElem defId body all_bodies_verified found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨⟨rfl, ?_⟩, dst_layout_spec⟩
    intro defId identity found
    have hSub := allMarkersAt_getElem defId identity all_markers_at found
    rw [Nat.zero_add] at hSub
    exact hSub

end Proof
