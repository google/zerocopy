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

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Part 1: Captured 90-Body Monomorphized MIR Verification -/

private theorem total_of_executes {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_exec :
      Executes body
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

private theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
    Spec.ReturnsTotal Captured.program defId args ret :=
  total_of_executes h_body h_adm h_args (run_executes h_runs)

private theorem zero_arg_body_at {defId : DefId} {body : Body}
    {identity : String} {expectedUnsafe : Bool}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_id : body.identity = identity)
    (h_unsafe : body.isUnsafe = expectedUnsafe)
    (h_argc : body.argumentCount = 0)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [])
    (h_args : ValidEntryArgs body [])
    (h_runs : Runs body 2 [] .unit)
    (h_step1 : ∀ mem : MemoryState,
      evalStep Captured.program 0
        { frames := [⟨defId, 0, 0, [.immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .step
        { frames := [⟨defId, 0, 1, [.immediate (some .unit)],
            none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ mem : MemoryState,
      evalStep Captured.program 0
        { frames := [⟨defId, 0, 1, [.immediate (some .unit)],
            none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨.unit, ⟨[]⟩⟩)) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.ZeroArgUnitBodyAt Captured.program defId identity expectedUnsafe := by
  refine ⟨?_, ⟨body, h_body, h_id, h_unsafe, h_argc,
    total_of_runs h_body h_adm h_args h_runs, fun mem =>
      ⟨{ frames := [⟨defId, 0, 1, [.immediate (some .unit)],
          none, none, none⟩],
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

private theorem writePlace_slot0_of_checkVal {ty : MirTy} {v : Val}
    (mem : MemoryState) (hv : checkVal v ty = true) :
    writePlace [.immediate none, .immediate none] mem 0 ty v =
      .ok ([.immediate (some v), .immediate none], mem) := by
  unfold writePlace
  rw [hv]
  rfl

private theorem move_step1_of_checkVal {defId : DefId}
    {ty : MirTy} {v : Val}
    (h_eval : ∀ mem : MemoryState,
      evalStep Captured.program 0
        { frames := [⟨defId, 0, 0,
            [.immediate none, .immediate (some v)], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      match writePlace [.immediate none, .immediate none] mem 0 ty v with
      | .error k => .fault k
      | .ok (l2, m2) =>
        .step
          { frames := [⟨defId, 0, 1, l2, none, none, none⟩],
            callerMem := ⟨[]⟩, mem := m2 })
    (hv : checkVal v ty = true) (mem : MemoryState) :
    evalStep Captured.program 0
      { frames := [⟨defId, 0, 0,
          [.immediate none, .immediate (some v)], none, none, none⟩],
        callerMem := ⟨[]⟩, mem := mem } =
    .step
      { frames := [⟨defId, 0, 1,
          [.immediate (some v), .immediate none], none, none, none⟩],
        callerMem := ⟨[]⟩, mem := mem } := by
  rw [h_eval mem, writePlace_slot0_of_checkVal mem hv]

private theorem move_body_executes {body : Body} {ty : MirTy} {v : Val}
    (h_loc : initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v)])
    (h_step1 :
      evalStep (bodyProg body) 0
        (mkState 0 0 [.immediate none, .immediate (some v)]) =
      match writePlace [.immediate none, .immediate none]
          entryMemory 0 ty v with
      | .error k => .fault k
      | .ok (l2, m2) =>
        .step
          { frames := [⟨0, 0, 1, l2, none, none, none⟩],
            callerMem := ⟨[]⟩, mem := m2 })
    (h_step2 :
      evalStep (bodyProg body) 0
        (mkState 0 1 [.immediate (some v), .immediate none]) =
      .done (.returned ⟨v, ⟨[]⟩⟩))
    (hv : checkVal v ty = true) :
    Executes body
      (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) v := by
  refine .next ?_ (.ret h_step2)
  rw [h_loc, h_step1, writePlace_slot0_of_checkVal entryMemory hv]
  rfl

private theorem unary_move_identity_verified {α : Type}
    {defId : DefId} {body : Body} {identity : String} {ty : MirTy}
    {encode : α → Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_id : body.identity = identity)
    (h_safe : body.isUnsafe = false)
    (h_argc : body.argumentCount = 1)
    (h_locals : body.locals = [ty, ty])
    (h_encode_ok : ∀ x : α, checkVal (encode x) ty = true)
    (h_step1 : ∀ (v : Val), checkVal v ty = true → ∀ (mem : MemoryState),
      evalStep Captured.program 0
        { frames := [⟨defId, 0, 0,
            [.immediate none, .immediate (some v)], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .step
        { frames := [⟨defId, 0, 1,
            [.immediate (some v), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ (v : Val) (mem : MemoryState),
      evalStep Captured.program 0
        { frames := [⟨defId, 0, 1,
            [.immediate (some v), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨v, ⟨[]⟩⟩))
    (h_body_exec : ∀ {v : Val}, checkVal v ty = true →
      Executes body
        (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) v) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.UnaryMoveIdentityAt Captured.program defId identity ty encode := by
  have h_tys : (body.locals.drop 1).take body.argumentCount = [ty] := by
    rw [h_locals, h_argc]
    rfl
  refine ⟨?_, ⟨body, h_body, h_id, h_safe, h_argc, h_locals, fun x => ?_⟩⟩
  · refine bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_)
    have hMatch : checkArgsMatch args [ty] = true := by
      unfold ValidEntryArgs at valid
      rw [h_tys] at valid
      exact valid
    let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
    have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
    subst hEq; subst hNil
    exact executes_safe (h_body_exec hv)
  · have hv : checkVal (encode x) ty = true := h_encode_ok x
    have hArgs : ValidEntryArgs body [encode x] := by
      unfold ValidEntryArgs
      rw [h_tys]
      exact checkArgsMatch_cons_iff.mpr ⟨encode x, [], rfl, hv, rfl⟩
    refine ⟨total_of_executes h_body h_adm hArgs (h_body_exec hv), fun mem =>
      ⟨{ frames := [⟨defId, 0, 1,
           [.immediate (some (encode x)), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem },
       ⟨0, rfl, h_step1 (encode x) hv mem⟩,
       rfl,
       ⟨0, rfl, h_step2 (encode x) mem⟩⟩⟩

private theorem bool_valid (b : Bool) : checkVal (.bool b) .bool = true := by
  cases b <;> rfl

private theorem u8_valid (n : BitVec 8) :
    checkVal (Spec.u8Val n) (.int .i8 false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .i8
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

private theorem u32_valid (n : BitVec 32) :
    checkVal (Spec.u32Val n) (.int .i32 false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .i32
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

private theorem usize_valid (n : BitVec 64) :
    checkVal (Spec.usizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

private theorem unary_move_bool_at {identity : String}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies 70 =
        some Captured.body_70)
    (h_adm : BodyStaticAdmitted Captured.program Captured.body_70 = true)
    (h_id : Captured.body_70.identity = identity)
    (h_safe : Captured.body_70.isUnsafe = false)
    (h_argc : Captured.body_70.argumentCount = 1)
    (h_locals : Captured.body_70.locals = [.bool, .bool])
    (h_step1 : ∀ (v : Val), checkVal v .bool = true → ∀ (mem : MemoryState),
      evalStep Captured.program 0
        { frames := [⟨70, 0, 0,
            [.immediate none, .immediate (some v)], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .step
        { frames := [⟨70, 0, 1,
            [.immediate (some v), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ (v : Val) (mem : MemoryState),
      evalStep Captured.program 0
        { frames := [⟨70, 0, 1,
            [.immediate (some v), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨v, ⟨[]⟩⟩)) :
    BodyVerified Captured.program 70 Captured.body_70
      (Spec.specs.safety Captured.body_70.identity) ∧
    Spec.UnaryMoveIdentityAt Captured.program 70 identity .bool Val.bool :=
  unary_move_identity_verified h_body h_adm h_id h_safe h_argc h_locals
    bool_valid h_step1 h_step2
    (fun hv => move_body_executes rfl rfl rfl hv)

private theorem unary_move_u32_at {identity : String}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies 71 =
        some Captured.body_71)
    (h_adm : BodyStaticAdmitted Captured.program Captured.body_71 = true)
    (h_id : Captured.body_71.identity = identity)
    (h_safe : Captured.body_71.isUnsafe = false)
    (h_argc : Captured.body_71.argumentCount = 1)
    (h_locals :
      Captured.body_71.locals = [.int .i32 false, .int .i32 false])
    (h_step1 :
      ∀ (v : Val), checkVal v (.int .i32 false) = true → ∀ (mem : MemoryState),
        evalStep Captured.program 0
          { frames := [⟨71, 0, 0,
              [.immediate none, .immediate (some v)], none, none, none⟩],
            callerMem := ⟨[]⟩, mem := mem } =
        .step
          { frames := [⟨71, 0, 1,
              [.immediate (some v), .immediate none], none, none, none⟩],
            callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ (v : Val) (mem : MemoryState),
      evalStep Captured.program 0
        { frames := [⟨71, 0, 1,
            [.immediate (some v), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨v, ⟨[]⟩⟩)) :
    BodyVerified Captured.program 71 Captured.body_71
      (Spec.specs.safety Captured.body_71.identity) ∧
    Spec.UnaryMoveIdentityAt Captured.program 71 identity
      (.int .i32 false) Spec.u32Val :=
  unary_move_identity_verified h_body h_adm h_id h_safe h_argc h_locals
    u32_valid h_step1 h_step2
    (fun hv => move_body_executes rfl rfl rfl hv)

private theorem unary_move_u8_at {identity : String}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies 72 =
        some Captured.body_72)
    (h_adm : BodyStaticAdmitted Captured.program Captured.body_72 = true)
    (h_id : Captured.body_72.identity = identity)
    (h_safe : Captured.body_72.isUnsafe = false)
    (h_argc : Captured.body_72.argumentCount = 1)
    (h_locals :
      Captured.body_72.locals = [.int .i8 false, .int .i8 false])
    (h_step1 :
      ∀ (v : Val), checkVal v (.int .i8 false) = true → ∀ (mem : MemoryState),
        evalStep Captured.program 0
          { frames := [⟨72, 0, 0,
              [.immediate none, .immediate (some v)], none, none, none⟩],
            callerMem := ⟨[]⟩, mem := mem } =
        .step
          { frames := [⟨72, 0, 1,
              [.immediate (some v), .immediate none], none, none, none⟩],
            callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ (v : Val) (mem : MemoryState),
      evalStep Captured.program 0
        { frames := [⟨72, 0, 1,
            [.immediate (some v), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨v, ⟨[]⟩⟩)) :
    BodyVerified Captured.program 72 Captured.body_72
      (Spec.specs.safety Captured.body_72.identity) ∧
    Spec.UnaryMoveIdentityAt Captured.program 72 identity
      (.int .i8 false) Spec.u8Val :=
  unary_move_identity_verified h_body h_adm h_id h_safe h_argc h_locals
    u8_valid h_step1 h_step2
    (fun hv => move_body_executes rfl rfl rfl hv)

private theorem unary_move_usize_at {identity : String}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies 73 =
        some Captured.body_73)
    (h_adm : BodyStaticAdmitted Captured.program Captured.body_73 = true)
    (h_id : Captured.body_73.identity = identity)
    (h_safe : Captured.body_73.isUnsafe = false)
    (h_argc : Captured.body_73.argumentCount = 1)
    (h_locals :
      Captured.body_73.locals = [.int .isize false, .int .isize false])
    (h_step1 :
      ∀ (v : Val), checkVal v (.int .isize false) = true →
        ∀ (mem : MemoryState),
        evalStep Captured.program 0
          { frames := [⟨73, 0, 0,
              [.immediate none, .immediate (some v)], none, none, none⟩],
            callerMem := ⟨[]⟩, mem := mem } =
        .step
          { frames := [⟨73, 0, 1,
              [.immediate (some v), .immediate none], none, none, none⟩],
            callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ (v : Val) (mem : MemoryState),
      evalStep Captured.program 0
        { frames := [⟨73, 0, 1,
            [.immediate (some v), .immediate none], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨v, ⟨[]⟩⟩)) :
    BodyVerified Captured.program 73 Captured.body_73
      (Spec.specs.safety Captured.body_73.identity) ∧
    Spec.UnaryMoveIdentityAt Captured.program 73 identity
      (.int .isize false) Spec.usizeVal :=
  unary_move_identity_verified h_body h_adm h_id h_safe h_argc h_locals
    usize_valid h_step1 h_step2
    (fun hv => move_body_executes rfl rfl rfl hv)

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

private def contractAt : Nat → List Spec.BodyContract → Spec.BodyContract
  | _, [] => Spec.bcSafeMarker ""
  | 0, c :: _ => c
  | n + 1, _ :: rest => contractAt n rest

private theorem m00 :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.BodyContractAt Captured.program 0
      (contractAt 0 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_0, Captured.Shard_000.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m01 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.BodyContractAt Captured.program 1
      (contractAt 1 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_1, Captured.Shard_000.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m02 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.BodyContractAt Captured.program 2
      (contractAt 2 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_2, Captured.Shard_000.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m03 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.BodyContractAt Captured.program 3
      (contractAt 3 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_3, Captured.Shard_000.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m04 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.BodyContractAt Captured.program 4
      (contractAt 4 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_4, Captured.Shard_000.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m05 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.BodyContractAt Captured.program 5
      (contractAt 5 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_5, Captured.Shard_000.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m06 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.BodyContractAt Captured.program 6
      (contractAt 6 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_6, Captured.Shard_000.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m07 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.BodyContractAt Captured.program 7
      (contractAt 7 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_7, Captured.Shard_000.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m08 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.BodyContractAt Captured.program 8
      (contractAt 8 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_8, Captured.Shard_000.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m09 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.BodyContractAt Captured.program 9
      (contractAt 9 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_9, Captured.Shard_000.body_9,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.BodyContractAt Captured.program 10
      (contractAt 10 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_10, Captured.Shard_001.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.BodyContractAt Captured.program 11
      (contractAt 11 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_11, Captured.Shard_001.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.BodyContractAt Captured.program 12
      (contractAt 12 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_12, Captured.Shard_001.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.BodyContractAt Captured.program 13
      (contractAt 13 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_13, Captured.Shard_001.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.BodyContractAt Captured.program 14
      (contractAt 14 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_14, Captured.Shard_001.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.BodyContractAt Captured.program 15
      (contractAt 15 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_15, Captured.Shard_001.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.BodyContractAt Captured.program 16
      (contractAt 16 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_16, Captured.Shard_001.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.BodyContractAt Captured.program 17
      (contractAt 17 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_17, Captured.Shard_001.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.BodyContractAt Captured.program 18
      (contractAt 18 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_18, Captured.Shard_001.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.BodyContractAt Captured.program 19
      (contractAt 19 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_19, Captured.Shard_002.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.BodyContractAt Captured.program 20
      (contractAt 20 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_20, Captured.Shard_002.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.BodyContractAt Captured.program 21
      (contractAt 21 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_21, Captured.Shard_002.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.BodyContractAt Captured.program 22
      (contractAt 22 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_22, Captured.Shard_002.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.BodyContractAt Captured.program 23
      (contractAt 23 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_23, Captured.Shard_002.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.BodyContractAt Captured.program 24
      (contractAt 24 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_24, Captured.Shard_002.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.BodyContractAt Captured.program 25
      (contractAt 25 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_25, Captured.Shard_002.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.BodyContractAt Captured.program 26
      (contractAt 26 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_26, Captured.Shard_002.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.BodyContractAt Captured.program 27
      (contractAt 27 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_27, Captured.Shard_002.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.BodyContractAt Captured.program 28
      (contractAt 28 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_28, Captured.Shard_003.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.BodyContractAt Captured.program 29
      (contractAt 29 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_29, Captured.Shard_003.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.BodyContractAt Captured.program 30
      (contractAt 30 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_30, Captured.Shard_003.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.BodyContractAt Captured.program 31
      (contractAt 31 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_31, Captured.Shard_003.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.BodyContractAt Captured.program 32
      (contractAt 32 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_32, Captured.Shard_003.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.BodyContractAt Captured.program 33
      (contractAt 33 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_33, Captured.Shard_003.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.BodyContractAt Captured.program 34
      (contractAt 34 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_34, Captured.Shard_003.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.BodyContractAt Captured.program 35
      (contractAt 35 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_35, Captured.Shard_003.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.BodyContractAt Captured.program 36
      (contractAt 36 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_36, Captured.Shard_003.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.BodyContractAt Captured.program 37
      (contractAt 37 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_37, Captured.Shard_004.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.BodyContractAt Captured.program 38
      (contractAt 38 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_38, Captured.Shard_004.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.BodyContractAt Captured.program 39
      (contractAt 39 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_39, Captured.Shard_004.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.BodyContractAt Captured.program 40
      (contractAt 40 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_40, Captured.Shard_004.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m41 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.BodyContractAt Captured.program 41
      (contractAt 41 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_41, Captured.Shard_004.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m42 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.BodyContractAt Captured.program 42
      (contractAt 42 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_42, Captured.Shard_004.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m43 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.BodyContractAt Captured.program 43
      (contractAt 43 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_43, Captured.Shard_004.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m44 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.BodyContractAt Captured.program 44
      (contractAt 44 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_44, Captured.Shard_004.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m45 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.BodyContractAt Captured.program 45
      (contractAt 45 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_45, Captured.Shard_004.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m46 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.BodyContractAt Captured.program 46
      (contractAt 46 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_46, Captured.Shard_005.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m47 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.BodyContractAt Captured.program 47
      (contractAt 47 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_47, Captured.Shard_005.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m48 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.BodyContractAt Captured.program 48
      (contractAt 48 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_48, Captured.Shard_005.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m49 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.BodyContractAt Captured.program 49
      (contractAt 49 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_49, Captured.Shard_005.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m50 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.BodyContractAt Captured.program 50
      (contractAt 50 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_50, Captured.Shard_005.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m51 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.BodyContractAt Captured.program 51
      (contractAt 51 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_51, Captured.Shard_005.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m52 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.BodyContractAt Captured.program 52
      (contractAt 52 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_52, Captured.Shard_005.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m53 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.BodyContractAt Captured.program 53
      (contractAt 53 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_53, Captured.Shard_005.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m54 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.BodyContractAt Captured.program 54
      (contractAt 54 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_54, Captured.Shard_005.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m55 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.BodyContractAt Captured.program 55
      (contractAt 55 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_55, Captured.Shard_006.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m56 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.BodyContractAt Captured.program 56
      (contractAt 56 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_56, Captured.Shard_006.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m57 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.BodyContractAt Captured.program 57
      (contractAt 57 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_57, Captured.Shard_006.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m58 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.BodyContractAt Captured.program 58
      (contractAt 58 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_58, Captured.Shard_006.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m59 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.BodyContractAt Captured.program 59
      (contractAt 59 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_59, Captured.Shard_006.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m60 :
    BodyVerified Captured.program 60 Captured.body_60
      (Spec.specs.safety Captured.body_60.identity) ∧
    Spec.BodyContractAt Captured.program 60
      (contractAt 60 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_60, Captured.Shard_006.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m61 :
    BodyVerified Captured.program 61 Captured.body_61
      (Spec.specs.safety Captured.body_61.identity) ∧
    Spec.BodyContractAt Captured.program 61
      (contractAt 61 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_61, Captured.Shard_006.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m62 :
    BodyVerified Captured.program 62 Captured.body_62
      (Spec.specs.safety Captured.body_62.identity) ∧
    Spec.BodyContractAt Captured.program 62
      (contractAt 62 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_62, Captured.Shard_006.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m63 :
    BodyVerified Captured.program 63 Captured.body_63
      (Spec.specs.safety Captured.body_63.identity) ∧
    Spec.BodyContractAt Captured.program 63
      (contractAt 63 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_63, Captured.Shard_006.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m64 :
    BodyVerified Captured.program 64 Captured.body_64
      (Spec.specs.safety Captured.body_64.identity) ∧
    Spec.BodyContractAt Captured.program 64
      (contractAt 64 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_64, Captured.Shard_007.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m65 :
    BodyVerified Captured.program 65 Captured.body_65
      (Spec.specs.safety Captured.body_65.identity) ∧
    Spec.BodyContractAt Captured.program 65
      (contractAt 65 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_65, Captured.Shard_007.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m66 :
    BodyVerified Captured.program 66 Captured.body_66
      (Spec.specs.safety Captured.body_66.identity) ∧
    Spec.BodyContractAt Captured.program 66
      (contractAt 66 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_66, Captured.Shard_007.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m67 :
    BodyVerified Captured.program 67 Captured.body_67
      (Spec.specs.safety Captured.body_67.identity) ∧
    Spec.BodyContractAt Captured.program 67
      (contractAt 67 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_67, Captured.Shard_007.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m68 :
    BodyVerified Captured.program 68 Captured.body_68
      (Spec.specs.safety Captured.body_68.identity) ∧
    Spec.BodyContractAt Captured.program 68
      (contractAt 68 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_68, Captured.Shard_007.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m69 :
    BodyVerified Captured.program 69 Captured.body_69
      (Spec.specs.safety Captured.body_69.identity) ∧
    Spec.BodyContractAt Captured.program 69
      (contractAt 69 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_69, Captured.Shard_007.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m70 :
    BodyVerified Captured.program 70 Captured.body_70
      (Spec.specs.safety Captured.body_70.identity) ∧
    Spec.BodyContractAt Captured.program 70
      (contractAt 70 Spec.genericUnitCatalog) :=
  unary_move_bool_at rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_70, Captured.Shard_007.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl
    (fun v hv mem =>
      move_step1_of_checkVal (defId := 70) (fun _ => rfl) hv mem)
    (fun v mem => rfl)

private theorem m71 :
    BodyVerified Captured.program 71 Captured.body_71
      (Spec.specs.safety Captured.body_71.identity) ∧
    Spec.BodyContractAt Captured.program 71
      (contractAt 71 Spec.genericUnitCatalog) :=
  unary_move_u32_at rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_71, Captured.Shard_007.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl
    (fun v hv mem =>
      move_step1_of_checkVal (defId := 71) (fun _ => rfl) hv mem)
    (fun v mem => rfl)

private theorem m72 :
    BodyVerified Captured.program 72 Captured.body_72
      (Spec.specs.safety Captured.body_72.identity) ∧
    Spec.BodyContractAt Captured.program 72
      (contractAt 72 Spec.genericUnitCatalog) :=
  unary_move_u8_at rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_72, Captured.Shard_007.body_8,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl
    (fun v hv mem =>
      move_step1_of_checkVal (defId := 72) (fun _ => rfl) hv mem)
    (fun v mem => rfl)

private theorem m73 :
    BodyVerified Captured.program 73 Captured.body_73
      (Spec.specs.safety Captured.body_73.identity) ∧
    Spec.BodyContractAt Captured.program 73
      (contractAt 73 Spec.genericUnitCatalog) :=
  unary_move_usize_at rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_73, Captured.Shard_007.body_9,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl
    (fun v hv mem =>
      move_step1_of_checkVal (defId := 73) (fun _ => rfl) hv mem)
    (fun v mem => rfl)

private theorem m74 :
    BodyVerified Captured.program 74 Captured.body_74
      (Spec.specs.safety Captured.body_74.identity) ∧
    Spec.BodyContractAt Captured.program 74
      (contractAt 74 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := true) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_74, Captured.Shard_007.body_10,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m75 :
    BodyVerified Captured.program 75 Captured.body_75
      (Spec.specs.safety Captured.body_75.identity) ∧
    Spec.BodyContractAt Captured.program 75
      (contractAt 75 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_75, Captured.Shard_008.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m76 :
    BodyVerified Captured.program 76 Captured.body_76
      (Spec.specs.safety Captured.body_76.identity) ∧
    Spec.BodyContractAt Captured.program 76
      (contractAt 76 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_76, Captured.Shard_008.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m77 :
    BodyVerified Captured.program 77 Captured.body_77
      (Spec.specs.safety Captured.body_77.identity) ∧
    Spec.BodyContractAt Captured.program 77
      (contractAt 77 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_77, Captured.Shard_008.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m78 :
    BodyVerified Captured.program 78 Captured.body_78
      (Spec.specs.safety Captured.body_78.identity) ∧
    Spec.BodyContractAt Captured.program 78
      (contractAt 78 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_78, Captured.Shard_008.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m79 :
    BodyVerified Captured.program 79 Captured.body_79
      (Spec.specs.safety Captured.body_79.identity) ∧
    Spec.BodyContractAt Captured.program 79
      (contractAt 79 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_79, Captured.Shard_008.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m80 :
    BodyVerified Captured.program 80 Captured.body_80
      (Spec.specs.safety Captured.body_80.identity) ∧
    Spec.BodyContractAt Captured.program 80
      (contractAt 80 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_80, Captured.Shard_008.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m81 :
    BodyVerified Captured.program 81 Captured.body_81
      (Spec.specs.safety Captured.body_81.identity) ∧
    Spec.BodyContractAt Captured.program 81
      (contractAt 81 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_81, Captured.Shard_008.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m82 :
    BodyVerified Captured.program 82 Captured.body_82
      (Spec.specs.safety Captured.body_82.identity) ∧
    Spec.BodyContractAt Captured.program 82
      (contractAt 82 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_82, Captured.Shard_008.body_7,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m83 :
    BodyVerified Captured.program 83 Captured.body_83
      (Spec.specs.safety Captured.body_83.identity) ∧
    Spec.BodyContractAt Captured.program 83
      (contractAt 83 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_83, Captured.Shard_009.body_0,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m84 :
    BodyVerified Captured.program 84 Captured.body_84
      (Spec.specs.safety Captured.body_84.identity) ∧
    Spec.BodyContractAt Captured.program 84
      (contractAt 84 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_84, Captured.Shard_009.body_1,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m85 :
    BodyVerified Captured.program 85 Captured.body_85
      (Spec.specs.safety Captured.body_85.identity) ∧
    Spec.BodyContractAt Captured.program 85
      (contractAt 85 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_85, Captured.Shard_009.body_2,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m86 :
    BodyVerified Captured.program 86 Captured.body_86
      (Spec.specs.safety Captured.body_86.identity) ∧
    Spec.BodyContractAt Captured.program 86
      (contractAt 86 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_86, Captured.Shard_009.body_3,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m87 :
    BodyVerified Captured.program 87 Captured.body_87
      (Spec.specs.safety Captured.body_87.identity) ∧
    Spec.BodyContractAt Captured.program 87
      (contractAt 87 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_87, Captured.Shard_009.body_4,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m88 :
    BodyVerified Captured.program 88 Captured.body_88
      (Spec.specs.safety Captured.body_88.identity) ∧
    Spec.BodyContractAt Captured.program 88
      (contractAt 88 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_88, Captured.Shard_009.body_5,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m89 :
    BodyVerified Captured.program 89 Captured.body_89
      (Spec.specs.safety Captured.body_89.identity) ∧
    Spec.BodyContractAt Captured.program 89
      (contractAt 89 Spec.genericUnitCatalog) :=
  zero_arg_body_at (expectedUnsafe := false) rfl rfl
    (by
      dsimp only [Spec.genericUnitCatalog, contractAt,
        Spec.bcUnsafeFence, Spec.bcSafeMarker, Spec.bcMustUseBool,
        Spec.bcMustUseU32, Spec.bcMustUseU8, Spec.bcMustUseUsize]
      simp only [Captured.body_89, Captured.Shard_009.body_6,
        stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem all_bodies_verified :
    BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
  ⟨
     m00.1, m01.1, m02.1, m03.1, m04.1, m05.1, m06.1, m07.1, m08.1, m09.1,
     m10.1, m11.1, m12.1, m13.1, m14.1, m15.1, m16.1, m17.1, m18.1, m19.1,
     m20.1, m21.1, m22.1, m23.1, m24.1, m25.1, m26.1, m27.1, m28.1, m29.1,
     m30.1, m31.1, m32.1, m33.1, m34.1, m35.1, m36.1, m37.1, m38.1, m39.1,
     m40.1, m41.1, m42.1, m43.1, m44.1, m45.1, m46.1, m47.1, m48.1, m49.1,
     m50.1, m51.1, m52.1, m53.1, m54.1, m55.1, m56.1, m57.1, m58.1, m59.1,
     m60.1, m61.1, m62.1, m63.1, m64.1, m65.1, m66.1, m67.1, m68.1, m69.1,
     m70.1, m71.1, m72.1, m73.1, m74.1, m75.1, m76.1, m77.1, m78.1, m79.1,
     m80.1, m81.1, m82.1, m83.1, m84.1, m85.1, m86.1, m87.1, m88.1, m89.1,
     True.intro
  ⟩

private noncomputable def AllContractsAt (program : Program) (startIdx : Nat)
    (catalog : List Spec.BodyContract) : Prop :=
  catalog.foldr
    (fun c ih curIdx =>
      Spec.BodyContractAt program curIdx c ∧ ih (curIdx + 1))
    (fun _ => True)
    startIdx

private theorem allContractsAt_getElem {p : Program} :
    ∀ {idx : Nat} {cs : List Spec.BodyContract},
      AllContractsAt p idx cs →
      ∀ (k : Nat) (c : Spec.BodyContract),
        Trusted.MirSemantics.getElem? cs k = some c →
        Spec.BodyContractAt p (idx + k) c
  | _, [], _, _, _, hGet => by cases hGet
  | idx, _ :: _, hCs, 0, _, hGet => by
    injection hGet with hEq
    subst hEq
    rw [Nat.add_zero]
    exact hCs.1
  | idx, _ :: _, hCs, k + 1, c, hGet => by
    have hSub := allContractsAt_getElem hCs.2 k c hGet
    have hIdx : idx + 1 + k = idx + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [← hIdx]
    exact hSub

private theorem all_contracts_at :
    AllContractsAt Captured.program 0 Spec.genericUnitCatalog :=
  ⟨
     m00.2, m01.2, m02.2, m03.2, m04.2, m05.2, m06.2, m07.2, m08.2, m09.2,
     m10.2, m11.2, m12.2, m13.2, m14.2, m15.2, m16.2, m17.2, m18.2, m19.2,
     m20.2, m21.2, m22.2, m23.2, m24.2, m25.2, m26.2, m27.2, m28.2, m29.2,
     m30.2, m31.2, m32.2, m33.2, m34.2, m35.2, m36.2, m37.2, m38.2, m39.2,
     m40.2, m41.2, m42.2, m43.2, m44.2, m45.2, m46.2, m47.2, m48.2, m49.2,
     m50.2, m51.2, m52.2, m53.2, m54.2, m55.2, m56.2, m57.2, m58.2, m59.2,
     m60.2, m61.2, m62.2, m63.2, m64.2, m65.2, m66.2, m67.2, m68.2, m69.2,
     m70.2, m71.2, m72.2, m73.2, m74.2, m75.2, m76.2, m77.2, m78.2, m79.2,
     m80.2, m81.2, m82.2, m83.2, m84.2, m85.2, m86.2, m87.2, m88.2, m89.2,
     True.intro
  ⟩

private theorem bodies_unique_identities :
    bodiesHaveUniqueIdentities Captured.program.bodies = true := rfl

/-! ## Part 2: `Trusted.MirSemantics` & `Spec`-Local Wrapper/Array Proofs -/

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

private theorem list_length_append {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | _ :: rest, ys => by
    dsimp only [List.cons_append, List.length_cons]
    rw [list_length_append rest ys, Nat.succ_add]

private theorem list_take_length_of_le {α : Type} :
    ∀ {n : Nat} {xs : List α}, n ≤ xs.length → (xs.take n).length = n
  | 0, _, _ => rfl
  | n + 1, [], h => False.elim (Nat.not_succ_le_zero n h)
  | _ + 1, _ :: _, h =>
    congrArg Nat.succ (list_take_length_of_le (Nat.le_of_succ_le_succ h))

private theorem list_drop_length {α : Type} :
    ∀ (n : Nat) (xs : List α), (xs.drop n).length = xs.length - n
  | 0, xs => (Nat.sub_zero xs.length).symm
  | n + 1, [] => (Nat.zero_sub (n + 1)).symm
  | n + 1, _ :: rest => by
    change (rest.drop n).length = (rest.length + 1) - (n + 1)
    rw [list_drop_length n rest, Nat.succ_sub_succ]

private theorem list_drop_append_exact {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: rest, ys => list_drop_append_exact rest ys

private theorem list_take_append_exact {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: rest, ys => congrArg (List.cons x) (list_take_append_exact rest ys)

private theorem list_drop_append_of_length {α : Type} {xs ys : List α}
    {k : Nat} (h : xs.length = k) : (xs ++ ys).drop k = ys := by
  subst h
  exact list_drop_append_exact xs ys

private theorem list_take_append_of_length {α : Type} {xs ys : List α}
    {k : Nat} (h : xs.length = k) : (xs ++ ys).take k = xs := by
  subst h
  exact list_take_append_exact xs ys

private theorem list_take_append_drop {α : Type} :
    ∀ (n : Nat) (xs : List α), xs.take n ++ xs.drop n = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: rest =>
    congrArg (List.cons x) (list_take_append_drop n rest)

private theorem replicate_add {α : Type} :
    ∀ (m n : Nat) (a : α),
      List.replicate (m + n) a = List.replicate m a ++ List.replicate n a
  | 0, n, a => by rw [Nat.zero_add]; rfl
  | m + 1, n, a => by
    rw [Nat.succ_add]
    exact congrArg (List.cons a) (replicate_add m n a)

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

private theorem initBytes?_append_of_some :
    ∀ {xs ys : List AllocByte} {rx ry : List UInt8},
      initBytes? xs = some rx →
      initBytes? ys = some ry →
      initBytes? (xs ++ ys) = some (rx ++ ry)
  | [], _, _, _, hx, hy => by
    injection hx with hEq
    subst hEq
    exact hy
  | .uninit :: _, _, _, _, hx, _ => by cases hx
  | .init b _ :: rest, ys, _, ry, hx, hy => by
    unfold initBytes? at hx
    cases hRest : initBytes? rest with
    | none => rw [hRest] at hx; cases hx
    | some rs =>
      rw [hRest] at hx
      injection hx with hEq
      subst hEq
      dsimp only [List.cons_append, initBytes?]
      rw [initBytes?_append_of_some hRest hy]

private theorem initBytes?_split :
    ∀ {xs ys : List AllocByte} {raw : List UInt8},
      initBytes? (xs ++ ys) = some raw →
      ∃ (rx ry : List UInt8),
        initBytes? xs = some rx ∧ initBytes? ys = some ry
  | [], ys, raw, h => ⟨[], raw, rfl, h⟩
  | .uninit :: _, _, _, h => by cases h
  | .init b _ :: rest, ys, _, h => by
    dsimp only [List.cons_append, initBytes?] at h
    cases hTail : initBytes? (rest ++ ys) with
    | none => rw [hTail] at h; cases h
    | some rTail =>
      rw [hTail] at h
      let ⟨rx, ry, hx, hy⟩ := initBytes?_split hTail
      refine ⟨b :: rx, ry, ?_, hy⟩
      unfold initBytes?
      rw [hx]

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

private theorem nat_pow_256_pos : ∀ (k : Nat), 0 < Nat.pow 256 k
  | 0 => Nat.zero_lt_one
  | k + 1 => by
    change 0 < Nat.pow 256 k * 256
    exact Nat.mul_pos (nat_pow_256_pos k) (by decide)

private theorem natOfLeBytes_leBytesOfNat :
    ∀ (k m : Nat),
      natOfLeBytes (leBytesOfNat k m) = Nat.mod m (Nat.pow 256 k)
  | 0, m => by
    change 0 = m % 1
    exact (Nat.mod_one m).symm
  | k + 1, m => by
    dsimp only [leBytesOfNat, natOfLeBytes]
    rw [natOfLeBytes_leBytesOfNat k (Nat.div m 256)]
    change (UInt8.ofNat (m % 256)).toNat + 256 * ((m / 256) % Nat.pow 256 k) =
      m % Nat.pow 256 (k + 1)
    have hMod256Lt : m % 256 < 256 := Nat.mod_lt m (by decide)
    have hU8 : (UInt8.ofNat (m % 256)).toNat = m % 256 :=
      Nat.mod_eq_of_lt hMod256Lt
    rw [hU8]
    let p := Nat.pow 256 k
    have hpPos : 0 < p := nat_pow_256_pos k
    let q := m / 256
    have hqModLt : q % p < p := Nat.mod_lt q hpPos
    have hSmall : m % 256 + 256 * (q % p) < 256 * p := by
      have h1 : m % 256 + 256 * (q % p) < 256 + 256 * (q % p) :=
        Nat.add_lt_add_right hMod256Lt (256 * (q % p))
      have h2 : 256 + 256 * (q % p) = 256 * (q % p + 1) := by
        rw [Nat.mul_succ, Nat.add_comm]
      rw [h2] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left 256 hqModLt)
    have hDecomp :
        m = (m % 256 + 256 * (q % p)) + (256 * p) * (q / p) := by
      have hm : m = m % 256 + 256 * q := (Nat.mod_add_div m 256).symm
      have hq : q = q % p + p * (q / p) := (Nat.mod_add_div q p).symm
      calc
        m = m % 256 + 256 * q := hm
        _ = m % 256 + 256 * (q % p + p * (q / p)) :=
              congrArg (fun x => m % 256 + 256 * x) hq
        _ = m % 256 + (256 * (q % p) + 256 * (p * (q / p))) := by
              rw [Nat.mul_add]
        _ = (m % 256 + 256 * (q % p)) + 256 * (p * (q / p)) :=
              (Nat.add_assoc _ _ _).symm
        _ = (m % 256 + 256 * (q % p)) + (256 * p) * (q / p) := by
              rw [Nat.mul_assoc 256 p (q / p)]
    have hPowSucc : Nat.pow 256 (k + 1) = 256 * p := by
      change p * 256 = 256 * p
      exact Nat.mul_comm p 256
    rw [hPowSucc]
    conv => rhs; rw [hDecomp]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSmall]

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

private theorem checkVal_unit_inv {v : Val} (h : checkVal v .unit = true) :
    v = .unit :=
  checkVal_unit_iff.mp h

/-! ### Base Primitive `Bytes` Lemmas -/

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

/-! ### Part 2A: `UnalignMemorySound` -/

private theorem nat_beq_zero_of_pos {n : Nat} (h : 0 < n) :
    Nat.beq n 0 = false := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 h)
  | succ _ => rfl

private theorem isAligned_zero_eq_true (a : Allocation) (off : Nat) :
    isAligned a off 0 = true := by
  unfold isAligned
  have hBle : Nat.ble 0 a.alignLog2 = true :=
    Nat.ble_eq_true_of_le (Nat.zero_le a.alignLog2)
  have hMod : Nat.mod off (Nat.pow 2 0) = 0 := Nat.mod_one off
  rw [hBle, hMod]
  rfl

private theorem unalign_write_read_any
    (alloc : Allocation) (nextId off : Nat) (ty : MirTy)
    (layout : LayoutData) (v : Val) (bs : List AllocByte)
    (hLive : alloc.live = true)
    (hMut : alloc.mutability = .mut)
    (_hLay : layoutOfTy ty = some layout)
    (hPos : 0 < layout.size)
    (_hEnc : encodeVal profileTargetEndian ty v = .ok bs)
    (hBsLen : bs.length = layout.size)
    (hFit : off + layout.size ≤ alloc.bytes.length) :
    let m : MemoryState := { nextAllocId := nextId, allocations := [alloc] }
    let place : MemPlace := ⟨alloc.allocId, off⟩
    ∃ m' : MemoryState,
      writeBytes m place 0 bs = .ok m' ∧
      readBytes m' place layout.size 0 = .ok bs := by
  intro m place
  have hBsPos : 0 < bs.length := by rw [hBsLen]; exact hPos
  have hBsBeq0 : Nat.beq bs.length 0 = false := nat_beq_zero_of_pos hBsPos
  have hSizeBeq0 : Nat.beq layout.size 0 = false := nat_beq_zero_of_pos hPos
  have hIdRefl : Nat.beq alloc.allocId alloc.allocId = true :=
    Anneal.InitLemmas.nat_beq_refl alloc.allocId
  have hFitBs : off + bs.length ≤ alloc.bytes.length := by
    rw [hBsLen]; exact hFit
  have hInB : isInBounds alloc off bs.length = true :=
    Nat.ble_eq_true_of_le hFitBs
  have hAl : isAligned alloc off 0 = true := isAligned_zero_eq_true alloc off
  let bytes' := alloc.bytes.take off ++ bs ++
    alloc.bytes.drop (off + bs.length)
  let alloc' : Allocation := { alloc with bytes := bytes' }
  let m' : MemoryState := { nextAllocId := nextId, allocations := [alloc'] }
  refine ⟨m', ?_, ?_⟩
  · unfold writeBytes
    dsimp only [m, place, findAllocation]
    rw [ite_bool_true hIdRefl]
    dsimp only
    rw [ite_bool_false hBsBeq0]
    have hGuard :
        (!alloc.live || !isInBounds alloc off bs.length ||
          !isAligned alloc off 0) = false := by
      rw [hLive, hInB, hAl]; rfl
    rw [ite_bool_false hGuard, hMut]
    dsimp only [replaceAllocation, m', alloc', bytes']
    rw [ite_bool_true hIdRefl, hMut]
  · have hOffLe : off ≤ alloc.bytes.length :=
      Nat.le_trans (Nat.le_add_right off layout.size) hFit
    have hTakeLen : (alloc.bytes.take off).length = off :=
      list_take_length_of_le hOffLe
    have hBytes'Len : bytes'.length = alloc.bytes.length := by
      dsimp only [bytes']
      rw [list_length_append, list_length_append, hTakeLen,
        list_drop_length (off + bs.length) alloc.bytes,
        Nat.add_sub_of_le hFitBs]
    have hInB' : isInBounds alloc' off layout.size = true := by
      unfold isInBounds
      rw [hBytes'Len]
      exact Nat.ble_eq_true_of_le hFit
    have hAl' : isAligned alloc' off 0 = true :=
      isAligned_zero_eq_true alloc' off
    unfold readBytes
    dsimp only [m', place, findAllocation]
    have hIdRefl' : Nat.beq alloc'.allocId alloc.allocId = true := hIdRefl
    rw [ite_bool_true hIdRefl']
    dsimp only
    rw [ite_bool_false hSizeBeq0]
    have hGuard' :
        (!alloc'.live || !isInBounds alloc' off layout.size ||
          !isAligned alloc' off 0) = false := by
      change (!alloc.live || !isInBounds alloc' off layout.size ||
        !isAligned alloc' off 0) = false
      rw [hLive, hInB', hAl']; rfl
    rw [ite_bool_false hGuard']
    dsimp only [alloc']
    have hSlice : (bytes'.drop off).take layout.size = bs := by
      have hAssoc :
          bytes' = alloc.bytes.take off ++
            (bs ++ alloc.bytes.drop (off + bs.length)) :=
        List.append_assoc _ _ _
      rw [hAssoc, list_drop_append_of_length hTakeLen,
        list_take_append_of_length hBsLen]
    rw [hSlice]

private theorem writeBytes_misaligned_arena (bs : List AllocByte)
    (w : IntWidth) (hw : w ≠ .i8) (hLen : bs.length = w.byteSize) :
    writeBytes Spec.sampleUnalignedArena ⟨1, 1⟩ (intLayout w).alignLog2 bs =
      .error .undefined := by
  have hAlFalse :
      isAligned
        { allocId := 1, alignLog2 := 4, mutability := .mut,
          bytes := List.replicate 17 .uninit, live := true }
        1 (intLayout w).alignLog2 = false := by
    cases w with
    | i8 => exact False.elim (hw rfl)
    | i16 | i32 | i64 | i128 | isize => rfl
  have hBeq0 : Nat.beq bs.length 0 = false := by
    cases w with
    | i8 => exact False.elim (hw rfl)
    | i16 | i32 | i64 | i128 | isize => rw [hLen]; rfl
  unfold writeBytes
  dsimp only [Spec.sampleUnalignedArena, findAllocation]
  rw [ite_bool_true (rfl : Nat.beq 1 1 = true)]
  dsimp only
  rw [ite_bool_false hBeq0]
  have hGuard :
      (!true ||
        !isInBounds
          { allocId := 1, alignLog2 := 4, mutability := .mut,
            bytes := List.replicate 17 .uninit, live := true }
          1 bs.length ||
        !isAligned
          { allocId := 1, alignLog2 := 4, mutability := .mut,
            bytes := List.replicate 17 .uninit, live := true }
          1 (intLayout w).alignLog2) = true := by
    rw [hAlFalse]
    exact Bool.or_true _
  rw [ite_bool_true hGuard]

private theorem storeIndirect_misaligned_arena (w : IntWidth) (s : Bool)
    (hw : w ≠ .i8) (v : Val) (hv : checkVal v (.int w s) = true) :
    storeIndirect Spec.sampleUnalignedArena (.int w s) ⟨1, 1⟩ v =
      .error .undefined := by
  let ⟨bits, hvEq, _⟩ := checkVal_int_iff.mp hv
  subst hvEq
  unfold storeIndirect
  dsimp only [layoutOfTy]
  unfold encodeVal
  rw [hv, ite_bool_false (rfl : (!true) = false)]
  dsimp only
  refine writeBytes_misaligned_arena _ w hw ?_
  rw [list_length_map, encodeUInt_length]

private theorem unalign_u32_roundtrip (x : BitVec 32) :
    ∃ (bs : List AllocByte) (m' : MemoryState),
      encodeVal profileTargetEndian (.int .i32 false) (Spec.u32Val x) =
        .ok bs ∧
      writeBytes Spec.sampleUnalignedArena ⟨1, 1⟩ 0 bs = .ok m' ∧
      readBytes m' ⟨1, 1⟩ 4 0 = .ok bs ∧
      decodeVal profileTargetEndian (.int .i32 false) bs =
        .ok (some (Spec.u32Val x)) := by
  have hv : checkVal (Spec.u32Val x) (.int .i32 false) = true := u32_valid x
  have hBitsNat : (BitVec.ofNat 128 x.toNat).toNat = x.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))
  let raw := encodeUInt profileTargetEndian 4 (BitVec.ofNat 128 x.toNat).toNat
  let bs := raw.map (fun b => AllocByte.init b none)
  have hEnc :
      encodeVal profileTargetEndian (.int .i32 false) (Spec.u32Val x) =
        .ok bs := by
    unfold encodeVal
    rw [hv]
    rfl
  have hBsLen : bs.length = 4 := by
    dsimp only [bs, raw]
    rw [list_length_map, encodeUInt_length]
  have hArenaLen : 1 + 4 ≤ (List.replicate 17 AllocByte.uninit).length := by
    rw [list_length_replicate]
    decide
  let ⟨m', hWr, hRd⟩ :=
    unalign_write_read_any
      { allocId := 1, alignLog2 := 4, mutability := .mut,
        bytes := List.replicate 17 .uninit, live := true }
      2 1 (.int .i32 false) ⟨4, 2⟩ (Spec.u32Val x) bs
      rfl rfl rfl (by decide) hEnc hBsLen hArenaLen
  refine ⟨bs, m', hEnc, hWr, hRd, ?_⟩
  have hDecRaw : decodeUInt profileTargetEndian raw = x.toNat := by
    dsimp only [raw, profileTargetEndian, encodeUInt, decodeUInt]
    rw [reverse_reverse, hBitsNat, natOfLeBytes_leBytesOfNat 4 x.toNat]
    exact Nat.mod_eq_of_lt x.isLt
  have hLenBeq : (!Nat.beq bs.length 4) = false := by
    rw [hBsLen]; rfl
  let bits : BitVec 128 := BitVec.ofNat 128 x.toNat
  have hBitsLt : bits.toNat < intWidthModulus .i32 := by
    dsimp only [bits]
    rw [hBitsNat]
    exact x.isLt
  have hTrunc : truncateBits .i32 bits = bits :=
    truncateBits_of_toNat_lt hBitsLt
  unfold decodeVal
  dsimp only [layoutOfTy, intLayout]
  rw [ite_bool_false hLenBeq, ite_bool_false (rfl : Nat.beq 4 0 = false),
    initBytes?_map_init raw]
  dsimp only [evalConstLit]
  rw [hDecRaw]
  rw [show BitVec.ofNat 128 x.toNat = bits from rfl, hTrunc,
    ite_bool_false (bne_self_eq_false bits)]
  rfl

private theorem unalign_memory_sound : Spec.UnalignMemorySound := by
  refine ⟨unalign_write_read_any, ?_, unalign_u32_roundtrip⟩
  intro w s hw
  refine ⟨?_, storeIndirect_misaligned_arena w s hw⟩
  cases w with
  | i8 => exact False.elim (hw rfl)
  | i16 | i32 | i64 | i128 | isize => rfl

/-! ### Part 2B: `ArrayCodecSound` -/

private theorem array_fromZeros_lift (endian : TargetEndian) (ty : MirTy) :
    ∀ (n : Nat), Spec.IsFromZeros endian ty → Spec.ArrayFromZeros endian ty n
  | 0, ⟨layout, _, hLay, _, _⟩ => by
    refine ⟨layout, [], hLay, ?_, rfl, fun _ hMem => by cases hMem⟩
    rw [Nat.zero_mul]
    rfl
  | n + 1, hFz => by
    let ⟨layout, v0, hLay, hDec0, hCv0⟩ := hFz
    let ⟨layout', vs, hLay', hDecRest, hLenVs, hAllCv⟩ :=
      array_fromZeros_lift endian ty n hFz
    rw [hLay] at hLay'
    injection hLay' with hEqL
    subst hEqL
    refine ⟨layout, v0 :: vs, hLay, ?_, congrArg Nat.succ hLenVs, ?_⟩
    · have hMul : (n + 1) * layout.size = layout.size + n * layout.size := by
        rw [Nat.succ_mul, Nat.add_comm]
      let zElem := List.replicate layout.size (AllocByte.init 0 none)
      let zRest := List.replicate (n * layout.size) (AllocByte.init 0 none)
      have hRep :
          List.replicate ((n + 1) * layout.size) (AllocByte.init 0 none) =
            zElem ++ zRest := by
        rw [hMul]
        exact replicate_add layout.size (n * layout.size) _
      have hZElemLen : zElem.length = layout.size :=
        list_length_replicate layout.size _
      have hTotLen :
          (List.replicate ((n + 1) * layout.size)
            (AllocByte.init 0 none)).length = (n + 1) * layout.size :=
        list_length_replicate _ _
      have hLenBeq :
          (!Nat.beq
            (List.replicate ((n + 1) * layout.size)
              (AllocByte.init 0 none)).length
            ((n + 1) * layout.size)) = false := by
        rw [hTotLen, Anneal.InitLemmas.nat_beq_refl]; rfl
      unfold Spec.decodeArray
      rw [ite_bool_false hLenBeq, hRep, ← hZElemLen,
        list_take_append_exact zElem zRest,
        list_drop_append_exact zElem zRest,
        hZElemLen, hDec0, hDecRest]
    · intro v hMem
      cases hMem with
      | head => exact hCv0
      | tail _ hTail => exact hAllCv v hTail

private theorem array_fromBytes_lift (endian : TargetEndian) (ty : MirTy) :
    ∀ (n : Nat), Spec.IsFromBytes endian ty → Spec.ArrayFromBytes endian ty n
  | 0, ⟨layout, hLay, _⟩ => by
    refine ⟨layout, hLay, fun bs _ hbs _ => ?_⟩
    rw [Nat.zero_mul] at hbs
    cases bs with
    | nil => exact ⟨[], rfl, rfl, fun _ hMem => by cases hMem⟩
    | cons _ _ => cases hbs
  | n + 1, hFb => by
    let ⟨layout, hLay, hElemFb⟩ := hFb
    let ⟨layout', hLay', hRestFb⟩ := array_fromBytes_lift endian ty n hFb
    rw [hLay] at hLay'
    injection hLay' with hEqL
    subst hEqL
    refine ⟨layout, hLay, fun bs raw hbs hraw => ?_⟩
    have hMul : (n + 1) * layout.size = layout.size + n * layout.size := by
      rw [Nat.succ_mul, Nat.add_comm]
    have hSizeLe : layout.size ≤ bs.length := by
      rw [hbs, hMul]
      exact Nat.le_add_right layout.size (n * layout.size)
    have hTakeLen : (bs.take layout.size).length = layout.size :=
      list_take_length_of_le hSizeLe
    have hDropLen : (bs.drop layout.size).length = n * layout.size := by
      rw [list_drop_length, hbs, hMul, Nat.add_comm, Nat.add_sub_cancel]
    have hSplitEq : bs.take layout.size ++ bs.drop layout.size = bs :=
      list_take_append_drop layout.size bs
    have hrawSplit :
        initBytes? (bs.take layout.size ++ bs.drop layout.size) = some raw := by
      rw [hSplitEq]; exact hraw
    let ⟨rx, ry, hrx, hry⟩ := initBytes?_split hrawSplit
    let ⟨v0, hDec0, hCv0⟩ := hElemFb (bs.take layout.size) rx hTakeLen hrx
    let ⟨vs, hDecRest, hLenVs, hAllCv⟩ :=
      hRestFb (bs.drop layout.size) ry hDropLen hry
    have hLenBeq : (!Nat.beq bs.length ((n + 1) * layout.size)) = false := by
      rw [hbs, Anneal.InitLemmas.nat_beq_refl]; rfl
    refine ⟨v0 :: vs, ?_, congrArg Nat.succ hLenVs, ?_⟩
    · unfold Spec.decodeArray
      rw [ite_bool_false hLenBeq, hDec0, hDecRest]
    · intro v hMem
      cases hMem with
      | head => exact hCv0
      | tail _ hTail => exact hAllCv v hTail

private theorem list_map_append {α β : Type} (f : α → β) :
    ∀ (xs ys : List α), (xs ++ ys).map f = xs.map f ++ ys.map f
  | [], _ => rfl
  | x :: rest, ys => congrArg (List.cons (f x)) (list_map_append f rest ys)

private theorem array_intoBytes_lift (endian : TargetEndian) (ty : MirTy) :
    ∀ (n : Nat), Spec.IsIntoBytes endian ty → Spec.ArrayIntoBytes endian ty n
  | 0, ⟨layout, hLay, _, _⟩ => by
    refine ⟨layout, hLay, fun vs hLen _ => ?_⟩
    cases vs with
    | nil =>
      rw [Nat.zero_mul]
      exact ⟨[], [], rfl, rfl, rfl, rfl⟩
    | cons _ _ => cases hLen
  | n + 1, hIb => by
    let ⟨layout, hLay, hEncOk, hEncProp⟩ := hIb
    let ⟨layout', hLay', hRestIb⟩ := array_intoBytes_lift endian ty n hIb
    rw [hLay] at hLay'
    injection hLay' with hEqL
    subst hEqL
    refine ⟨layout, hLay, fun vs hLen hAllCv => ?_⟩
    cases vs with
    | nil => cases hLen
    | cons v0 rest =>
      have hRestLen : rest.length = n := Nat.succ.inj hLen
      have hCv0 : checkVal v0 ty = true := hAllCv v0 (.head _)
      let ⟨bs0, hEnc0⟩ := hEncOk v0 hCv0
      let ⟨hbs0Len, raw0, hraw0, hbs0Map⟩ := hEncProp v0 bs0 hEnc0
      let ⟨bsRest, rawRest, hEncRest, hbsRestLen, hrawRest, hbsRestMap⟩ :=
        hRestIb rest hRestLen (fun v hv => hAllCv v (.tail _ hv))
      refine ⟨bs0 ++ bsRest, raw0 ++ rawRest, ?_, ?_,
        initBytes?_append_of_some hraw0 hrawRest, ?_⟩
      · unfold Spec.encodeArray
        rw [hEnc0, hEncRest]
      · rw [list_length_append, hbs0Len, hbsRestLen, Nat.succ_mul, Nat.add_comm]
      · rw [list_map_append, ← hbs0Map, ← hbsRestMap]

private theorem array_codec_sound : Spec.ArrayCodecSound := by
  refine ⟨fun endian ty n =>
      ⟨array_fromZeros_lift endian ty n,
       array_fromBytes_lift endian ty n,
       array_intoBytes_lift endian ty n⟩,
    fun endian w s n =>
      ⟨array_fromZeros_lift endian (.int w s) n (int_fromZeros endian w s),
       array_fromBytes_lift endian (.int w s) n (int_fromBytes endian w s),
       array_intoBytes_lift endian (.int w s) n (int_intoBytes endian w s)⟩,
    fun endian => ?_⟩
  have hBad :
      Spec.decodeArray endian .bool 1 4
        [.init 0 none, .init 0 none, .init 2 none, .init 0 none] =
      .error .undefined := by
    cases endian <;> rfl
  refine ⟨array_fromZeros_lift endian .bool 4 (bool_fromZeros endian),
    array_intoBytes_lift endian .bool 4 (bool_intoBytes endian),
    hBad,
    fun ⟨layout, hLay, hAll⟩ => ?_⟩
  injection hLay with hEqL
  subst hEqL
  let ⟨_, hOk, _, _⟩ :=
    hAll [.init 0 none, .init 0 none, .init 2 none, .init 0 none]
      [0, 0, 2, 0] rfl rfl
  rw [hBad] at hOk
  cases hOk

/-! ### Part 2C: `MaybeUninitSound` -/

private theorem maybeUninit_sound : Spec.MaybeUninitSound := by
  intro endian w s
  let uninitBuf := List.replicate w.byteSize AllocByte.uninit
  have hInit : initBytes? uninitBuf = none := by
    cases w <;> rfl
  have hDec : decodeVal endian (.int w s) uninitBuf = .ok none := by
    cases endian <;> cases w <;> cases s <;> rfl
  refine ⟨hInit, hDec, fun v hEnc => ?_⟩
  let ⟨_, _, _, hEncProp⟩ := int_intoBytes endian w s
  have ⟨_, raw, hSome, _⟩ := hEncProp v uninitBuf hEnc
  rw [hInit] at hSome
  cases hSome

/-! ### Part 2D: `PointerAndZstSound` -/

private theorem uint8_eq_zero_of_toNat_eq_zero {b : UInt8}
    (h : b.toNat = 0) : b = 0 := by
  cases b with
  | ofBitVec bv =>
    cases bv with
    | ofFin f =>
      cases f with
      | mk val isLt =>
        cases h
        rfl

private theorem natOfLeBytes_eq_zero_iff_replicate :
    ∀ (xs : List UInt8),
      natOfLeBytes xs = 0 ↔ xs = List.replicate xs.length (0 : UInt8)
  | [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | b :: rest => by
    constructor
    · intro hZero
      unfold natOfLeBytes at hZero
      have hb0 : b.toNat = 0 := by
        cases hb : b.toNat with
        | zero => rfl
        | succ k =>
          rw [hb, Nat.succ_add] at hZero
          cases hZero
      have hMul0 : 256 * natOfLeBytes rest = 0 := by
        rw [hb0, Nat.zero_add] at hZero
        exact hZero
      have hRest0 : natOfLeBytes rest = 0 := by
        cases hr : natOfLeBytes rest with
        | zero => rfl
        | succ k =>
          rw [hr, Nat.mul_succ] at hMul0
          cases hMul0
      have hbZ : b = 0 := uint8_eq_zero_of_toNat_eq_zero hb0
      have hRestRep : rest = List.replicate rest.length 0 :=
        (natOfLeBytes_eq_zero_iff_replicate rest).mp hRest0
      subst hbZ
      exact congrArg (List.cons 0) hRestRep
    · intro hRep
      injection hRep with hb hRest
      subst hb
      have hRest0 : natOfLeBytes rest = 0 :=
        (natOfLeBytes_eq_zero_iff_replicate rest).mpr hRest
      unfold natOfLeBytes
      rw [hRest0]
      rfl

private theorem decodeUInt_eight_zero_iff (endian : TargetEndian)
    (raw : List UInt8) (hLen : raw.length = 8) :
    decodeUInt endian raw = 0 ↔ raw = List.replicate 8 (0 : UInt8) := by
  cases endian with
  | little =>
    unfold decodeUInt
    rw [natOfLeBytes_eq_zero_iff_replicate raw, hLen]
  | big =>
    unfold decodeUInt
    rw [natOfLeBytes_eq_zero_iff_replicate raw.reverse,
      list_length_reverse, hLen]
    constructor
    · intro hRev
      have h1 := congrArg List.reverse hRev
      rw [reverse_reverse, reverse_replicate] at h1
      exact h1
    · intro hRaw
      rw [hRaw, reverse_replicate]

private theorem pointer_and_zst_sound : Spec.PointerAndZstSound := by
  refine ⟨⟨rfl, fun endian => ⟨?_, ?_, decodeUInt_eight_zero_iff endian⟩⟩,
    ⟨rfl,
      fun endian =>
        ⟨unit_fromZeros endian, unit_fromBytes endian,
         unit_intoBytes endian, unit_unaligned⟩,
      fun m place a hFound => ?_⟩⟩
  · cases endian <;> rfl
  · cases endian <;> (intro h; cases h)
  · refine ⟨?_, ?_⟩
    · unfold readBytes
      rw [hFound]
      dsimp only
      rw [isAligned_zero_eq_true a place.offset]
      rfl
    · unfold writeBytes
      rw [hFound]
      dsimp only
      rw [isAligned_zero_eq_true a place.offset]
      rfl

private theorem generic_wrapper_and_array_model_spec :
    Spec.GenericWrapperAndArrayModelSpec :=
  ⟨unalign_memory_sound,
   array_codec_sound,
   maybeUninit_sound,
   pointer_and_zst_sound⟩

/-! ## Top-Level Proof-Unit Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, bodies_unique_identities, ?_, ?_⟩
  · intro defId body found
    have hSub := bodiesVerified_getElem all_bodies_verified defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨⟨rfl, ?_⟩, generic_wrapper_and_array_model_spec⟩
    intro defId c found
    have hSub := allContractsAt_getElem all_contracts_at defId c found
    rw [Nat.zero_add] at hSub
    exact hSub

end Proof
