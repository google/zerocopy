-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp.Execution

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private abbrev idBlocks : List BasicBlock :=
  [{ statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
     terminator := .return_
     cleanup := false }]

private abbrev moveBlocks : List BasicBlock :=
  [{ statements :=
       [.storageLive 2,
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩)),
        .storageDead 2]
     terminator := .return_
     cleanup := false }]

private theorem verified_id {idx : DefId} (b : Body)
    (hGet : Trusted.MirSemantics.getElem? Captured.program.bodies idx = some b)
    (hAdm : BodyStaticAdmitted Captured.program b = true)
    (hArgs : b.argumentCount = 1)
    (hLocs : b.locals = [.int .isize false, .int .isize false])
    (hBbs : b.basicBlocks = idBlocks) :
    BodyVerified Captured.program idx b (fun _ => True) := by
  refine bodyVerified_of_safe hGet hAdm (fun args valid _ => ?_)
  cases b with
  | mk ac locs bbs iu ident =>
    dsimp only at hArgs hLocs hBbs
    subst hArgs; subst hLocs; subst hBbs
    unfold ValidEntryArgs at valid
    change checkArgsMatch args [.int .isize false] = true at valid
    rw [checkArgsMatch_cons_iff] at valid
    let ⟨v, rest, hCons, hv, hNil⟩ := valid
    rw [checkArgsMatch_nil_iff] at hNil
    subst hCons; subst hNil
    rw [checkVal_int_iff] at hv
    let ⟨bits, hvEq, hT⟩ := hv
    subst hvEq
    let b' : Body :=
      { argumentCount := 1, isUnsafe := iu,
        locals := [.int .isize false, .int .isize false],
        basicBlocks := idBlocks, identity := ident }
    have hCheck : checkVal (.scalar ⟨.isize, false, bits⟩)
        (.int .isize false) = true :=
      checkVal_int_iff.mpr ⟨bits, rfl, hT⟩
    have hInit :
        initLocalsLoop b' [.scalar ⟨.isize, false, bits⟩] 0 b'.locals =
        [.immediate none, .immediate (some (.scalar ⟨.isize, false, bits⟩))] := rfl
    have hWrite :
        writePlace .little [.immediate none, .immediate (some (.scalar ⟨.isize, false, bits⟩))]
          entryMemory 0 (.int .isize false) (.scalar ⟨.isize, false, bits⟩) =
        .ok ([.immediate (some (.scalar ⟨.isize, false, bits⟩)),
              .immediate (some (.scalar ⟨.isize, false, bits⟩))],
             entryMemory) := by
      unfold writePlace
      rw [ite_bool_false (by rw [hCheck]; rfl)]
      rfl
    have hStep :
        evalStep (bodyProg b') 0
          (mkState 0 0 [.immediate none,
            .immediate (some (.scalar ⟨.isize, false, bits⟩))]) =
        .step (mkState 0 1 [.immediate (some (.scalar ⟨.isize, false, bits⟩)),
          .immediate (some (.scalar ⟨.isize, false, bits⟩))]) := by
      change (match writePlace .little _ entryMemory 0 (.int .isize false) (.scalar ⟨.isize, false, bits⟩) with
        | .error k => StepResult.fault k
        | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
      rw [hWrite]; rfl
    have hExec : Executes .little b'
        (mkState 0 0 (initLocalsLoop b' [.scalar ⟨.isize, false, bits⟩] 0 b'.locals))
        (.scalar ⟨.isize, false, bits⟩) := by
      rw [hInit]
      exact .next hStep (.ret rfl)
    exact executes_safe hExec

private theorem verified_move {idx : DefId} (b : Body)
    (hGet : Trusted.MirSemantics.getElem? Captured.program.bodies idx = some b)
    (hAdm : BodyStaticAdmitted Captured.program b = true)
    (hArgs : b.argumentCount = 1)
    (hLocs : b.locals = [.int .isize false, .int .isize false, .int .isize false])
    (hBbs : b.basicBlocks = moveBlocks) :
    BodyVerified Captured.program idx b (fun _ => True) := by
  refine bodyVerified_of_safe hGet hAdm (fun args valid _ => ?_)
  cases b with
  | mk ac locs bbs iu ident =>
    dsimp only at hArgs hLocs hBbs
    subst hArgs; subst hLocs; subst hBbs
    unfold ValidEntryArgs at valid
    change checkArgsMatch args [.int .isize false] = true at valid
    rw [checkArgsMatch_cons_iff] at valid
    let ⟨v, rest, hCons, hv, hNil⟩ := valid
    rw [checkArgsMatch_nil_iff] at hNil
    subst hCons; subst hNil
    rw [checkVal_int_iff] at hv
    let ⟨bits, hvEq, hT⟩ := hv
    subst hvEq
    let sv : Val := .scalar ⟨.isize, false, bits⟩
    let b' : Body :=
      { argumentCount := 1, isUnsafe := iu,
        locals := [.int .isize false, .int .isize false, .int .isize false],
        basicBlocks := moveBlocks, identity := ident }
    have hCheck : checkVal sv (.int .isize false) = true :=
      checkVal_int_iff.mpr ⟨bits, rfl, hT⟩
    have hInit :
        initLocalsLoop b' [sv] 0 b'.locals =
        [.immediate none, .immediate (some sv), .dead] := rfl
    have hS0 : evalStep (bodyProg b') 0
        (mkState 0 0 [.immediate none, .immediate (some sv), .dead]) =
        .step (mkState 0 1 [.immediate none, .immediate (some sv), .immediate none]) := rfl
    have hW2 : writePlace .little [.immediate none, .immediate (some sv), .immediate none]
        entryMemory 2 (.int .isize false) sv =
        .ok ([.immediate none, .immediate (some sv), .immediate (some sv)], entryMemory) := by
      unfold writePlace
      rw [ite_bool_false (by rw [hCheck]; rfl)]
      rfl
    have hS1 : evalStep (bodyProg b') 0
        (mkState 0 1 [.immediate none, .immediate (some sv), .immediate none]) =
        .step (mkState 0 2 [.immediate none, .immediate (some sv), .immediate (some sv)]) := by
      change (match writePlace .little _ entryMemory 2 (.int .isize false) sv with
        | .error k => StepResult.fault k
        | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 2, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
      rw [hW2]; rfl
    have hW0 : writePlace .little [.immediate none, .immediate (some sv), .immediate (some sv)]
        entryMemory 0 (.int .isize false) sv =
        .ok ([.immediate (some sv), .immediate (some sv), .immediate (some sv)], entryMemory) := by
      unfold writePlace
      rw [ite_bool_false (by rw [hCheck]; rfl)]
      rfl
    have hS2 : evalStep (bodyProg b') 0
        (mkState 0 2 [.immediate none, .immediate (some sv), .immediate (some sv)]) =
        .step (mkState 0 3 [.immediate (some sv), .immediate (some sv), .immediate (some sv)]) := by
      change (match writePlace .little _ entryMemory 0 (.int .isize false) sv with
        | .error k => StepResult.fault k
        | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 3, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
      rw [hW0]; rfl
    have hS3 : evalStep (bodyProg b') 0
        (mkState 0 3 [.immediate (some sv), .immediate (some sv), .immediate (some sv)]) =
        .step (mkState 0 4 [.immediate (some sv), .immediate (some sv), .dead]) := rfl
    have hExec : Executes .little b'
        (mkState 0 0 (initLocalsLoop b' [sv] 0 b'.locals)) sv := by
      rw [hInit]
      exact .next hS0 (.next hS1 (.next hS2 (.next hS3 (.ret rfl))))
    exact executes_safe hExec

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  intro defId body found
  have hB := bodiesVerified_getElem
    (p := Captured.program) (specs := Spec.specs) (idx := 0) (bs := Captured.program.bodies)
    (by
      refine ⟨
        verified_id Captured.body_0 rfl rfl rfl rfl rfl,
        verified_id Captured.body_1 rfl rfl rfl rfl rfl,
        verified_id Captured.body_2 rfl rfl rfl rfl rfl,
        verified_id Captured.body_3 rfl rfl rfl rfl rfl,
        verified_id Captured.body_4 rfl rfl rfl rfl rfl,
        verified_id Captured.body_5 rfl rfl rfl rfl rfl,
        verified_id Captured.body_6 rfl rfl rfl rfl rfl,
        verified_id Captured.body_7 rfl rfl rfl rfl rfl,
        verified_id Captured.body_8 rfl rfl rfl rfl rfl,
        verified_id Captured.body_9 rfl rfl rfl rfl rfl,
        verified_id Captured.body_10 rfl rfl rfl rfl rfl,
        verified_id Captured.body_11 rfl rfl rfl rfl rfl,
        verified_id Captured.body_12 rfl rfl rfl rfl rfl,
        verified_id Captured.body_13 rfl rfl rfl rfl rfl,
        verified_id Captured.body_14 rfl rfl rfl rfl rfl,
        verified_id Captured.body_15 rfl rfl rfl rfl rfl,
        verified_id Captured.body_16 rfl rfl rfl rfl rfl,
        verified_id Captured.body_17 rfl rfl rfl rfl rfl,
        verified_id Captured.body_18 rfl rfl rfl rfl rfl,
        verified_id Captured.body_19 rfl rfl rfl rfl rfl,
        verified_id Captured.body_20 rfl rfl rfl rfl rfl,
        verified_id Captured.body_21 rfl rfl rfl rfl rfl,
        verified_id Captured.body_22 rfl rfl rfl rfl rfl,
        verified_id Captured.body_23 rfl rfl rfl rfl rfl,
        verified_id Captured.body_24 rfl rfl rfl rfl rfl,
        verified_move Captured.body_25 rfl rfl rfl rfl rfl,
        verified_move Captured.body_26 rfl rfl rfl rfl rfl,
        verified_move Captured.body_27 rfl rfl rfl rfl rfl,
        verified_move Captured.body_28 rfl rfl rfl rfl rfl,
        verified_move Captured.body_29 rfl rfl rfl rfl rfl,
        verified_move Captured.body_30 rfl rfl rfl rfl rfl,
        verified_move Captured.body_31 rfl rfl rfl rfl rfl,
        verified_move Captured.body_32 rfl rfl rfl rfl rfl,
        verified_move Captured.body_33 rfl rfl rfl rfl rfl,
        verified_move Captured.body_34 rfl rfl rfl rfl rfl,
        verified_move Captured.body_35 rfl rfl rfl rfl rfl,
        verified_move Captured.body_36 rfl rfl rfl rfl rfl,
        verified_move Captured.body_37 rfl rfl rfl rfl rfl,
        verified_move Captured.body_38 rfl rfl rfl rfl rfl,
        verified_move Captured.body_39 rfl rfl rfl rfl rfl,
        verified_move Captured.body_40 rfl rfl rfl rfl rfl,
        verified_move Captured.body_41 rfl rfl rfl rfl rfl,
        verified_move Captured.body_42 rfl rfl rfl rfl rfl,
        verified_move Captured.body_43 rfl rfl rfl rfl rfl,
        verified_move Captured.body_44 rfl rfl rfl rfl rfl,
        verified_move Captured.body_45 rfl rfl rfl rfl rfl,
        verified_move Captured.body_46 rfl rfl rfl rfl rfl,
        verified_move Captured.body_47 rfl rfl rfl rfl rfl,
        verified_move Captured.body_48 rfl rfl rfl rfl rfl,
        verified_move Captured.body_49 rfl rfl rfl rfl rfl,
        trivial⟩)
    defId body found
  rw [Nat.zero_add] at hB
  exact hB

end Proof
