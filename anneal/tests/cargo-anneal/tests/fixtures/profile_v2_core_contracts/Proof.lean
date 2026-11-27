-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Spec
import Expected
import Anneal.MirWp
import Anneal.MirWp.V2Memory

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Step & Arithmetic Helpers -/

private theorem ite_bool_false {α : Type u} {b : Bool} {t f : α}
    (h : b = false) : (if b = true then t else f) = f := by
  rw [h]; rfl

private theorem ite_bool_true {α : Type u} {b : Bool} {t f : α}
    (h : b = true) : (if b = true then t else f) = t := by
  rw [h]; rfl

private theorem ite_any_false {α : Type u} {c : Prop} [d : Decidable c]
    {t f : α} (h : ¬c) : (@ite α c d t f) = f := by
  cases d with
  | isTrue hc => exact False.elim (h hc)
  | isFalse _ => rfl

private theorem ite_bool_eq_false {α : Type u} {b : Bool} {t f : α}
    {d : Decidable (b = true)} (h : b = false) :
    (@ite α (b = true) d t f) = f := by
  cases d with
  | isTrue hc => exact False.elim (by rw [h] at hc; cases hc)
  | isFalse _ => rfl

private theorem lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

private theorem blt_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

private theorem toNat_uint64_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (UInt64.ofNat n).toNat = n :=
  Nat.mod_eq_of_lt h

private theorem checkVal_int_eq {w : IntWidth} {s : Bool} {bits : BitVec 128}
    (h : truncateBits w bits = bits) :
    checkVal (.scalar ⟨w, s, bits⟩) (.int w s) = true :=
  checkVal_int_iff.mpr ⟨bits, rfl, h⟩

private theorem execOutcomeStateV2_step {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : execOutcomeStateV2 p onDone onFault fuel s') :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hNext

private theorem execOutcomeStateV2_done {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out) (hDone : onDone out) :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hDone

private theorem wellFormedV2_of_exec {p : Program} {q : Query} {fuel : Nat}
    {s₀ : State} (hInit : initStateV2 p q = .ok s₀)
    (hExec : execStateV2 p fuel s₀ (fun _ => True)) :
    WellFormedV2 p q := by
  refine ⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, fun k hFault => ?_⟩
  unfold ReachesResultV2 at hFault
  rw [hInit] at hFault
  let ⟨s, hReach, _, _, hEval⟩ := hFault
  let ⟨fuel', hE⟩ := execOutcomeStateV2_of_reaches hExec hReach
  cases fuel' with
  | zero => exact False.elim hE
  | succ f' =>
    have hEval' : evalStepV2 p s = .fault k := hEval
    change (match evalStepV2 p s with
      | .step st' =>
        execOutcomeStateV2 p (fun _ => True) (fun _ => False) f' st'
      | .done _ => True
      | .fault _ => False) at hE
    rw [hEval'] at hE
    exact hE

/-! ## Generic Step & Local Helpers -/

private theorem initStateV2_ok_of {p : Program} {q : Query} {body : Body}
    (hPW : Nat.beq p.pointerWidthBits 64 = true)
    (hPV : Nat.beq p.mirProfileVersion 2 = true)
    (hCM : validCallerMemory q.callerMem = true)
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hNonEmpty : body.basicBlocks.isEmpty = false)
    (hArgLt : Nat.blt body.argumentCount body.locals.length = true)
    (hSto : storageAnnotationsInBounds body = true)
    (hDiscr : discriminantTypesValidV2 body = true)
    (hCast : castTypesValid body = true)
    (hAssert : assertConditionTypesValid body = true)
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hArgs : checkArgsMatchV2 q.args
      ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true)
    (hNoRaw : tyListHasRawPtrV2
      ((body.locals.drop 1).take body.argumentCount) = false := by rfl) :
    initStateV2 p q = .ok
      ⟨[⟨p.entryDefId, 0, 0, initLocalsLoop body q.args 0 body.locals, none, none, none⟩],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  have h := Anneal.MirWp.initStateV2_ok_of hPW hPV hCM hEntry hNonEmpty hArgLt
    hSto hDiscr hCast hAssert hLocs hArgs hRefs hDisj
  unfold entryMemoryForArgsV2 at h
  rw [hNoRaw] at h
  exact h

private theorem readPlaceV2_copy_local {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true) :
    readPlaceV2 bodyLocals locals mem false ⟨lid, []⟩ =
      .ok (ty, optVal, locals, mem) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [hSup]
  change (if false = true then Except.error FaultKind.unsupported else _) = _
  rw [ite_bool_false rfl]
  rfl

private theorem readPlaceV2_move_local {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) =
      some locals') :
    readPlaceV2 bodyLocals locals mem true ⟨lid, []⟩ =
      .ok (ty, optVal, locals', mem) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [hSup]
  change (if false = true then Except.error FaultKind.unsupported else _) = _
  rw [ite_bool_false rfl]
  change (if true = true then match setElem? locals lid (liveUninitSlot ty) with
    | some locals1 => Except.ok (ty, optVal, locals1, mem)
    | none => Except.error FaultKind.unsupported else _) = _
  rw [hSet]
  rfl

private theorem evalRvalueV2_use_copy_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {dstTy : MirTy}
    {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some dstTy)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy dstTy = true)
    (hEq : MirTy.beq dstTy dstTy = true) :
    evalRvalueV2 bodyLocals locals mem dstTy (.use (.copy ⟨lid, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [hEq]
  rfl

private theorem evalRvalueV2_use_copy_u64_downcast1_field0_ok
    {bodyLocals : List MirTy} {locals : List LocalSlot} {mem : MemoryState}
    {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid =
      some (.option (.int .i64 false)))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some (.optionVal (some v))))) :
    evalRvalueV2 bodyLocals locals mem (.int .i64 false)
        (.use (.copy ⟨lid, [.downcast 1, .field 0 (.int .i64 false)]⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2 readPlaceV2
  dsimp only
  rw [hTy, hSlot]
  rfl

private theorem writePlaceDestV2_immediate_ok
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) =
      some locals') :
    writePlaceDestV2 locals mem (.local lid) ty val =
      .ok (locals', mem) := by
  unfold writePlaceDestV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]

private theorem writePlaceV2_immediate_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) =
      some locals') :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val =
      .ok (locals', mem) := by
  unfold writePlaceV2 resolvePlaceDestV2
  dsimp only
  exact writePlaceDestV2_immediate_ok hCheck hSlot hSet

private theorem evalRefRvalueV2_deref_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState}
    {srcMut reqMut : Mutability} {pt : MirTy} {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid =
      some (.ref srcMut pt))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hMutOk :
      (Mutability.beq srcMut .shared && Mutability.beq reqMut .mut) = false)
    (hDst : MirTy.beq (.ref reqMut pt) (.ref reqMut pt) = true)
    (hRef : refValidInMem mem reqMut pt v = .ok ()) :
    evalRefRvalueV2 bodyLocals locals mem (.ref reqMut pt) reqMut
        ⟨lid, [.deref]⟩ =
      .ok (v, locals, mem) := by
  unfold evalRefRvalueV2
  rw [hTy, hSlot]
  dsimp only
  rw [hMutOk, hDst]
  change (if false = true then _ else if false = true then _ else _) = _
  rw [ite_bool_false rfl, ite_bool_false rfl, hRef]

private theorem evalRvalueV2_ref_deref_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState}
    {srcMut reqMut : Mutability} {pt : MirTy} {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid =
      some (.ref srcMut pt))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hMutOk :
      (Mutability.beq srcMut .shared && Mutability.beq reqMut .mut) = false)
    (hDst : MirTy.beq (.ref reqMut pt) (.ref reqMut pt) = true)
    (hRef : refValidInMem mem reqMut pt v = .ok ()) :
    evalRvalueV2 bodyLocals locals mem (.ref reqMut pt)
        (.ref reqMut ⟨lid, [.deref]⟩) =
      .ok (v, locals, mem) :=
  evalRefRvalueV2_deref_ok hTy hSlot hMutOk hDst hRef

private theorem evalRvalueV2_discriminant_option_none_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {inner : MirTy}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some (.option inner))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some (.optionVal none)))) :
    evalRvalueV2 bodyLocals locals mem (.int .isize true)
        (.discriminant ⟨lid, []⟩) =
      .ok (.scalar ⟨.isize, true, BitVec.ofNat 128 0⟩, locals, mem) := by
  unfold evalRvalueV2
  dsimp only
  rw [ite_bool_false (by decide), hTy, hSlot]
  rfl

private theorem evalRvalueV2_discriminant_option_some_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {inner : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some (.option inner))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some (.optionVal (some v))))) :
    evalRvalueV2 bodyLocals locals mem (.int .isize true)
        (.discriminant ⟨lid, []⟩) =
      .ok (.scalar ⟨.isize, true, BitVec.ofNat 128 1⟩, locals, mem) := by
  unfold evalRvalueV2
  dsimp only
  rw [ite_bool_false (by decide), hTy, hSlot]
  rfl

private theorem evalRvalueV2_aggregateTuple2_move_ok
    {bodyLocals : List MirTy} {locals locals1 locals2 : List LocalSlot}
    {mem : MemoryState} {lid1 lid2 : LocalId} {ty1 ty2 : MirTy} {v1 v2 : Val}
    (hTy1 : Trusted.MirSemantics.getElem? bodyLocals lid1 = some ty1)
    (hSlot1 : Trusted.MirSemantics.getElem? locals lid1 =
      some (.immediate (some v1)))
    (hSup1 : isSupportedV2LocalTy ty1 = true)
    (hSet1 : Trusted.MirSemantics.setElem? locals lid1 (liveUninitSlot ty1) =
      some locals1)
    (hTy2 : Trusted.MirSemantics.getElem? bodyLocals lid2 = some ty2)
    (hSlot2 : Trusted.MirSemantics.getElem? locals1 lid2 =
      some (.immediate (some v2)))
    (hSup2 : isSupportedV2LocalTy ty2 = true)
    (hSet2 : Trusted.MirSemantics.setElem? locals1 lid2 (liveUninitSlot ty2) =
      some locals2)
    (hChk1 : checkValV2 v1 ty1 = true) (hChk2 : checkValV2 v2 ty2 = true) :
    evalRvalueV2 bodyLocals locals mem (.tuple [ty1, ty2])
        (.aggregateTuple [.move ⟨lid1, []⟩, .move ⟨lid2, []⟩]) =
      .ok (.tuple [v1, v2], locals2, mem) := by
  unfold evalRvalueV2
  dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
  rw [readPlaceV2_move_local hTy1 hSlot1 hSup1 hSet1]
  dsimp only
  rw [readPlaceV2_move_local hTy2 hSlot2 hSup2 hSet2]
  dsimp only
  have hNot : (!checkValV2List (argValues [(ty1, v1), (ty2, v2)]) [ty1, ty2]) =
      false := by
    dsimp only [argValues, checkValV2List]
    rw [hChk1, hChk2]; rfl
  rw [ite_bool_eq_false hNot]
  rfl

private theorem evalRvalueV2_aggregateTuple3_move_ok
    {bodyLocals : List MirTy}
    {locals locals1 locals2 locals3 : List LocalSlot}
    {mem : MemoryState} {lid1 lid2 lid3 : LocalId}
    {ty1 ty2 ty3 : MirTy} {v1 v2 v3 : Val}
    (hTy1 : Trusted.MirSemantics.getElem? bodyLocals lid1 = some ty1)
    (hSlot1 : Trusted.MirSemantics.getElem? locals lid1 =
      some (.immediate (some v1)))
    (hSup1 : isSupportedV2LocalTy ty1 = true)
    (hSet1 : Trusted.MirSemantics.setElem? locals lid1 (liveUninitSlot ty1) =
      some locals1)
    (hTy2 : Trusted.MirSemantics.getElem? bodyLocals lid2 = some ty2)
    (hSlot2 : Trusted.MirSemantics.getElem? locals1 lid2 =
      some (.immediate (some v2)))
    (hSup2 : isSupportedV2LocalTy ty2 = true)
    (hSet2 : Trusted.MirSemantics.setElem? locals1 lid2 (liveUninitSlot ty2) =
      some locals2)
    (hTy3 : Trusted.MirSemantics.getElem? bodyLocals lid3 = some ty3)
    (hSlot3 : Trusted.MirSemantics.getElem? locals2 lid3 =
      some (.immediate (some v3)))
    (hSup3 : isSupportedV2LocalTy ty3 = true)
    (hSet3 : Trusted.MirSemantics.setElem? locals2 lid3 (liveUninitSlot ty3) =
      some locals3)
    (hChk1 : checkValV2 v1 ty1 = true) (hChk2 : checkValV2 v2 ty2 = true)
    (hChk3 : checkValV2 v3 ty3 = true) :
    evalRvalueV2 bodyLocals locals mem (.tuple [ty1, ty2, ty3])
        (.aggregateTuple
          [.move ⟨lid1, []⟩, .move ⟨lid2, []⟩, .move ⟨lid3, []⟩]) =
      .ok (.tuple [v1, v2, v3], locals3, mem) := by
  unfold evalRvalueV2
  dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
  rw [readPlaceV2_move_local hTy1 hSlot1 hSup1 hSet1]
  dsimp only
  rw [readPlaceV2_move_local hTy2 hSlot2 hSup2 hSet2]
  dsimp only
  rw [readPlaceV2_move_local hTy3 hSlot3 hSup3 hSet3]
  dsimp only
  have hNot : (!checkValV2List (argValues [(ty1, v1), (ty2, v2), (ty3, v3)])
      [ty1, ty2, ty3]) = false := by
    dsimp only [argValues, checkValV2List]
    rw [hChk1, hChk2, hChk3]; rfl
  rw [ite_bool_eq_false hNot]
  rfl

private theorem evalArgOperandsV2_one_move {bodyLocals : List MirTy}
    {locals locals1 : List LocalSlot} {mem : MemoryState}
    {lid : LocalId} {ty : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) =
      some locals1) :
    evalArgOperandsV2 bodyLocals locals mem [.move ⟨lid, []⟩] =
      .ok ([(ty, v)], locals1, mem) := by
  unfold evalArgOperandsV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_move_local hTy hSlot hSup hSet]
  rfl

private theorem evalArgOperandsV2_two_move {bodyLocals : List MirTy}
    {locals locals1 locals2 : List LocalSlot} {mem : MemoryState}
    {lid1 lid2 : LocalId} {ty1 ty2 : MirTy} {v1 v2 : Val}
    (hTy1 : Trusted.MirSemantics.getElem? bodyLocals lid1 = some ty1)
    (hSlot1 : Trusted.MirSemantics.getElem? locals lid1 =
      some (.immediate (some v1)))
    (hSup1 : isSupportedV2LocalTy ty1 = true)
    (hSet1 : Trusted.MirSemantics.setElem? locals lid1 (liveUninitSlot ty1) =
      some locals1)
    (hTy2 : Trusted.MirSemantics.getElem? bodyLocals lid2 = some ty2)
    (hSlot2 : Trusted.MirSemantics.getElem? locals1 lid2 =
      some (.immediate (some v2)))
    (hSup2 : isSupportedV2LocalTy ty2 = true)
    (hSet2 : Trusted.MirSemantics.setElem? locals1 lid2 (liveUninitSlot ty2) =
      some locals2) :
    evalArgOperandsV2 bodyLocals locals mem
        [.move ⟨lid1, []⟩, .move ⟨lid2, []⟩] =
      .ok ([(ty1, v1), (ty2, v2)], locals2, mem) := by
  unfold evalArgOperandsV2
  dsimp only [evalOperandToSlotV2]
  rw [readPlaceV2_move_local hTy1 hSlot1 hSup1 hSet1]
  dsimp only
  unfold evalArgOperandsV2
  dsimp only [evalOperandToSlotV2]
  rw [readPlaceV2_move_local hTy2 hSlot2 hSup2 hSet2]
  rfl

private theorem evalStepV2_assign_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem mem1 mem2 : MemoryState}
    {cm : CallerMemory} {lid : LocalId} {rv : Rvalue} {dstTy : MirTy}
    {val : Val} {locals1 locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨lid, []⟩ rv))
    (hTy : placeStaticTyV2 body.locals ⟨lid, []⟩ = some dstTy)
    (hRv : evalRvalueV2 body.locals frame.locals mem dstTy rv =
      .ok (val, locals1, mem1))
    (hWr : writePlaceV2 body.locals locals1 mem1 ⟨lid, []⟩ dstTy val =
      .ok (locals2, mem2))
    (hHaz : checkAssignCopyHazardV2 body.locals frame.locals mem (.local lid)
      dstTy rv = .ok () := by rfl) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, frame.blockIdx, frame.stmtIdx + 1, locals2, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩],
        cm, mem2⟩ := by
  have hWr' : writePlaceDestV2 locals1 mem1 (.local lid) dstTy val =
      .ok (locals2, mem2) := hWr
  unfold evalStepV2
  dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hSt]; dsimp only
  unfold evalStatementV2
  dsimp only
  rw [hTy]; dsimp only [resolvePlaceDestV2]; rw [hRv]; dsimp only; rw [hWr']
  dsimp only; rw [hHaz]

private theorem evalStepV2_nop_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem : MemoryState}
    {cm : CallerMemory}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some .nop) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, frame.blockIdx, frame.stmtIdx + 1, frame.locals, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩],
        cm, mem⟩ := by
  unfold evalStepV2; dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hSt]; rfl

private theorem evalStepV2_storageLive_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem : MemoryState}
    {cm : CallerMemory} {lid : LocalId} {localTy : MirTy}
    {locals1 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.storageLive lid))
    (hTy : Trusted.MirSemantics.getElem? body.locals lid = some localTy)
    (hOld : Trusted.MirSemantics.getElem? frame.locals lid =
      some (.immediate none))
    (hSet : Trusted.MirSemantics.setElem? frame.locals lid
      (liveUninitSlot localTy) = some locals1)
    (hDeadOld : deallocateLocal mem (.immediate none) = .ok mem) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, frame.blockIdx, frame.stmtIdx + 1, locals1, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩],
        cm, mem⟩ := by
  unfold evalStepV2; dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hSt]; dsimp only
  unfold evalStatementV2; dsimp only
  rw [hTy, hOld]; dsimp only; rw [hSet]; dsimp only; rw [hDeadOld]

private theorem evalStepV2_storageLive_dead_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem : MemoryState}
    {cm : CallerMemory} {lid : LocalId} {localTy : MirTy}
    {locals1 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.storageLive lid))
    (hTy : Trusted.MirSemantics.getElem? body.locals lid = some localTy)
    (hOld : Trusted.MirSemantics.getElem? frame.locals lid = some .dead)
    (hSet : Trusted.MirSemantics.setElem? frame.locals lid
      (liveUninitSlot localTy) = some locals1) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, frame.blockIdx, frame.stmtIdx + 1, locals1, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩],
        cm, mem⟩ := by
  unfold evalStepV2; dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hSt]; dsimp only
  unfold evalStatementV2; dsimp only
  rw [hTy, hOld]; dsimp only; rw [hSet]; rfl

private theorem evalStepV2_storageDead_imm_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem : MemoryState}
    {cm : CallerMemory} {lid : LocalId} {optV : Option Val}
    {locals1 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.storageDead lid))
    (hNZ : Nat.beq lid 0 = false)
    (hOld : Trusted.MirSemantics.getElem? frame.locals lid =
      some (.immediate optV))
    (hSet : Trusted.MirSemantics.setElem? frame.locals lid .dead =
      some locals1) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, frame.blockIdx, frame.stmtIdx + 1, locals1, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩],
        cm, mem⟩ := by
  unfold evalStepV2; dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hSt]; dsimp only
  unfold evalStatementV2; dsimp only
  rw [ite_bool_false hNZ, hOld]; dsimp only; rw [hSet]; rfl

private theorem evalStepV2_goto_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem : MemoryState}
    {cm : CallerMemory} {target : BasicBlockId}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hNone : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (hLen : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .goto target) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, target, 0, frame.locals, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩], cm, mem⟩ := by
  unfold evalStepV2; dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hNone]; dsimp only
  rw [ite_bool_true hLen]
  unfold evalTerminatorV2
  rw [hTerm]; rfl

private theorem evalStepV2_coreCall_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem mem1 mem1' mem2 : MemoryState}
    {cm : CallerMemory} {op : CoreCallOp} {args : List Operand} {dst : Place}
    {target : BasicBlockId} {ua : UnwindAction} {dstTy : MirTy}
    {typedArgs : List (MirTy × Val)} {resVal : Val}
    {locals1 locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hNone : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (hLen : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .coreCall op args dst (some target) ua)
    (hEmp : dst.projection.isEmpty = true)
    (hDstTy : Trusted.MirSemantics.getElem? body.locals dst.localId = some dstTy)
    (hArgs : evalArgOperandsV2 body.locals frame.locals mem args =
      .ok (typedArgs, locals1, mem1))
    (hCall : execCoreCallWithMem mem1 op typedArgs dstTy = .ok (resVal, mem1'))
    (hWr : writePlaceV2 body.locals locals1 mem1' dst dstTy resVal =
      .ok (locals2, mem2)) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, target, 0, locals2, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩], cm, mem2⟩ := by
  unfold evalStepV2
  dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hNone]; dsimp only
  rw [ite_bool_true hLen]
  unfold evalTerminatorV2
  rw [hTerm]; dsimp only
  rw [ite_bool_false (by rw [hEmp]; rfl)]
  rw [hDstTy]; dsimp only; rw [hArgs]; dsimp only
  rw [hCall]; dsimp only; rw [hWr]; rfl

private theorem evalTerminatorV2_return_ok {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : MemoryState} {callerMem : CallerMemory}
    {retTy : MirTy} {retVal : Val} {ps : PanicStrategy} {hLocal oc : Bool}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hNoRodata : hasEscapingRodataPtr callerMem mem retTy retVal = false)
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalTerminatorV2 body bb frame mem callerMem ps hLocal oc =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false hNoRodata, ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]

private theorem evalStepV2_switchInt_move_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem : MemoryState}
    {cm : CallerMemory} {lid : LocalId} {sv : ScalarVal}
    {targets : SwitchTargets} {target : BasicBlockId}
    {ty : MirTy} {locals1 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hNone : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (hLen : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .switchInt (.move ⟨lid, []⟩) targets)
    (hTy : Trusted.MirSemantics.getElem? body.locals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? frame.locals lid =
      some (.immediate (some (.scalar sv))))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? frame.locals lid (liveUninitSlot ty) =
      some locals1)
    (hPrim : isPrimitiveReadableTy ty = true)
    (hBranch : evalSwitchBranches sv.width sv.bits targets.otherwise
      targets.branches = .ok target) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[⟨frame.defId, target, 0, locals1, frame.sysrootOp?, frame.retDst?, frame.retTarget?⟩], cm, mem⟩ := by
  unfold evalStepV2; dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hNone]; dsimp only
  rw [ite_bool_true hLen]
  unfold evalTerminatorV2
  rw [hTerm]; dsimp only
  unfold evalPrimitiveOperandV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_move_local hTy hSlot hSup hSet]
  dsimp only
  rw [ite_bool_false (by rw [hPrim]; rfl)]
  dsimp only
  rw [hBranch]
  rfl

private theorem evalStepV2_return_ok {p : Program} {body : Body}
    {bb : BasicBlock} {frame : FrameState} {mem : MemoryState}
    {callerMem : CallerMemory} {retTy : MirTy} {retVal : Val}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx =
      some bb)
    (hNone : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = none)
    (hLen : Nat.beq frame.stmtIdx bb.statements.length = true)
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hNoRodata : hasEscapingRodataPtr callerMem mem retTy retVal = false)
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalStepV2 p ⟨[frame], callerMem, mem⟩ =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalStepV2; dsimp only
  rw [hB]; dsimp only; rw [hBB]; dsimp only; rw [hNone]; dsimp only
  rw [ite_bool_true hLen]
  exact evalTerminatorV2_return_ok hTerm hCleanup hRetTy hRetSlot hNoRodata
    hStay hValid hDisj

/-! ## Caller Memory & Slice Helpers -/

private theorem natNotElem_cons_ne {x y : Nat} {ys : List Nat} :
    natNotElem x (y :: ys) = true → x ≠ y ∧ natNotElem x ys = true := by
  intro h
  unfold natNotElem at h
  cases hEq : Nat.beq x y with
  | true => rw [hEq] at h; cases h
  | false =>
    rw [hEq] at h
    exact ⟨(fun hxy => by subst hxy; rw [Nat.beq_refl] at hEq; cases hEq), h⟩

private theorem findAllocation_append_of_not_in_prefix
    (pref : List Allocation) (a : Allocation) (suff : List Allocation)
    (hDisj : natNotElem a.allocId (pref.map Allocation.allocId) = true) :
    findAllocation a.allocId (pref ++ a :: suff) = some a := by
  induction pref with
  | nil =>
    change (if Nat.beq a.allocId a.allocId then some a
      else findAllocation a.allocId suff) = some a
    rw [Nat.beq_refl]
    rfl
  | cons x xs ih =>
    have hCons :
        natNotElem a.allocId (x.allocId :: xs.map Allocation.allocId) = true :=
      hDisj
    let ⟨hNe, hRest⟩ := natNotElem_cons_ne hCons
    change (if Nat.beq x.allocId a.allocId then some x
      else findAllocation a.allocId (xs ++ a :: suff)) = some a
    have hFlip : Nat.beq x.allocId a.allocId = false := by
      cases hB : Nat.beq x.allocId a.allocId with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB).symm)
    rw [hFlip]
    exact ih hRest

private theorem natNotElem_iff_not_mem (x : Nat) :
    ∀ xs : List Nat, natNotElem x xs = true ↔ ∀ y, y ∈ xs → x ≠ y
  | [] => ⟨(fun _ _ hy => by cases hy), (fun _ => rfl)⟩
  | y :: ys =>
    ⟨(fun h z hz => by
      let ⟨hNe, hRest⟩ := natNotElem_cons_ne h
      cases hz with
      | head _ => exact hNe
      | tail _ hIn => exact (natNotElem_iff_not_mem x ys).mp hRest z hIn),
     (fun h => by
      have hNe : x ≠ y := h y (.head _)
      have hRest : natNotElem x ys = true :=
        (natNotElem_iff_not_mem x ys).mpr (fun z hz => h z (.tail _ hz))
      unfold natNotElem
      have hFalse : Nat.beq x y = false := by
        cases hB : Nat.beq x y with
        | false => rfl
        | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB))
      rw [hFalse]
      exact hRest)⟩

private theorem extractCallerAllocations_suffix (m : MemoryState) :
    ∀ (pref suff : List Allocation),
      m.allocations = pref ++ suff →
      (∀ a, a ∈ suff → findAllocation a.allocId m.allocations = some a) →
      extractCallerAllocations m suff = suff
  | _, [], _, _ => rfl
  | pref, a :: rest, hEq, hFind => by
    have hFoundA : findAllocation a.allocId m.allocations = some a :=
      hFind a (.head _)
    have hTail : extractCallerAllocations m rest = rest :=
      extractCallerAllocations_suffix m (pref ++ [a]) rest
        (by rw [hEq, List.append_assoc]; rfl)
        (fun b hb => hFind b (.tail _ hb))
    change (findAllocation a.allocId m.allocations).getD a ::
      extractCallerAllocations m rest = a :: rest
    rw [hFoundA, hTail]
    rfl

private theorem natNotElem_of_forall_ne {x : Nat} :
    ∀ {xs : List Nat}, (∀ y, y ∈ xs → x ≠ y) → natNotElem x xs = true :=
  fun h => (natNotElem_iff_not_mem x _).mpr h

private theorem mem_map_reverse_append {x : Allocation}
    {pref : List Allocation} {y : AllocId}
    (h : y ∈ (pref ++ [x]).map Allocation.allocId) :
    y = x.allocId ∨ y ∈ pref.map Allocation.allocId := by
  induction pref with
  | nil =>
    cases h with
    | head _ => exact .inl rfl
    | tail _ hEmpty => cases hEmpty
  | cons p ps ih =>
    cases h with
    | head _ => exact .inr (.head _)
    | tail _ hTail =>
      cases ih hTail with
      | inl hEq => exact .inl hEq
      | inr hIn => exact .inr (.tail _ hIn)

private theorem mem_map_self_append (pref : List Allocation) (x : Allocation) :
    x.allocId ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => exact .head _
  | cons _ _ ih => exact .tail _ ih

private theorem mem_map_append_left {pref : List Allocation} {x : Allocation}
    {w : AllocId} (h : w ∈ pref.map Allocation.allocId) :
    w ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => cases h
  | cons _ _ ih =>
    cases h with
    | head _ => exact .head _
    | tail _ h' => exact .tail _ (ih h')

private theorem findAllocation_in_allocIdsValid (pref : List Allocation) :
    ∀ (suff : List Allocation) (seen : List AllocId),
      (∀ z, z ∈ seen →
        natNotElem z (pref.map Allocation.allocId) = true → False) →
      (∀ z, z ∈ pref.map Allocation.allocId → z ∈ seen) →
      allocIdsValid seen suff = true →
      ∀ a, a ∈ suff → findAllocation a.allocId (pref ++ suff) = some a
  | [], _, _, _, _, _, ha => by cases ha
  | x :: xs, seen, hSeenSub, hPrefSub, hValid, a, ha => by
    unfold allocIdsValid at hValid
    cases hNz : !Nat.beq x.allocId 0 with
    | false => rw [hNz] at hValid; cases hValid
    | true =>
      rw [hNz] at hValid
      cases hNotElem : natNotElem x.allocId seen with
      | false => rw [hNotElem] at hValid; cases hValid
      | true =>
        rw [hNotElem] at hValid
        cases hLen : Nat.blt x.bytes.length isizeMaxBytes with
        | false => rw [hLen] at hValid; cases hValid
        | true =>
          rw [hLen] at hValid
          cases hAl : Nat.ble x.alignLog2 29 with
          | false => rw [hAl] at hValid; cases hValid
          | true =>
            rw [hAl] at hValid
            cases ha with
            | head _ =>
              have hForall := (natNotElem_iff_not_mem x.allocId seen).mp hNotElem
              have hNotPref :
                  natNotElem x.allocId (pref.map Allocation.allocId) = true :=
                natNotElem_of_forall_ne (fun y hy => hForall y (hPrefSub y hy))
              exact findAllocation_append_of_not_in_prefix pref x xs hNotPref
            | tail _ hIn =>
              have hEq : pref ++ x :: xs = (pref ++ [x]) ++ xs := by
                rw [List.append_assoc]; rfl
              rw [hEq]
              exact findAllocation_in_allocIdsValid (pref ++ [x]) xs
                (x.allocId :: seen)
                (fun z hz hNot => by
                  cases hz with
                  | head _ =>
                    exact (natNotElem_iff_not_mem x.allocId _).mp hNot x.allocId
                      (mem_map_self_append pref x) rfl
                  | tail _ hZ =>
                    exact hSeenSub z hZ (natNotElem_of_forall_ne (fun w hw =>
                      (natNotElem_iff_not_mem z _).mp hNot w
                        (mem_map_append_left hw))))
                (fun z hz => by
                  cases mem_map_reverse_append hz with
                  | inl hEqZ => subst hEqZ; exact .head _
                  | inr hInP => exact .tail _ (hPrefSub z hInP))
                hValid a hIn

private theorem extractCallerMemory_entry (cm : CallerMemory)
    (hValid : validCallerMemory cm = true) :
    extractCallerMemory cm (entryMemoryWithCaller cm) = cm := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    have hEq := extractCallerAllocations_suffix
      (entryMemoryWithCaller ⟨allocs⟩) [] allocs rfl
      (findAllocation_in_allocIdsValid [] allocs []
        (fun _ hz => by cases hz) (fun _ hz => by cases hz) hValid)
    rw [hEq]

private theorem findAllocation_mem {aid : AllocId} :
    ∀ {allocs : List Allocation} {a : Allocation},
      findAllocation aid allocs = some a → a ∈ allocs
  | [], _, h => by cases h
  | x :: xs, a, h => by
    change (if Nat.beq x.allocId aid then some x
      else findAllocation aid xs) = some a at h
    cases hEq : Nat.beq x.allocId aid with
    | true => rw [hEq] at h; cases h; exact .head _
    | false => rw [hEq] at h; exact .tail _ (findAllocation_mem h)

private theorem allocIdsValid_bytes_lt :
    ∀ (seen : List AllocId) (allocs : List Allocation),
      allocIdsValid seen allocs = true →
      ∀ a, a ∈ allocs → a.bytes.length < isizeMaxBytes
  | _, [], _, _, ha => by cases ha
  | seen, x :: xs, hValid, a, ha => by
    unfold allocIdsValid at hValid
    cases hNz : !Nat.beq x.allocId 0 with
    | false => rw [hNz] at hValid; cases hValid
    | true =>
      rw [hNz] at hValid
      cases hNotElem : natNotElem x.allocId seen with
      | false => rw [hNotElem] at hValid; cases hValid
      | true =>
        rw [hNotElem] at hValid
        cases hLen : Nat.blt x.bytes.length isizeMaxBytes with
        | false => rw [hLen] at hValid; cases hValid
        | true =>
          rw [hLen] at hValid
          cases hAl : Nat.ble x.alignLog2 29 with
          | false => rw [hAl] at hValid; cases hValid
          | true =>
            rw [hAl] at hValid
            cases ha with
            | head _ => exact lt_of_blt_true hLen
            | tail _ hIn =>
              exact allocIdsValid_bytes_lt (x.allocId :: seen) xs hValid a hIn

private theorem entryMemoryWithCaller_bytes_lt (cm : CallerMemory)
    (hValid : validCallerMemory cm = true) :
    ∀ aid a, findAllocation aid (entryMemoryWithCaller cm).allocations = some a →
      a.bytes.length < isizeMaxBytes :=
  fun _ a hFind =>
    allocIdsValid_bytes_lt [] cm.allocations hValid a (findAllocation_mem hFind)

private theorem isSliceAllInit_take_le :
    ∀ (xs : List AllocByte) (n m : Nat),
      m ≤ n → isSliceAllInit (xs.take n) = true →
      isSliceAllInit (xs.take m) = true
  | _, _, 0, _, _ => rfl
  | [], _, _ + 1, _, _ => by rw [List.take_nil]; rfl
  | .uninit :: _, _ + 1, _ + 1, _, h => by cases h
  | .init _ _ :: xs, n + 1, m + 1, hLe, h =>
    isSliceAllInit_take_le xs n m (Nat.le_of_succ_le_succ hLe) h
  | _ :: _, 0, m + 1, hLe, _ => False.elim (Nat.not_succ_le_zero m hLe)

private theorem isSliceAllInit_drop_take :
    ∀ (bs : List AllocByte) (off len start subLen : Nat),
      start + subLen ≤ len →
      isSliceAllInit ((bs.drop off).take len) = true →
      isSliceAllInit ((bs.drop (off + start)).take subLen) = true
  | [], _, _, _, _, _, _ => by rw [List.drop_nil, List.take_nil]; rfl
  | _ :: bs, o + 1, len, start, subLen, hSub, hInit => by
    rw [Nat.succ_add o start]
    exact isSliceAllInit_drop_take bs o len start subLen hSub hInit
  | b :: bs, 0, len, 0, subLen, hSub, hInit => by
    rw [Nat.zero_add] at hSub ⊢
    exact isSliceAllInit_take_le (b :: bs) len subLen hSub hInit
  | _ :: _, 0, 0, s + 1, subLen, hSub, _ => by
    have hFalse : s + 1 + subLen ≤ 0 := hSub
    exact False.elim (Nat.not_succ_le_zero (s + subLen)
      (by rw [Nat.succ_add] at hFalse; exact hFalse))
  | .uninit :: _, 0, _ + 1, _, _, _, hInit => by cases hInit
  | .init _ _ :: bs, 0, l + 1, s + 1, subLen, hSub, hInit => by
    have hSub' : s + subLen ≤ l := by
      have h1 : (s + subLen) + 1 ≤ l + 1 := by
        rw [Nat.succ_add] at hSub
        exact hSub
      exact Nat.le_of_succ_le_succ h1
    rw [Nat.zero_add]
    have hRec := isSliceAllInit_drop_take bs 0 l s subLen hSub' hInit
    rw [Nat.zero_add] at hRec
    exact hRec

private theorem sliceFromRawPartsCheck_ok_val
    {m : MemoryState} {isMut : Bool} {es ea : Nat} {p : PtrVal}
    {len : UInt64} {v : Val}
    (h : sliceFromRawPartsCheck m isMut es ea p len = .ok v) :
    v = .slicePtr p len := by
  unfold sliceFromRawPartsCheck at h
  cases hRaw : sliceRefRawCheck m isMut es ea p len with
  | error k => rw [hRaw] at h; cases h
  | ok optAlloc =>
    rw [hRaw] at h
    cases optAlloc with
    | none => injection h with hv; exact hv.symm
    | some a =>
      dsimp only at h
      cases hInit : (!isSliceAllInit
          ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * es))) with
      | true => rw [hInit] at h; cases h
      | false => rw [hInit] at h; injection h with hv; exact hv.symm

private theorem layoutOfTyV2_u8 :
    layoutOfTyV2 (.int .i8 false) = some ⟨1, 0⟩ := rfl

private theorem layoutOfTyV2_u64 :
    layoutOfTyV2 (.int .i64 false) = some ⟨8, 3⟩ := rfl

private theorem layoutOfTyV2_opt_u64 :
    layoutOfTyV2 (.option (.int .i64 false)) = some ⟨16, 3⟩ := rfl

private theorem sliceCheck_of_refValidInMem {m : MemoryState}
    {reqMut : Mutability} {ptr : PtrVal} {len : UInt64}
    (hValid : refValidInMem m reqMut (.slice (.int .i8 false))
      (.slicePtr ptr len) = .ok ()) :
    sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len =
      .ok (.slicePtr ptr len) := by
  unfold refValidInMem at hValid
  dsimp only at hValid
  rw [ite_bool_false (b := !isSizedNoRefV2Ty (.int .i8 false)) rfl] at hValid
  rw [layoutOfTyV2_u8] at hValid
  dsimp only at hValid
  cases hChk : sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len with
  | error k => rw [hChk] at hValid; cases hValid
  | ok _ =>
    have hv := sliceFromRawPartsCheck_ok_val hChk
    subst hv
    rfl

private theorem refValidInMem_of_sliceCheck {m : MemoryState}
    {reqMut : Mutability} {ptr : PtrVal} {len : UInt64}
    (hChk : sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len =
      .ok (.slicePtr ptr len)) :
    refValidInMem m reqMut (.slice (.int .i8 false)) (.slicePtr ptr len) =
      .ok () := by
  unfold refValidInMem
  dsimp only
  rw [ite_bool_false (b := !isSizedNoRefV2Ty (.int .i8 false)) rfl]
  rw [layoutOfTyV2_u8]
  dsimp only
  rw [hChk]

private theorem sliceFromRawPartsCheck_u8_to_subslice
    {m : MemoryState} {isMut isMutOut : Bool} {ptr : PtrVal} {len : UInt64}
    {start subLen : Nat}
    (hAllocLt : ∀ aid a, findAllocation aid m.allocations = some a →
      a.bytes.length < isizeMaxBytes)
    (hMut : isMutOut = false ∨ isMut = true)
    (hOrig : sliceFromRawPartsCheck m isMut 1 0 ptr len = .ok (.slicePtr ptr len))
    (hSub : start + subLen ≤ len.toNat) :
    ∃ pSub : PtrVal,
      ptrAddInMem m 1 ptr start = .ok pSub ∧
      sliceFromRawPartsCheck m isMutOut 1 0 pSub (UInt64.ofNat subLen) =
        .ok (.slicePtr pSub (UInt64.ofNat subLen)) ∧
      pSub.allocId = ptr.allocId ∧
      pSub.width = ptr.width ∧
      (match ptr.allocId with
        | none => pSub = ptr
        | some _ =>
          pSub = { ptr with
            offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + start) } ∧
          ptr.offsetBytes.toNat + start < Nat.pow 2 64 ∧
          pSub.offsetBytes.toNat = ptr.offsetBytes.toNat + start) := by
  unfold sliceFromRawPartsCheck at hOrig
  cases hRawOrig : sliceRefRawCheck m isMut 1 0 ptr len with
  | error k => rw [hRawOrig] at hOrig; cases hOrig
  | ok optOrig =>
    rw [hRawOrig] at hOrig
    unfold sliceRefRawCheck at hRawOrig
    dsimp only at hRawOrig
    rw [Nat.mul_one] at hRawOrig
    cases hMax : Nat.blt len.toNat isizeMaxBytes with
    | false => rw [hMax] at hRawOrig; cases hRawOrig
    | true =>
      rw [hMax] at hRawOrig
      have hLenLtMax : len.toNat < isizeMaxBytes := lt_of_blt_true hMax
      have hStartLtMax : start < isizeMaxBytes :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right start subLen) hSub) hLenLtMax
      have hSubLtMax : subLen < isizeMaxBytes :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left subLen start) hSub) hLenLtMax
      have hSubU64 : (UInt64.ofNat subLen).toNat = subLen :=
        toNat_uint64_ofNat_lt (Nat.lt_trans hSubLtMax (by decide))
      cases hAid : ptr.allocId with
      | none =>
        rw [hAid] at hRawOrig; dsimp only at hRawOrig
        cases hZero : Nat.beq ptr.offsetBytes.toNat 0 with
        | true => rw [hZero] at hRawOrig; cases hRawOrig
        | false =>
          cases hLenPos : Nat.blt 0 len.toNat with
          | true => rw [hZero, hLenPos] at hRawOrig; cases hRawOrig
          | false =>
            have hLenZero : len.toNat = 0 := by
              cases hN : len.toNat with
              | zero => rfl
              | succ k =>
                have hPos : Nat.blt 0 (k + 1) = true :=
                  blt_true_of_lt (Nat.zero_lt_succ k)
                rw [hN] at hLenPos; cases hLenPos.symm.trans hPos
            have hSum0 : start + subLen = 0 :=
              Nat.eq_zero_of_le_zero (hLenZero ▸ hSub)
            have hStart0 : start = 0 :=
              Nat.eq_zero_of_le_zero
                (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hSum0))
            have hSub0 : subLen = 0 :=
              Nat.eq_zero_of_le_zero
                (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hSum0))
            subst hStart0; subst hSub0
            refine ⟨ptr, ?_, ?_, hAid, rfl, ?_⟩
            · change (if !Nat.blt (0 * 1) isizeMaxBytes then
                  Except.error FaultKind.undefined else
                match ptr.allocId with
                | none => if Nat.beq (0 * 1) 0 then Except.ok ptr else
                    Except.error FaultKind.undefined
                | some aid =>
                  match findAllocation aid m.allocations with
                  | none => Except.error FaultKind.undefined
                  | some a =>
                    if !a.live ||
                        !Nat.ble (ptr.offsetBytes.toNat + 0 * 1) a.bytes.length then
                      Except.error FaultKind.undefined
                    else Except.ok { ptr with
                      offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + 0 * 1) }) =
                  .ok ptr
              rw [Nat.mul_one]
              have hZeroLtMax : Nat.blt 0 isizeMaxBytes = true := by decide
              rw [hZeroLtMax, ite_bool_false (by decide), hAid]
              rfl
            · unfold sliceFromRawPartsCheck sliceRefRawCheck
              dsimp only
              rw [Nat.mul_one, hSubU64]
              have hZeroLtMax : Nat.blt 0 isizeMaxBytes = true := by decide
              have hPow0 : Nat.pow 2 0 = 1 := rfl
              have hMod1 : Nat.mod ptr.offsetBytes.toNat 1 = 0 := Nat.mod_one _
              rw [hZeroLtMax, ite_bool_false (by decide), hAid, hZero,
                hPow0, hMod1]
              rfl
            · dsimp only
      | some aid =>
        rw [hAid] at hRawOrig; dsimp only at hRawOrig
        cases hFind : findAllocation aid m.allocations with
        | none => rw [hFind] at hRawOrig; cases hRawOrig
        | some a =>
          rw [hFind] at hRawOrig; dsimp only at hRawOrig
          cases hLive : a.live with
          | false => rw [hLive] at hRawOrig; cases hRawOrig
          | true =>
            rw [hLive] at hRawOrig
            cases hBounds : isInBounds a ptr.offsetBytes.toNat len.toNat with
            | false => rw [hBounds] at hRawOrig; cases hRawOrig
            | true =>
              rw [hBounds] at hRawOrig
              cases hAlign : isAligned a ptr.offsetBytes.toNat 0 with
              | false => rw [hAlign] at hRawOrig; cases hRawOrig
              | true =>
                rw [hAlign] at hRawOrig
                cases hMutChk : (isMut && !Mutability.beq a.mutability .mut) with
                | true => rw [hMutChk] at hRawOrig; cases hRawOrig
                | false =>
                  rw [hMutChk] at hRawOrig
                  cases hRawOrig
                  dsimp only at hOrig
                  rw [Nat.mul_one] at hOrig
                  cases hInit : isSliceAllInit
                      ((a.bytes.drop ptr.offsetBytes.toNat).take len.toNat) with
                  | false => rw [hInit] at hOrig; cases hOrig
                  | true =>
                    have hBoundsNat : ptr.offsetBytes.toNat + len.toNat ≤ a.bytes.length :=
                      Nat.le_of_ble_eq_true hBounds
                    have hStartIn : ptr.offsetBytes.toNat + start ≤ a.bytes.length :=
                      Nat.le_trans (Nat.add_le_add_left
                        (Nat.le_trans (Nat.le_add_right _ _) hSub) _) hBoundsNat
                    have hEndIn :
                        ptr.offsetBytes.toNat + start + subLen ≤ a.bytes.length :=
                      Nat.le_trans
                        (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hSub _)
                        hBoundsNat
                    have hStartLt64 : ptr.offsetBytes.toNat + start < Nat.pow 2 64 :=
                      Nat.lt_trans
                        (Nat.lt_of_le_of_lt hStartIn (hAllocLt aid a hFind)) (by decide)
                    let pSub : PtrVal :=
                      { ptr with
                        offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + start) }
                    have hPSubOff :
                        pSub.offsetBytes.toNat = ptr.offsetBytes.toNat + start :=
                      toNat_uint64_ofNat_lt hStartLt64
                    refine ⟨pSub, ?_, ?_, hAid, rfl, ?_⟩
                    · change (if !Nat.blt (start * 1) isizeMaxBytes then
                          Except.error FaultKind.undefined else
                        match ptr.allocId with
                        | none => if Nat.beq (start * 1) 0 then Except.ok ptr else
                            Except.error FaultKind.undefined
                        | some aid' =>
                          match findAllocation aid' m.allocations with
                          | none => Except.error FaultKind.undefined
                          | some a' =>
                            if !a'.live ||
                                !Nat.ble (ptr.offsetBytes.toNat + start * 1)
                                  a'.bytes.length then
                              Except.error FaultKind.undefined
                            else Except.ok { ptr with
                              offsetBytes := UInt64.ofNat
                                (ptr.offsetBytes.toNat + start * 1) }) =
                          .ok pSub
                      rw [Nat.mul_one, blt_true_of_lt hStartLtMax,
                        ite_bool_false (by decide), hAid]
                      dsimp only; rw [hFind]; dsimp only
                      rw [hLive, Nat.ble_eq_true_of_le hStartIn,
                        ite_bool_false (by decide)]
                      dsimp only [pSub]; rw [hAid]
                    · unfold sliceFromRawPartsCheck sliceRefRawCheck
                      dsimp only
                      rw [Nat.mul_one, hSubU64, blt_true_of_lt hSubLtMax,
                        ite_bool_false (by decide)]
                      have hPSubAid : pSub.allocId = some aid := hAid
                      rw [hPSubAid]; dsimp only; rw [hFind]; dsimp only
                      rw [hLive, hPSubOff]
                      have hInB :
                          isInBounds a (ptr.offsetBytes.toNat + start) subLen = true :=
                        Nat.ble_eq_true_of_le hEndIn
                      have hAl0 :
                          isAligned a (ptr.offsetBytes.toNat + start) 0 = true := by
                        unfold isAligned
                        have hPow0 : Nat.pow 2 0 = 1 := rfl
                        have hMod1 :
                            Nat.mod (ptr.offsetBytes.toNat + start) 1 = 0 :=
                          Nat.mod_one _
                        rw [Nat.ble_eq_true_of_le (Nat.zero_le a.alignLog2),
                          hPow0, hMod1, Nat.beq_refl]
                        rfl
                      have hMutOk :
                          (isMutOut && !Mutability.beq a.mutability .mut) = false := by
                        cases isMutOut with
                        | false => rfl
                        | true =>
                          cases hMut with
                          | inl hF => cases hF
                          | inr hT => subst hT; exact hMutChk
                      have hInitSub :
                          isSliceAllInit
                            ((a.bytes.drop (ptr.offsetBytes.toNat + start)).take subLen) =
                          true :=
                        isSliceAllInit_drop_take a.bytes ptr.offsetBytes.toNat len.toNat
                          start subLen hSub hInit
                      rw [hInB, hAl0, hMutOk,
                        ite_bool_false (rfl : (!true || !true || !true) = false),
                        ite_bool_false (rfl : false = false)]
                      dsimp only
                      rw [hInitSub]
                      rfl
                    · dsimp only
                      refine ⟨?_, hStartLt64, hPSubOff⟩
                      dsimp only [pSub]
                      rw [hAid]

private theorem refsStayInCallerMem_of_slice {cm : CallerMemory} {isMut : Bool}
    {ptr pOut : PtrVal} {len outLen : UInt64} {reqMut : Mutability}
    (hOrig : sliceFromRawPartsCheck (entryMemoryWithCaller cm) isMut 1 0 ptr len =
      .ok (.slicePtr ptr len))
    (hAllocEq : pOut.allocId = ptr.allocId) :
    refsStayInCallerMem cm (.ref reqMut (.slice (.int .i8 false)))
      (.slicePtr pOut outLen) = true := by
  unfold refsStayInCallerMem refAllocIds
  rw [hAllocEq]
  cases hAid : ptr.allocId with
  | none => rfl
  | some aid =>
    unfold sliceFromRawPartsCheck at hOrig
    cases hRaw : sliceRefRawCheck (entryMemoryWithCaller cm) isMut 1 0 ptr len with
    | error k => rw [hRaw] at hOrig; cases hOrig
    | ok _ =>
      unfold sliceRefRawCheck at hRaw
      dsimp only at hRaw
      cases hMax : Nat.blt (len.toNat * 1) isizeMaxBytes with
      | false => rw [hMax] at hRaw; cases hRaw
      | true =>
        rw [hMax, hAid] at hRaw
        dsimp only at hRaw
        cases hFind : findAllocation aid (entryMemoryWithCaller cm).allocations with
        | none => rw [hFind] at hRaw; cases hRaw
        | some a =>
          have hSome : (findAllocation aid cm.allocations).isSome = true := by
            change (findAllocation aid
              (entryMemoryWithCaller cm).allocations).isSome = true
            rw [hFind]; rfl
          change ((findAllocation aid cm.allocations).isSome && true) = true
          rw [hSome]; rfl

private theorem hasEscapingRodataPtr_of_slice {cm : CallerMemory}
    {mem : MemoryState} {isMut : Bool} {ptr pOut : PtrVal}
    {len outLen : UInt64} {reqMut : Mutability}
    (hOrig : sliceFromRawPartsCheck (entryMemoryWithCaller cm) isMut 1 0 ptr len =
      .ok (.slicePtr ptr len))
    (hAllocEq : pOut.allocId = ptr.allocId) :
    hasEscapingRodataPtr cm mem (.ref reqMut (.slice (.int .i8 false)))
      (.slicePtr pOut outLen) = false := by
  unfold hasEscapingRodataPtr ptrOrRefAllocIds
  rw [hAllocEq]
  cases hAid : ptr.allocId with
  | none => rfl
  | some aid =>
    unfold sliceFromRawPartsCheck at hOrig
    cases hRaw : sliceRefRawCheck (entryMemoryWithCaller cm) isMut 1 0 ptr len with
    | error k => rw [hRaw] at hOrig; cases hOrig
    | ok _ =>
      unfold sliceRefRawCheck at hRaw
      dsimp only at hRaw
      cases hMax : Nat.blt (len.toNat * 1) isizeMaxBytes with
      | false => rw [hMax] at hRaw; cases hRaw
      | true =>
        rw [hMax, hAid] at hRaw
        dsimp only at hRaw
        cases hFind : findAllocation aid (entryMemoryWithCaller cm).allocations with
        | none => rw [hFind] at hRaw; cases hRaw
        | some a =>
          have hFindCm : findAllocation aid cm.allocations = some a := hFind
          change (isRodataAllocId cm mem aid || false) = false
          unfold isRodataAllocId
          rw [hFindCm]
          rfl

/-! ## Body 0: `subslice` (`&s[a..b]`) -/

private theorem execCoreCall_sliceIndexRange_u8_ok {m : MemoryState}
    {p pOut : PtrVal} {len : UInt64} {a b : Nat}
    (hRef : refValidInMem m .shared (.slice (.int .i8 false))
      (.slicePtr p len) = .ok ())
    (hAB : a ≤ b) (hBLen : b ≤ len.toNat)
    (hAdd : ptrAddInMem m 1 p a = .ok pOut) :
    execCoreCallWithMem m
        (.sliceIndexRange .shared (.int .i8 false))
        [(.ref .shared (.slice (.int .i8 false)), .slicePtr p len),
         (.range (.int .isize false),
          .range (UInt64.ofNat a) (UInt64.ofNat b))]
        (.ref .shared (.slice (.int .i8 false))) =
      .ok (.slicePtr pOut (UInt64.ofNat (b - a)), m) := by
  dsimp only [execCoreCallWithMem, execCoreContractOp]
  rw [ite_bool_false (by decide)]
  unfold execSliceSubslice
  rw [ite_bool_false (b := !isSizedNoRefV2Ty (.int .i8 false)) (by decide)]
  rw [ite_bool_false (by decide)]
  rw [hRef]; dsimp only
  have hALt64 : a < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans hAB hBLen) len.toBitVec.isLt
  have hBLt64 : b < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt hBLen len.toBitVec.isLt
  rw [toNat_uint64_ofNat_lt hALt64, toNat_uint64_ofNat_lt hBLt64]
  rw [Nat.ble_eq_true_of_le hAB, Nat.ble_eq_true_of_le hBLen]
  rw [ite_bool_false (by decide)]
  rw [layoutOfTyV2_u8]; dsimp only
  rw [hAdd]

private theorem checkArgsMatchV2_subslice_inv {args : List Val}
    (h : checkArgsMatchV2 args
      [.ref .shared (.slice (.int .i8 false)),
       .int .isize false, .int .isize false] = true) :
    ∃ (ptr : PtrVal) (len : UInt64) (aBits bBits : BitVec 128),
      args = [.slicePtr ptr len, .scalar ⟨.isize, false, aBits⟩,
        .scalar ⟨.isize, false, bBits⟩] ∧
      ptr.width = .isize ∧
      truncateBits .isize aBits = aBits ∧
      truncateBits .isize bBits = bBits := by
  cases args with
  | nil => cases h
  | cons v0 r0 =>
    cases r0 with
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) <;>
        rw [h0] at h <;> cases h
    | cons v1 r1 =>
      cases r1 with
      | nil =>
        dsimp only [checkArgsMatchV2] at h
        cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) <;>
          rw [h0] at h
        · cases h
        · cases h1 : checkValV2 v1 (.int .isize false) <;>
            rw [h1] at h <;> cases h
      | cons v2 r2 =>
        cases r2 with
        | cons _ _ =>
          dsimp only [checkArgsMatchV2] at h
          cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) <;>
            rw [h0] at h
          · cases h
          · cases h1 : checkValV2 v1 (.int .isize false) <;> rw [h1] at h
            · cases h
            · cases h2 : checkValV2 v2 (.int .isize false) <;>
                rw [h2] at h <;> cases h
        | nil =>
          dsimp only [checkArgsMatchV2] at h
          cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) with
          | false => rw [h0] at h; cases h
          | true =>
            rw [h0] at h
            cases h1 : checkValV2 v1 (.int .isize false) with
            | false => rw [h1] at h; cases h
            | true =>
              rw [h1] at h
              cases h2 : checkValV2 v2 (.int .isize false) with
              | false => rw [h2] at h; cases h
              | true =>
                cases v0 with
                | slicePtr ptr len =>
                  have hW : ptr.width = .isize := by
                    change IntWidth.beq ptr.width .isize = true at h0
                    cases hPw : ptr.width with
                    | isize => rfl
                    | i8 | i16 | i32 | i64 | i128 => rw [hPw] at h0; cases h0
                  cases v1 with
                  | scalar aSv =>
                    let ⟨aBits, haEq, haT⟩ := checkVal_int_iff.mp
                      (show checkVal (.scalar aSv) (.int .isize false) = true
                        from h1)
                    injection haEq with haSv; subst haSv
                    cases v2 with
                    | scalar bSv =>
                      let ⟨bBits, hbEq, hbT⟩ := checkVal_int_iff.mp
                        (show checkVal (.scalar bSv) (.int .isize false) = true
                          from h2)
                      injection hbEq with hbSv; subst hbSv
                      exact ⟨ptr, len, aBits, bBits, rfl, hW, haT, hbT⟩
                    | optionVal optV => cases optV <;> cases h2
                    | _ => cases h2
                  | optionVal optV => cases optV <;> cases h1
                  | _ => cases h1
                | optionVal optV => cases optV <;> cases h0
                | _ => cases h0

private theorem subslice_pOut_eq {ptr pOut : PtrVal} {aBits : BitVec 128}
    (hSpec : match ptr.allocId with
      | none => pOut = ptr
      | some _ =>
        pOut = { ptr with
          offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + aBits.toNat) } ∧
        ptr.offsetBytes.toNat + aBits.toNat < Nat.pow 2 64 ∧
        pOut.offsetBytes.toNat = ptr.offsetBytes.toNat + aBits.toNat) :
    pOut =
      match ptr.allocId with
      | none => ptr
      | some _ =>
        { ptr with
          offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + aBits.toNat) } := by
  cases hAid : ptr.allocId with
  | none => rw [hAid] at hSpec; exact hSpec
  | some _ => rw [hAid] at hSpec; exact hSpec.1

private theorem subslice_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hSafe : Spec.subsliceSafety q) :
    match q.args with
    | [.slicePtr ptr _, .scalar aSv, .scalar bSv] =>
      let pOut :=
        match ptr.allocId with
        | none => ptr
        | some _ =>
          { ptr with
            offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + aSv.bits.toNat) }
      let outLen := UInt64.ofNat (bSv.bits.toNat - aSv.bits.toNat)
      WellFormedV2 (entryProgForBody Captured.program 0) q ∧
      BehaviorV2 (entryProgForBody Captured.program 0) q
        (TerminalOut.returned ⟨.slicePtr pOut outLen, q.callerMem⟩)
    | _ => False := by
  unfold ValidEntryArgsV2 at hValid
  let ⟨hCM, hMatch, hRefs, hDisj⟩ := hValid
  let ⟨ptr, len, aBits, bBits, hArgs, hPtrW, hATr, hBTr⟩ :=
    checkArgsMatchV2_subslice_inv hMatch
  unfold Spec.subsliceSafety at hSafe
  rw [hArgs] at hSafe
  let ⟨hALeB, hBLeLen⟩ := hSafe
  cases ptr with
  | mk ptrAid ptrOff ptrW =>
    dsimp only at hPtrW; subst hPtrW
    let m : MemoryState := entryMemoryWithCaller q.callerMem
    have hQ : q = ⟨[.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
        .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩],
        q.callerMem⟩ := by
      cases q; dsimp only at hArgs; rw [hArgs]
    have hRefValid0 :
        refValidInMem m .shared (.slice (.int .i8 false))
          (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len) = .ok () := by
      have hRefs' :
          refsValidInMemList m
            [.ref .shared (.slice (.int .i8 false)),
             .int .isize false, .int .isize false]
            [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
             .scalar ⟨.isize, false, aBits⟩,
             .scalar ⟨.isize, false, bBits⟩] = true := by
        rw [← hArgs]; exact hRefs
      dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
      cases hR : refValidInMem m .shared (.slice (.int .i8 false))
          (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len) with
      | error k => rw [hR] at hRefs'; cases hRefs'
      | ok u => cases u; rfl
    have hOrig := sliceCheck_of_refValidInMem hRefValid0
    have hAllocLt := entryMemoryWithCaller_bytes_lt q.callerMem hCM
    have hSub : aBits.toNat + (bBits.toNat - aBits.toNat) ≤ len.toNat := by
      rw [Nat.add_sub_of_le hALeB]; exact hBLeLen
    let ⟨pOut, hPtrAdd, hSliceOut, hOutAid, hOutW, hOutSpec⟩ :=
      sliceFromRawPartsCheck_u8_to_subslice hAllocLt (.inl rfl) hOrig hSub
    have hPOutEq := subslice_pOut_eq hOutSpec
    let outLen := UInt64.ofNat (bBits.toNat - aBits.toNat)
    have hRefValidOut :
        refValidInMem m .shared (.slice (.int .i8 false))
          (.slicePtr pOut outLen) = .ok () :=
      refValidInMem_of_sliceCheck hSliceOut
    have hRefsOut :
        refsValidInMem m (.ref .shared (.slice (.int .i8 false)))
          (.slicePtr pOut outLen) = true := by
      dsimp only [refsValidInMem]; rw [hRefValidOut]
    have hStay := refsStayInCallerMem_of_slice hOrig hOutAid (outLen := outLen)
      (reqMut := .shared)
    have hExt := extractCallerMemory_entry q.callerMem hCM
    have hAChk : checkValV2 (.scalar ⟨.isize, false, aBits⟩)
        (.int .isize false) = true := checkVal_int_eq hATr
    have hBChk : checkValV2 (.scalar ⟨.isize, false, bBits⟩)
        (.int .isize false) = true := checkVal_int_eq hBTr
    have hInit : initStateV2 (entryProgForBody Captured.program 0) q =
        .ok ⟨[⟨0, 0, 0, [
          .immediate none,
          .immediate (some (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len)),
          .immediate (some (.scalar ⟨.isize, false, aBits⟩)),
          .immediate (some (.scalar ⟨.isize, false, bBits⟩)),
          .dead, .dead, .dead, .dead, .dead, .dead
        ], none, none, none⟩], q.callerMem, m⟩ := by
      rw [hQ]
      have hChkArgs : checkArgsMatchV2
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
           .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩]
          ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount) =
          true := by
        change checkArgsMatchV2
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
           .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩]
          [.ref .shared (.slice (.int .i8 false)),
           .int .isize false, .int .isize false] = true
        dsimp only [checkArgsMatchV2]; rw [hAChk, hBChk]; rfl
      have hRefsList : refsValidInMemList m
          ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount)
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
           .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩] =
          true := by
        change refsValidInMemList m
          [.ref .shared (.slice (.int .i8 false)),
           .int .isize false, .int .isize false]
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
           .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩] =
          true
        dsimp only [refsValidInMemList, refsValidInMem]
        rw [hRefValid0]; rfl
      have hDisjList : spansPairwiseDisjoint (refAccessSpansList
          ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount)
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
           .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩]) =
          true := by
        change spansPairwiseDisjoint (refAccessSpansList
          [.ref .shared (.slice (.int .i8 false)),
           .int .isize false, .int .isize false]
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
           .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩]) =
          true
        dsimp only [refAccessSpansList, refAccessSpans]
        cases ptrAid <;> rfl
      have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 0)
        (q := ⟨[.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len,
          .scalar ⟨.isize, false, aBits⟩, .scalar ⟨.isize, false, bBits⟩],
          q.callerMem⟩)
        (body := Captured.body_0)
        rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hChkArgs hRefsList hDisjList
      rw [h0]; rfl
    have hExec : execProgV2 (entryProgForBody Captured.program 0) 25 q
        (fun o => o = .returned ⟨.slicePtr pOut outLen, q.callerMem⟩) := by
      unfold execProgV2
      rw [hInit]
      -- bb0 stmts 0..2: storageLive 4, 5, 6
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 stmt 3: assign 6 (.ref .shared [1, .deref])
      apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
        (evalRvalueV2_ref_deref_ok rfl rfl rfl rfl hRefValid0)
        (writePlaceV2_immediate_ok rfl rfl rfl))
      -- bb0 stmts 4..5: storageLive 7, 8
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 stmt 6: assign 8 (.use (.copy 2))
      apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
        (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
        (writePlaceV2_immediate_ok hAChk rfl rfl))
      -- bb0 stmt 7: storageLive 9
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 stmt 8: assign 9 (.use (.copy 3))
      apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
        (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
        (writePlaceV2_immediate_ok hBChk rfl rfl))
      -- bb0 stmt 9: assign 7 (.aggregateRange isize (move 8) (move 9))
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program,
          Captured.body_0, evalStatementV2, placeStaticTyV2,
          resolvePlaceDestV2, writePlaceDestV2, evalRvalueV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local rfl rfl rfl rfl]
        dsimp only
        rw [readPlaceV2_move_local rfl rfl rfl rfl]
        rfl)
      -- bb0 stmts 10..11: storageDead 9, 8
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 term: coreCall sliceIndexRange [move 6, move 7] -> 5, bb1
      apply execOutcomeStateV2_step (evalStepV2_coreCall_ok rfl rfl rfl rfl rfl
        rfl rfl
        (evalArgOperandsV2_two_move rfl rfl rfl rfl rfl rfl rfl rfl)
        (execCoreCall_sliceIndexRange_u8_ok hRefValid0 hALeB hBLeLen hPtrAdd)
        (writePlaceV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hOutW]; rfl) rfl rfl))
      -- bb1 stmts 0..1: storageDead 7, 6
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 stmt 2: assign 4 (.ref .shared [5, .deref])
      apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
        (evalRvalueV2_ref_deref_ok rfl rfl rfl rfl hRefValidOut)
        (writePlaceV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hOutW]; rfl) rfl rfl))
      -- bb1 stmt 3: assign 0 (.ref .shared [4, .deref])
      apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
        (evalRvalueV2_ref_deref_ok rfl rfl rfl rfl hRefValidOut)
        (writePlaceV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hOutW]; rfl) rfl rfl))
      -- bb1 stmts 4..5: storageDead 5, 4
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 term: return_
      apply execOutcomeStateV2_done (by
        apply evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
          (hasEscapingRodataPtr_of_slice hOrig hOutAid) hStay hRefsOut
        dsimp only [refAccessSpans]
        cases hOutAid' : pOut.allocId <;> rfl)
      · rw [hExt]
    let ⟨hWf, hBeh, _⟩ := spec_and_behaviorV2_of_exec_eq hExec
    rw [hArgs]
    dsimp only
    rw [← hPOutEq]
    exact ⟨hWf, hBeh⟩

/-! ## Body 1: `opt_unwrap` (`Option<u64>::unwrap`) -/

private theorem execCoreCall_optionUnwrap_u64_ok {m : MemoryState} {v : Val} :
    execCoreCallWithMem m (.optionUnwrap (.int .i64 false))
      [(.option (.int .i64 false), .optionVal (some v))] (.int .i64 false) =
      .ok (v, m) := by
  unfold execCoreCallWithMem execCoreContractOp
  dsimp only
  cases v <;> rfl

private theorem opt_unwrap_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q)
    (hSafe : Spec.optUnwrapSafety q) :
    match q.args with
    | [.optionVal (some v)] =>
      WellFormedV2 (entryProgForBody Captured.program 1) q ∧
      BehaviorV2 (entryProgForBody Captured.program 1) q
        (TerminalOut.returned ⟨v, q.callerMem⟩)
    | _ => False := by
  let ⟨hCM, hMatch, _, _⟩ := hValid
  unfold Spec.optUnwrapSafety at hSafe
  cases hArgs : q.args with
  | nil => rw [hArgs] at hSafe; exact False.elim hSafe
  | cons a0 r0 =>
    cases r0 with
    | cons _ _ =>
      rw [hArgs] at hMatch
      rw [show (Captured.body_1.locals.drop 1).take Captured.body_1.argumentCount =
          [.option (.int .i64 false)] from rfl] at hMatch
      dsimp only [checkArgsMatchV2] at hMatch
      rw [Bool.and_false] at hMatch
      cases hMatch
    | nil =>
      rw [hArgs] at hSafe
      cases a0 with
      | optionVal optV =>
        cases optV with
        | none => exact False.elim hSafe
        | some v =>
          have hChkOpt :
              checkValV2 (.optionVal (some v)) (.option (.int .i64 false)) =
              true := by
            rw [hArgs] at hMatch
            have hMatch' : (checkValV2 (.optionVal (some v))
                (.option (.int .i64 false)) && decide (true = true)) = true :=
              hMatch
            rw [show decide (true = true) = true from rfl, Bool.and_true]
              at hMatch'
            exact hMatch'
          have hChkV : checkValV2 v (.int .i64 false) = true := hChkOpt
          have hVSc : ∃ bits, v = .scalar ⟨.i64, false, bits⟩ ∧
              truncateBits .i64 bits = bits := by
            cases v with
            | scalar sv =>
              let ⟨bits, hEq, hT⟩ := checkVal_int_iff.mp
                (show checkVal (.scalar sv) (.int .i64 false) = true from hChkV)
              injection hEq with hSv; subst hSv
              exact ⟨bits, rfl, hT⟩
            | optionVal optV' => cases optV' <;> cases hChkV
            | _ => cases hChkV
          let ⟨vBits, hvEq, hvTr⟩ := hVSc
          subst hvEq
          let m := entryMemoryWithCaller q.callerMem
          have hQ : q = ⟨[.optionVal (some (.scalar ⟨.i64, false, vBits⟩))],
              q.callerMem⟩ := by
            cases q; dsimp only at hArgs; rw [hArgs]
          have hExt := extractCallerMemory_entry q.callerMem hCM
          have hVChk : checkValV2 (.scalar ⟨.i64, false, vBits⟩)
              (.int .i64 false) = true := checkVal_int_eq hvTr
          have hInit : initStateV2 (entryProgForBody Captured.program 1) q =
              .ok ⟨[⟨1, 0, 0, [
                .immediate none,
                .immediate (some (.optionVal (some (.scalar ⟨.i64, false, vBits⟩)))),
                .dead
              ], none, none, none⟩], q.callerMem, m⟩ := by
            rw [hQ]
            have hChkArgs : checkArgsMatchV2
                [.optionVal (some (.scalar ⟨.i64, false, vBits⟩))]
                ((Captured.body_1.locals.drop 1).take
                  Captured.body_1.argumentCount) = true := by
              change checkValV2 (.scalar ⟨.i64, false, vBits⟩)
                  (.int .i64 false) && true = true
              rw [hVChk]; rfl
            have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 1)
              (q := ⟨[.optionVal (some (.scalar ⟨.i64, false, vBits⟩))],
                q.callerMem⟩)
              (body := Captured.body_1)
              rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) hChkArgs rfl rfl
            rw [h0]; rfl
          have hExec : execProgV2 (entryProgForBody Captured.program 1) 8 q
              (fun o => o = .returned
                ⟨.scalar ⟨.i64, false, vBits⟩, q.callerMem⟩) := by
            unfold execProgV2
            rw [hInit]
            -- bb0 stmt 0: storageLive 2
            apply execOutcomeStateV2_step (by rfl)
            -- bb0 stmt 1: assign 2 (.use (.copy 1))
            apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
              (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
              (writePlaceV2_immediate_ok hChkOpt rfl rfl))
            -- bb0 term: coreCall optionUnwrap [move 2] -> 0, bb1
            apply execOutcomeStateV2_step (evalStepV2_coreCall_ok rfl rfl rfl rfl
              rfl rfl rfl
              (evalArgOperandsV2_one_move rfl rfl rfl rfl)
              execCoreCall_optionUnwrap_u64_ok
              (writePlaceV2_immediate_ok hVChk rfl rfl))
            -- bb1 stmt 0: storageDead 2
            apply execOutcomeStateV2_step (by rfl)
            -- bb1 term: return_
            apply execOutcomeStateV2_done
              (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
            · rw [hExt]
          let ⟨hWf, hBeh, _⟩ := spec_and_behaviorV2_of_exec_eq hExec
          exact ⟨hWf, hBeh⟩
      | _ => exact False.elim hSafe

/-! ## Body 2: `checked_scalar` (Safe Core Scalar Contracts) -/

private theorem body2_locals_eq :
    Captured.body_2.locals = [
      .tuple [.bool, .int .i64 false, .int .i32 false],
      .int .i64 false, .int .i64 false, .int .i32 false,
      .int .i64 false, .option (.int .i64 false),
      .int .i64 false, .int .i64 false, .int .isize true,
      .int .i64 false, .int .i64 false, .int .i64 false,
      .bool, .int .i64 false, .int .i64 false, .int .i64 false,
      .int .i64 false, .int .i32 false, .int .i64 false,
      .int .i64 false, .int .i32 false
    ] := rfl

private theorem initLocalsLoop_body2 (aBits bBits sBits : BitVec 128) :
    initLocalsLoop Captured.body_2
      [.scalar ⟨.i64, false, aBits⟩, .scalar ⟨.i64, false, bBits⟩,
       .scalar ⟨.i32, false, sBits⟩]
      0 Captured.body_2.locals =
    [.immediate none,
     .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
     .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
     .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
     .dead, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead,
     .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead] := rfl

private theorem intHostOverflow_u64_sum_false (aBits bBits : BitVec 128) :
    intHostOverflow false
      (decodeScalar ⟨.i64, false, aBits⟩ +
        decodeScalar ⟨.i64, false, bBits⟩) = false := by
  have hBound : ∀ x : BitVec 128,
      (truncateBits .i64 x).toNat < Nat.pow 2 64 := by
    intro x
    rw [toNat_truncateBits]
    exact Nat.mod_lt x.toNat (intWidth_modulus_pos .i64)
  have hSum : (truncateBits .i64 aBits).toNat + (truncateBits .i64 bBits).toNat <
      Nat.pow 2 128 :=
    Nat.lt_trans (Nat.add_lt_add (hBound aBits) (hBound bBits)) (by decide)
  change (decide (Int.ofNat ((truncateBits .i64 aBits).toNat +
      (truncateBits .i64 bBits).toNat) < 0) ||
    decide (HPow.hPow (2 : Int) 128 ≤
      Int.ofNat ((truncateBits .i64 aBits).toNat +
        (truncateBits .i64 bBits).toNat))) = false
  have hNotGe : ¬ (HPow.hPow (2 : Int) 128 ≤
      Int.ofNat ((truncateBits .i64 aBits).toNat +
        (truncateBits .i64 bBits).toNat)) := by
    intro hGeI
    have hNeg : Neg.neg (HPow.hPow (2 : Int) 128) =
        Int.negSucc (Nat.pow 2 128 - 1) := by decide
    have hSucc : Nat.succ (Nat.pow 2 128 - 1) = Nat.pow 2 128 := by decide
    change Int.NonNeg
      (Int.add (Int.ofNat ((truncateBits .i64 aBits).toNat +
          (truncateBits .i64 bBits).toNat))
        (Neg.neg (HPow.hPow (2 : Int) 128))) at hGeI
    rw [hNeg] at hGeI
    change Int.NonNeg
      (Int.subNatNat ((truncateBits .i64 aBits).toNat +
          (truncateBits .i64 bBits).toNat)
        (Nat.succ (Nat.pow 2 128 - 1))) at hGeI
    rw [hSucc] at hGeI
    unfold Int.subNatNat at hGeI
    cases hDiff : Nat.pow 2 128 - ((truncateBits .i64 aBits).toNat +
        (truncateBits .i64 bBits).toNat) with
    | zero =>
      exact Nat.not_le_of_gt hSum (Nat.le_of_sub_eq_zero hDiff)
    | succ k =>
      rw [hDiff] at hGeI
      nomatch hGeI
  have hFalse : decide (HPow.hPow (2 : Int) 128 ≤
      Int.ofNat ((truncateBits .i64 aBits).toNat +
        (truncateBits .i64 bBits).toNat)) = false := by
    cases hD : decide (HPow.hPow (2 : Int) 128 ≤
        Int.ofNat ((truncateBits .i64 aBits).toNat +
          (truncateBits .i64 bBits).toNat)) with
    | false => rfl
    | true => exact False.elim (hNotGe (of_decide_eq_true hD))
  rw [hFalse]
  rfl

private theorem execCoreCall_checkedAdd_u64_ok {m : MemoryState}
    {aBits bBits : BitVec 128} :
    let rawSum := bvOfInt 128
      (decodeScalar ⟨.i64, false, aBits⟩ + decodeScalar ⟨.i64, false, bBits⟩)
    let truncSum := truncateBits .i64 rawSum
    execCoreCallWithMem m (.numCheckedAdd .i64 false)
      [(.int .i64 false, .scalar ⟨.i64, false, aBits⟩),
       (.int .i64 false, .scalar ⟨.i64, false, bBits⟩)]
      (.option (.int .i64 false)) =
      .ok (.optionVal (if truncSum != rawSum then none
        else some (.scalar ⟨.i64, false, truncSum⟩)), m) := by
  dsimp only
  unfold execCoreCallWithMem
  dsimp only
  unfold execCoreContractOp execCheckedArith
  dsimp only
  have hGuard : (!IntWidth.beq .i64 .i64 || !IntWidth.beq .i64 .i64 ||
      !(false == false) || !(false == false) ||
      !MirTy.beq (.option (.int .i64 false)) (.option (.int .i64 false))) =
      false := by decide
  rw [ite_bool_false hGuard]
  unfold truncateScalarWithHostOverflow truncateScalar
  rw [ite_bool_false rfl]
  dsimp only
  rw [intHostOverflow_u64_sum_false, Bool.false_or]
  cases (truncateBits .i64 (bvOfInt 128
    (decodeScalar ⟨.i64, false, aBits⟩ + decodeScalar ⟨.i64, false, bBits⟩)) !=
    bvOfInt 128
      (decodeScalar ⟨.i64, false, aBits⟩ + decodeScalar ⟨.i64, false, bBits⟩)) <;>
    rfl

private theorem execCoreCall_saturatingAdd_u64_ok {m : MemoryState}
    {aBits bBits : BitVec 128} :
    let rawSum := bvOfInt 128
      (decodeScalar ⟨.i64, false, aBits⟩ + decodeScalar ⟨.i64, false, bBits⟩)
    let truncSum := truncateBits .i64 rawSum
    let resSv : ScalarVal :=
      if !(truncSum != rawSum) then ⟨.i64, false, truncSum⟩
      else ⟨.i64, false, truncateBits .i64 (bvOfInt 128 (unsignedMaxInt .i64))⟩
    execCoreCallWithMem m (.numSaturatingAdd .i64 false)
      [(.int .i64 false, .scalar ⟨.i64, false, aBits⟩),
       (.int .i64 false, .scalar ⟨.i64, false, bBits⟩)]
      (.int .i64 false) =
      .ok (.scalar resSv, m) := by
  dsimp only
  unfold execCoreCallWithMem
  dsimp only
  unfold execCoreContractOp
  dsimp only
  have hGuard : (!IntWidth.beq .i64 .i64 || !IntWidth.beq .i64 .i64 ||
      !(false == false) || !(false == false) ||
      !MirTy.beq (.int .i64 false) (.int .i64 false)) = false := by decide
  rw [ite_bool_false hGuard]
  unfold saturateScalar truncateScalarWithHostOverflow truncateScalar
  rw [ite_bool_false rfl]
  dsimp only
  rw [intHostOverflow_u64_sum_false, Bool.false_or]
  cases !(truncateBits .i64 (bvOfInt 128
    (decodeScalar ⟨.i64, false, aBits⟩ + decodeScalar ⟨.i64, false, bBits⟩)) !=
    bvOfInt 128
      (decodeScalar ⟨.i64, false, aBits⟩ + decodeScalar ⟨.i64, false, bBits⟩)) <;>
    first | rfl | (rw [ite_bool_false rfl]; rfl)

private theorem execCoreCall_cmpMin_u64_ok {m : MemoryState}
    {sumSv bSv : ScalarVal} (hSW : sumSv.width = .i64)
    (hSS : sumSv.signed = false) (hBW : bSv.width = .i64)
    (hBS : bSv.signed = false) :
    let minSv := if decide (decodeScalar sumSv ≤ decodeScalar bSv)
      then sumSv else bSv
    execCoreCallWithMem m (.cmpMin .i64 false)
      [(.int .i64 false, .scalar sumSv), (.int .i64 false, .scalar bSv)]
      (.int .i64 false) = .ok (.scalar minSv, m) := by
  dsimp only
  unfold execCoreCallWithMem; dsimp only
  unfold execCoreContractOp; dsimp only
  cases sumSv; cases bSv
  dsimp only at hSW hSS hBW hBS
  subst hSW; subst hSS; subst hBW; subst hBS
  rw [ite_bool_false (by decide)]
  cases hDec : decide (decodeScalar _ ≤ decodeScalar _) <;> rfl

private theorem execCoreCall_wrappingShl_u64_ok {m : MemoryState}
    {aBits sBits : BitVec 128} :
    let amt := Nat.mod (truncateBits .i32 sBits).toNat IntWidth.i64.bitWidth
    let res := intShiftLeft (decodeScalar ⟨.i64, false, aBits⟩)
      (intEmod (Int.ofNat amt) (Int.ofNat IntWidth.i64.bitWidth)).toNat
    execCoreCallWithMem m (.numWrappingShl .i64 false)
      [(.int .i64 false, .scalar ⟨.i64, false, aBits⟩),
       (.int .i32 false, .scalar ⟨.i32, false, sBits⟩)]
      (.int .i64 false) =
      .ok (.scalar ⟨.i64, false, truncateBits .i64 (bvOfInt 128 res)⟩, m) := by
  unfold execCoreCallWithMem; dsimp only
  unfold execCoreContractOp; dsimp only
  rw [ite_bool_false (by decide)]
  unfold evalShiftOp truncateScalar
  dsimp only
  rw [ite_bool_false rfl]
  dsimp only
  rw [ite_bool_eq_false (by dsimp only [BinOp.isUnchecked]; exact Bool.and_false _)]

private theorem execCoreCall_leadingZeros_u64_ok {m : MemoryState}
    {xBits : BitVec 128} :
    let lzBits := truncateBits .i32 (BitVec.ofNat 128
      (leadingZerosFrom (truncateBits .i64 xBits).toNat IntWidth.i64.bitWidth))
    execCoreCallWithMem m (.numLeadingZeros .i64 false)
      [(.int .i64 false, .scalar ⟨.i64, false, xBits⟩)]
      (.int .i32 false) =
      .ok (.scalar ⟨.i32, false, lzBits⟩, m) := by
  unfold execCoreCallWithMem execCoreContractOp
  rfl

private theorem checkArgsMatchV2_u64_u64_u32_inv {args : List Val}
    (h : checkArgsMatchV2 args
      [.int .i64 false, .int .i64 false, .int .i32 false] = true) :
    ∃ (aBits bBits sBits : BitVec 128),
      args = [.scalar ⟨.i64, false, aBits⟩, .scalar ⟨.i64, false, bBits⟩,
        .scalar ⟨.i32, false, sBits⟩] ∧
      truncateBits .i64 aBits = aBits ∧
      truncateBits .i64 bBits = bBits ∧
      truncateBits .i32 sBits = sBits := by
  cases args with
  | nil => cases h
  | cons v0 r0 =>
    cases r0 with
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases h0 : checkValV2 v0 (.int .i64 false) <;> rw [h0] at h <;> cases h
    | cons v1 r1 =>
      cases r1 with
      | nil =>
        dsimp only [checkArgsMatchV2] at h
        cases h0 : checkValV2 v0 (.int .i64 false) <;> rw [h0] at h
        · cases h
        · cases h1 : checkValV2 v1 (.int .i64 false) <;> rw [h1] at h <;> cases h
      | cons v2 r2 =>
        cases r2 with
        | cons _ _ =>
          dsimp only [checkArgsMatchV2] at h
          cases h0 : checkValV2 v0 (.int .i64 false) <;> rw [h0] at h
          · cases h
          · cases h1 : checkValV2 v1 (.int .i64 false) <;> rw [h1] at h
            · cases h
            · cases h2 : checkValV2 v2 (.int .i32 false) <;> rw [h2] at h <;> cases h
        | nil =>
          dsimp only [checkArgsMatchV2] at h
          cases h0 : checkValV2 v0 (.int .i64 false) with
          | false => rw [h0] at h; cases h
          | true =>
            rw [h0] at h
            cases h1 : checkValV2 v1 (.int .i64 false) with
            | false => rw [h1] at h; cases h
            | true =>
              rw [h1] at h
              cases h2 : checkValV2 v2 (.int .i32 false) with
              | false => rw [h2] at h; cases h
              | true =>
                cases v0 with
                | scalar aSv =>
                  let ⟨aBits, haEq, haT⟩ := checkVal_int_iff.mp
                    (show checkVal (.scalar aSv) (.int .i64 false) = true from h0)
                  injection haEq with haSv; subst haSv
                  cases v1 with
                  | scalar bSv =>
                    let ⟨bBits, hbEq, hbT⟩ := checkVal_int_iff.mp
                      (show checkVal (.scalar bSv) (.int .i64 false) = true
                        from h1)
                    injection hbEq with hbSv; subst hbSv
                    cases v2 with
                    | scalar sSv =>
                      let ⟨sBits, hsEq, hsT⟩ := checkVal_int_iff.mp
                        (show checkVal (.scalar sSv) (.int .i32 false) = true
                          from h2)
                      injection hsEq with hsSv; subst hsSv
                      exact ⟨aBits, bBits, sBits, rfl, haT, hbT, hsT⟩
                    | optionVal optV => cases optV <;> cases h2
                    | _ => cases h2
                  | optionVal optV => cases optV <;> cases h1
                  | _ => cases h1
                | optionVal optV => cases optV <;> cases h0
                | _ => cases h0

@[irreducible]
private def execV2 (p : Program) (fuel : Nat) (s : State)
    (P : TerminalOut → Prop) : Prop :=
  execStateV2 p fuel s P

private theorem execStateV2_of_execV2 {p : Program} {fuel : Nat} {s : State}
    {P : TerminalOut → Prop} (h : execV2 p fuel s P) :
    execStateV2 p fuel s P := by
  unfold execV2 at h
  exact h

private theorem execV2_step {p : Program} {P : TerminalOut → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : execV2 p fuel s' P) :
    execV2 p (fuel + 1) s P := by
  unfold execV2 at hNext ⊢
  exact execOutcomeStateV2_step hStep hNext

private theorem execV2_done {p : Program} {P : TerminalOut → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out) (hDone : P out) :
    execV2 p (fuel + 1) s P := by
  unfold execV2
  exact execOutcomeStateV2_done hStep hDone

private theorem body2_at :
    Trusted.MirSemantics.getElem? (entryProgForBody Captured.program 2).bodies 2 =
      some Captured.body_2 := rfl

private theorem checked_scalar_tail_ok (m : MemoryState)
    (cm : CallerMemory) (aBits bBits sBits : BitVec 128)
    (sumSv : ScalarVal) (opt5 : Option Val)
    (hATr : truncateBits .i64 aBits = aBits)
    (hBTr : truncateBits .i64 bBits = bBits)
    (hSTr : truncateBits .i32 sBits = sBits)
    (hSumTy :
      sumSv.width = .i64 ∧ sumSv.signed = false ∧
      truncateBits .i64 sumSv.bits = sumSv.bits) :
    execV2 (entryProgForBody Captured.program 2) 31
      ⟨[⟨2, 6, 0, [
        .immediate none,
        .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
        .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
        .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
        .immediate (some (.scalar sumSv)),
        .immediate (some (.optionVal opt5)),
        .dead, .dead, .immediate none, .dead, .dead, .dead, .dead, .dead,
        .dead, .dead, .dead, .dead, .dead, .dead, .dead
      ], none, none, none⟩], cm, m⟩
      (fun _ => True) := by
  let ⟨hSumW, hSumS, hSumTr⟩ := hSumTy
  have hAChk : checkValV2 (.scalar ⟨.i64, false, aBits⟩) (.int .i64 false) = true :=
    checkVal_int_eq hATr
  have hBChk : checkValV2 (.scalar ⟨.i64, false, bBits⟩) (.int .i64 false) = true :=
    checkVal_int_eq hBTr
  have hSChk : checkValV2 (.scalar ⟨.i32, false, sBits⟩) (.int .i32 false) = true :=
    checkVal_int_eq hSTr
  have hChkSum : checkValV2 (.scalar sumSv) (.int .i64 false) = true := by
    cases sumSv; dsimp only at hSumW hSumS hSumTr; subst hSumW; subst hSumS
    exact checkVal_int_eq hSumTr
  -- bb6 stmt 0: storageDead 5
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  -- bb6 stmts 1..2: storageLive 12, 13
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  -- bb6 stmt 3: assign 13 (.use (.copy 2))
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hBChk rfl rfl))
  -- bb6 term: coreCall numIsMultipleOf [move 13, const 4] -> 12, bb7
  have hMultArgs :
      evalArgOperandsV2 Captured.body_2.locals [
        .immediate none,
        .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
        .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
        .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
        .immediate (some (.scalar sumSv)),
        .dead, .dead, .dead, .immediate none, .dead, .dead, .dead,
        .immediate none, .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
        .dead, .dead, .dead, .dead, .dead, .dead, .dead
      ] m [
        .move ⟨13, []⟩,
        .constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 4)⟩
      ] = .ok ([
        (.int .i64 false, .scalar ⟨.i64, false, bBits⟩),
        (.int .i64 false, .scalar ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4)⟩)
      ], [
        .immediate none,
        .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
        .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
        .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
        .immediate (some (.scalar sumSv)),
        .dead, .dead, .dead, .immediate none, .dead, .dead, .dead,
        .immediate none, .immediate none,
        .dead, .dead, .dead, .dead, .dead, .dead, .dead
      ], m) := by
    unfold evalArgOperandsV2 evalOperandToSlotV2
    dsimp only
    rw [readPlaceV2_move_local rfl rfl rfl rfl]
    rfl
  apply execV2_step (evalStepV2_coreCall_ok body2_at rfl rfl rfl rfl
    rfl rfl hMultArgs (by rfl) (writePlaceV2_immediate_ok rfl rfl rfl))
  -- bb7 stmts 0..2: storageDead 13, storageLive 14, storageLive 15
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  -- bb7 stmt 3: assign 15 (.use (.copy 4))
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hChkSum rfl rfl))
  -- bb7 stmt 4: storageLive 16
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  -- bb7 stmt 5: assign 16 (.use (.copy 2))
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hBChk rfl rfl))
  -- bb7 term: coreCall cmpMin [move 15, move 16] -> 14, bb8
  let minSv := if decide (decodeScalar sumSv ≤ decodeScalar ⟨.i64, false, bBits⟩)
    then sumSv else ⟨.i64, false, bBits⟩
  have hMinChk : checkValV2 (.scalar minSv) (.int .i64 false) = true := by
    dsimp only [minSv]
    cases decide (decodeScalar sumSv ≤ decodeScalar ⟨.i64, false, bBits⟩)
    · exact hBChk
    · exact hChkSum
  apply execV2_step (evalStepV2_coreCall_ok body2_at rfl rfl rfl rfl
    rfl rfl
    (evalArgOperandsV2_two_move rfl rfl rfl rfl rfl rfl rfl rfl)
    (execCoreCall_cmpMin_u64_ok hSumW hSumS rfl rfl)
    (writePlaceV2_immediate_ok hMinChk rfl rfl))
  -- bb8 stmts 0..4: storageDead 16, 15, storageLive 17, 18, 19
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  -- bb8 stmt 5: assign 19 (.use (.copy 1))
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hAChk rfl rfl))
  -- bb8 stmt 6: storageLive 20
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  -- bb8 stmt 7: assign 20 (.use (.copy 3))
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hSChk rfl rfl))
  -- bb8 term: coreCall numWrappingShl [move 19, move 20] -> 18, bb9
  let shlAmt := Nat.mod (truncateBits .i32 sBits).toNat IntWidth.i64.bitWidth
  let shlRes := intShiftLeft (decodeScalar ⟨.i64, false, aBits⟩)
    (intEmod (Int.ofNat shlAmt) (Int.ofNat IntWidth.i64.bitWidth)).toNat
  let shlBits := truncateBits .i64 (bvOfInt 128 shlRes)
  have hShlChk : checkValV2 (.scalar ⟨.i64, false, shlBits⟩) (.int .i64 false) =
      true :=
    checkVal_scalar_truncateBits .i64 false (bvOfInt 128 shlRes)
  apply execV2_step (evalStepV2_coreCall_ok body2_at rfl rfl rfl rfl
    rfl rfl
    (evalArgOperandsV2_two_move rfl rfl rfl rfl rfl rfl rfl rfl)
    execCoreCall_wrappingShl_u64_ok
    (writePlaceV2_immediate_ok hShlChk rfl rfl))
  -- bb9 stmts 0..1: storageDead 20, 19
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  -- bb9 term: coreCall numLeadingZeros [move 18] -> 17, bb10
  let lzBits := truncateBits .i32 (BitVec.ofNat 128
    (leadingZerosFrom (truncateBits .i64 shlBits).toNat IntWidth.i64.bitWidth))
  have hLzChk : checkValV2 (.scalar ⟨.i32, false, lzBits⟩) (.int .i32 false) =
      true :=
    checkVal_scalar_truncateBits .i32 false _
  apply execV2_step (evalStepV2_coreCall_ok body2_at rfl rfl rfl rfl
    rfl rfl
    (evalArgOperandsV2_one_move rfl rfl rfl rfl)
    execCoreCall_leadingZeros_u64_ok
    (writePlaceV2_immediate_ok hLzChk rfl rfl))
  -- bb10 stmt 0: storageDead 18
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  -- bb10 stmt 1: assign 0 (.aggregateTuple [move 12, move 14, move 17])
  let multVal : Val := .bool (Nat.beq ((truncateBits .i64 bBits).toNat %
    (truncateBits .i64 (truncateBits .i64 (BitVec.ofNat 128 4))).toNat) 0)
  have hMultChk : checkValV2 multVal .bool = true := rfl
  have hTupChk : checkValV2
      (.tuple [multVal, .scalar minSv, .scalar ⟨.i32, false, lzBits⟩])
      (.tuple [.bool, .int .i64 false, .int .i32 false]) = true := by
    change checkValV2List
        [multVal, .scalar minSv, .scalar ⟨.i32, false, lzBits⟩]
        [.bool, .int .i64 false, .int .i32 false] = true
    dsimp only [checkValV2List]
    rw [hMultChk, hMinChk, hLzChk]; rfl
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_aggregateTuple3_move_ok rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl hMultChk hMinChk hLzChk)
    (writePlaceV2_immediate_ok hTupChk rfl rfl))
  -- bb10 stmts 2..5: storageDead 17, 14, 12, 4
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  -- bb10 term: return_
  apply execV2_done
    (evalStepV2_return_ok body2_at rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
  exact trivial

private theorem checked_scalar_no_ovf_ok (m : MemoryState) (cm : CallerMemory)
    (aBits bBits sBits : BitVec 128) (addSv : ScalarVal)
    (hATr : truncateBits .i64 aBits = aBits)
    (hBTr : truncateBits .i64 bBits = bBits)
    (hSTr : truncateBits .i32 sBits = sBits)
    (hAddW : addSv.width = .i64) (hAddS : addSv.signed = false)
    (hAddTr : truncateBits .i64 addSv.bits = addSv.bits) :
    execV2 (entryProgForBody Captured.program 2) 41
      ⟨[⟨2, 1, 0, [
        .immediate none,
        .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
        .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
        .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
        .immediate none,
        .immediate (some (.optionVal (some (.scalar addSv)))),
        .immediate none,
        .immediate none,
        .immediate none,
        .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
        .dead, .dead
      ], none, none, none⟩], cm, m⟩
      (fun _ => True) := by
  have hAddChk : checkValV2 (.scalar addSv) (.int .i64 false) = true := by
    cases addSv; dsimp only at hAddW hAddS hAddTr; subst hAddW; subst hAddS
    exact checkVal_int_eq hAddTr
  -- bb1 stmts 0..3 & switchInt -> bb4
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step (evalStepV2_nop_ok body2_at rfl rfl)
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_discriminant_option_some_ok rfl rfl)
    (writePlaceV2_immediate_ok (checkVal_int_eq (by decide)) rfl rfl))
  have hSw1 : evalSwitchBranches .isize (BitVec.ofNat 128 1) 2
      [((BitVec.ofNat 128 0), 3), ((BitVec.ofNat 128 1), 4)] = .ok 4 := rfl
  apply execV2_step
    (evalStepV2_switchInt_move_ok body2_at rfl rfl rfl rfl rfl rfl rfl rfl rfl hSw1)
  -- bb4 stmt 0: storageLive 9
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  -- bb4 stmt 1: assign 9 (.use (.copy (5, [.downcast 1, .field 0 u64])))
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_u64_downcast1_field0_ok rfl rfl)
    (writePlaceV2_immediate_ok hAddChk rfl rfl))
  -- bb4 stmt 2: assign 4 (.use (.copy 9))
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hAddChk rfl rfl))
  -- bb4 stmt 3: storageDead 9; term: goto 6
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step (evalStepV2_goto_ok body2_at rfl rfl rfl rfl)
  exact checked_scalar_tail_ok m cm aBits bBits sBits addSv
    (some (.scalar addSv)) hATr hBTr hSTr ⟨hAddW, hAddS, hAddTr⟩

private theorem checked_scalar_ovf_ok (m : MemoryState) (cm : CallerMemory)
    (aBits bBits sBits : BitVec 128)
    (hATr : truncateBits .i64 aBits = aBits)
    (hBTr : truncateBits .i64 bBits = bBits)
    (hSTr : truncateBits .i32 sBits = sBits)
    (hOvf : (truncateBits .i64 (bvOfInt 128
      (decodeScalar ⟨.i64, false, aBits⟩ +
       decodeScalar ⟨.i64, false, bBits⟩)) !=
      bvOfInt 128 (decodeScalar ⟨.i64, false, aBits⟩ +
        decodeScalar ⟨.i64, false, bBits⟩)) = true) :
    execV2 (entryProgForBody Captured.program 2) 44
      ⟨[⟨2, 1, 0, [
        .immediate none,
        .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
        .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
        .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
        .immediate none,
        .immediate (some (.optionVal none)),
        .immediate none,
        .immediate none,
        .immediate none,
        .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead,
        .dead, .dead
      ], none, none, none⟩], cm, m⟩
      (fun _ => True) := by
  have hAChk : checkValV2 (.scalar ⟨.i64, false, aBits⟩) (.int .i64 false) = true :=
    checkVal_int_eq hATr
  have hBChk : checkValV2 (.scalar ⟨.i64, false, bBits⟩) (.int .i64 false) = true :=
    checkVal_int_eq hBTr
  -- bb1 stmts 0..3 & switchInt -> bb3
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step (evalStepV2_nop_ok body2_at rfl rfl)
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_discriminant_option_none_ok rfl rfl)
    (writePlaceV2_immediate_ok (checkVal_int_eq (by decide)) rfl rfl))
  have hSw0 : evalSwitchBranches .isize (BitVec.ofNat 128 0) 2
      [((BitVec.ofNat 128 0), 3), ((BitVec.ofNat 128 1), 4)] = .ok 3 := rfl
  apply execV2_step
    (evalStepV2_switchInt_move_ok body2_at rfl rfl rfl rfl rfl rfl rfl rfl rfl hSw0)
  -- bb3 stmts 0..3
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hAChk rfl rfl))
  apply execV2_step
    (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
    (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
    (writePlaceV2_immediate_ok hBChk rfl rfl))
  -- bb3 term: saturatingAdd
  let satSv : ScalarVal :=
    ⟨.i64, false, truncateBits .i64 (bvOfInt 128 (unsignedMaxInt .i64))⟩
  have hMaxChk : checkValV2 (.scalar satSv) (.int .i64 false) = true :=
    checkVal_scalar_truncateBits .i64 false _
  have hMaxTr : truncateBits .i64 satSv.bits = satSv.bits :=
    truncateBits_idem .i64 _
  have hSatCall : execCoreCallWithMem m (.numSaturatingAdd .i64 false)
      [(.int .i64 false, .scalar ⟨.i64, false, aBits⟩),
       (.int .i64 false, .scalar ⟨.i64, false, bBits⟩)]
      (.int .i64 false) = .ok (.scalar satSv, m) := by
    have h0 := execCoreCall_saturatingAdd_u64_ok (m := m) (aBits := aBits)
      (bBits := bBits)
    dsimp only at h0
    rw [hOvf] at h0
    exact h0
  apply execV2_step (evalStepV2_coreCall_ok body2_at rfl rfl rfl rfl
    rfl rfl
    (evalArgOperandsV2_two_move rfl rfl rfl rfl rfl rfl rfl rfl)
    hSatCall
    (writePlaceV2_immediate_ok hMaxChk rfl rfl))
  -- bb5 stmts 0..1 & goto 6
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step
    (evalStepV2_storageDead_imm_ok body2_at rfl rfl rfl rfl rfl)
  apply execV2_step (evalStepV2_goto_ok body2_at rfl rfl rfl rfl)
  exact checked_scalar_tail_ok m cm aBits bBits sBits satSv none
    hATr hBTr hSTr ⟨rfl, rfl, hMaxTr⟩

private theorem checked_scalar_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q) :
    WellFormedV2 (entryProgForBody Captured.program 2) q := by
  let ⟨hCM, hMatch, _, _⟩ := hValid
  let ⟨aBits, bBits, sBits, hArgs, hATr, hBTr, hSTr⟩ :=
    checkArgsMatchV2_u64_u64_u32_inv hMatch
  have hAChk : checkValV2 (.scalar ⟨.i64, false, aBits⟩) (.int .i64 false) = true :=
    checkVal_int_eq hATr
  have hBChk : checkValV2 (.scalar ⟨.i64, false, bBits⟩) (.int .i64 false) = true :=
    checkVal_int_eq hBTr
  have hSChk : checkValV2 (.scalar ⟨.i32, false, sBits⟩) (.int .i32 false) = true :=
    checkVal_int_eq hSTr
  let m := entryMemoryWithCaller q.callerMem
  have hQ : q = ⟨[.scalar ⟨.i64, false, aBits⟩, .scalar ⟨.i64, false, bBits⟩,
      .scalar ⟨.i32, false, sBits⟩], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hInit : initStateV2 (entryProgForBody Captured.program 2) q =
      .ok ⟨[⟨2, 0, 0, [
        .immediate none,
        .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
        .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
        .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
        .dead, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead, .dead,
        .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead
      ], none, none, none⟩], q.callerMem, m⟩ := by
    rw [hQ]
    have hChkArgs : checkArgsMatchV2
        [.scalar ⟨.i64, false, aBits⟩, .scalar ⟨.i64, false, bBits⟩,
         .scalar ⟨.i32, false, sBits⟩]
        ((Captured.body_2.locals.drop 1).take Captured.body_2.argumentCount) =
        true := by
      change checkArgsMatchV2
        [.scalar ⟨.i64, false, aBits⟩, .scalar ⟨.i64, false, bBits⟩,
         .scalar ⟨.i32, false, sBits⟩]
        [.int .i64 false, .int .i64 false, .int .i32 false] = true
      dsimp only [checkArgsMatchV2]; rw [hAChk, hBChk, hSChk]; rfl
    have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 2)
      (q := ⟨[.scalar ⟨.i64, false, aBits⟩, .scalar ⟨.i64, false, bBits⟩,
        .scalar ⟨.i32, false, sBits⟩], q.callerMem⟩)
      (body := Captured.body_2)
      rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hChkArgs rfl rfl
    rw [h0]
    exact congrArg
      (fun ls => (Except.ok ⟨[⟨2, 0, 0, ls, none, none, none⟩], q.callerMem, m⟩ :
        Except FaultKind State))
      (initLocalsLoop_body2 aBits bBits sBits)
  let rawSum := bvOfInt 128
    (decodeScalar ⟨.i64, false, aBits⟩ + decodeScalar ⟨.i64, false, bBits⟩)
  let truncSum := truncateBits .i64 rawSum
  let addSv : ScalarVal := ⟨.i64, false, truncSum⟩
  have hAddTr : truncateBits .i64 addSv.bits = addSv.bits :=
    truncateBits_idem .i64 rawSum
  have hAddChk : checkValV2 (.scalar addSv) (.int .i64 false) = true :=
    checkVal_scalar_truncateBits .i64 false rawSum
  have hAddCall : execCoreCallWithMem m (.numCheckedAdd .i64 false)
      [(.int .i64 false, .scalar ⟨.i64, false, aBits⟩),
       (.int .i64 false, .scalar ⟨.i64, false, bBits⟩)]
      (.option (.int .i64 false)) =
      .ok (.optionVal (if truncSum != rawSum then none
        else some (.scalar addSv)), m) := execCoreCall_checkedAdd_u64_ok
  cases hOvf : (truncSum != rawSum) with
  | true =>
    rw [hOvf] at hAddCall
    have hExecV2 : execV2 (entryProgForBody Captured.program 2) 51
        ⟨[⟨2, 0, 0, [
          .immediate none,
          .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
          .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
          .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
          .dead, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead, .dead,
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead
        ], none, none, none⟩], q.callerMem, m⟩
        (fun _ => True) := by
      -- bb0 stmts 0..5
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
        (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
        (writePlaceV2_immediate_ok hAChk rfl rfl))
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
        (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
        (writePlaceV2_immediate_ok hBChk rfl rfl))
      -- bb0 term: checkedAdd -> bb1
      apply execV2_step (evalStepV2_coreCall_ok body2_at rfl rfl rfl
        rfl rfl rfl
        (evalArgOperandsV2_two_move rfl rfl rfl rfl rfl rfl rfl rfl)
        hAddCall
        (writePlaceV2_immediate_ok rfl rfl rfl))
      exact checked_scalar_ovf_ok m q.callerMem aBits bBits sBits
        hATr hBTr hSTr hOvf
    exact wellFormedV2_of_exec hInit (execStateV2_of_execV2 hExecV2)
  | false =>
    rw [hOvf] at hAddCall
    rw [ite_bool_false rfl] at hAddCall
    have hExecV2 : execV2 (entryProgForBody Captured.program 2) 48
        ⟨[⟨2, 0, 0, [
          .immediate none,
          .immediate (some (.scalar ⟨.i64, false, aBits⟩)),
          .immediate (some (.scalar ⟨.i64, false, bBits⟩)),
          .immediate (some (.scalar ⟨.i32, false, sBits⟩)),
          .dead, .dead, .dead, .dead, .immediate none, .dead, .dead, .dead, .dead,
          .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead
        ], none, none, none⟩], q.callerMem, m⟩
        (fun _ => True) := by
      -- bb0 stmts 0..5
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
        (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
        (writePlaceV2_immediate_ok hAChk rfl rfl))
      apply execV2_step
        (evalStepV2_storageLive_dead_ok body2_at rfl rfl rfl rfl rfl)
      apply execV2_step (evalStepV2_assign_ok body2_at rfl rfl rfl
        (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
        (writePlaceV2_immediate_ok hBChk rfl rfl))
      -- bb0 term: checkedAdd -> bb1
      apply execV2_step (evalStepV2_coreCall_ok body2_at rfl rfl rfl
        rfl rfl rfl
        (evalArgOperandsV2_two_move rfl rfl rfl rfl rfl rfl rfl rfl)
        hAddCall
        (writePlaceV2_immediate_ok hAddChk rfl rfl))
      exact checked_scalar_no_ovf_ok m q.callerMem aBits bBits sBits addSv
        hATr hBTr hSTr rfl rfl hAddTr
    exact wellFormedV2_of_exec hInit (execStateV2_of_execV2 hExecV2)

/-! ## Body 3: `slice_and_replace` (`is_empty` + `mem::replace`) -/

private theorem checkArgsMatchV2_slice_mutU64_u64_inv {args : List Val}
    (h : checkArgsMatchV2 args
      [.ref .shared (.slice (.int .i8 false)),
       .ref .mut (.int .i64 false), .int .i64 false] = true) :
    ∃ (sPtr : PtrVal) (sLen : UInt64) (dPtr : PtrVal) (nBits : BitVec 128),
      args = [.slicePtr sPtr sLen, .ptr dPtr, .scalar ⟨.i64, false, nBits⟩] ∧
      sPtr.width = .isize ∧ dPtr.width = .isize ∧
      truncateBits .i64 nBits = nBits := by
  cases args with
  | nil => cases h
  | cons v0 r0 =>
    cases r0 with
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) <;>
        rw [h0] at h <;> cases h
    | cons v1 r1 =>
      cases r1 with
      | nil =>
        dsimp only [checkArgsMatchV2] at h
        cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) <;>
          rw [h0] at h
        · cases h
        · cases h1 : checkValV2 v1 (.ref .mut (.int .i64 false)) <;>
            rw [h1] at h <;> cases h
      | cons v2 r2 =>
        cases r2 with
        | cons _ _ =>
          dsimp only [checkArgsMatchV2] at h
          cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) <;>
            rw [h0] at h
          · cases h
          · cases h1 : checkValV2 v1 (.ref .mut (.int .i64 false)) <;> rw [h1] at h
            · cases h
            · cases h2 : checkValV2 v2 (.int .i64 false) <;>
                rw [h2] at h <;> cases h
        | nil =>
          dsimp only [checkArgsMatchV2] at h
          cases h0 : checkValV2 v0 (.ref .shared (.slice (.int .i8 false))) with
          | false => rw [h0] at h; cases h
          | true =>
            rw [h0] at h
            cases h1 : checkValV2 v1 (.ref .mut (.int .i64 false)) with
            | false => rw [h1] at h; cases h
            | true =>
              rw [h1] at h
              cases h2 : checkValV2 v2 (.int .i64 false) with
              | false => rw [h2] at h; cases h
              | true =>
                cases v0 with
                | slicePtr sPtr sLen =>
                  have hsW : sPtr.width = .isize := by
                    change IntWidth.beq sPtr.width .isize = true at h0
                    cases hw : sPtr.width with
                    | isize => rfl
                    | i8 | i16 | i32 | i64 | i128 => rw [hw] at h0; cases h0
                  cases v1 with
                  | ptr dPtr =>
                    have hdW : dPtr.width = .isize := by
                      change IntWidth.beq dPtr.width .isize = true at h1
                      cases hw : dPtr.width with
                      | isize => rfl
                      | i8 | i16 | i32 | i64 | i128 => rw [hw] at h1; cases h1
                    cases v2 with
                    | scalar nSv =>
                      let ⟨nBits, hnEq, hnT⟩ := checkVal_int_iff.mp
                        (show checkVal (.scalar nSv) (.int .i64 false) = true
                          from h2)
                      injection hnEq with hnSv; subst hnSv
                      exact ⟨sPtr, sLen, dPtr, nBits, rfl, hsW, hdW, hnT⟩
                    | optionVal optV => cases optV <;> cases h2
                    | _ => cases h2
                  | optionVal optV => cases optV <;> cases h1
                  | _ => cases h1
                | optionVal optV => cases optV <;> cases h0
                | _ => cases h0

private theorem decodeValV2_u64_some {endian : TargetEndian}
    {bs : List AllocByte} {v : Val}
    (h : decodeValV2 endian (.int .i64 false) bs = .ok (some v)) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨.i64, false, bits⟩ ∧
      truncateBits .i64 bits = bits := by
  change decodeVal endian (.int .i64 false) bs = .ok (some v) at h
  unfold decodeVal at h
  dsimp only [layoutOfTy, intLayout] at h
  cases hLen : Nat.beq bs.length 8 with
  | false => rw [hLen] at h; cases h
  | true =>
    rw [hLen] at h
    cases hInit : initBytes? bs with
    | none => rw [hInit] at h; cases h
    | some raw =>
      rw [hInit] at h
      rw [ite_bool_false (by decide), ite_bool_false (by decide)] at h
      dsimp only [evalConstLit] at h
      cases hOv : (truncateBits .i64 (BitVec.ofNat 128 (decodeUInt endian raw)) !=
          BitVec.ofNat 128 (decodeUInt endian raw)) with
      | true => rw [ite_bool_true hOv] at h; cases h
      | false =>
        rw [ite_bool_false hOv] at h
        injection h with hv
        injection hv with hv2
        rw [← hv2]
        exact ⟨_, rfl, truncateBits_idem .i64 _⟩

private theorem readBytes_of_ok {m : MemoryState} {aid : AllocId}
    {a : Allocation} {len al off : Nat}
    (hNZ : Nat.beq len 0 = false)
    (hFind : findAllocation aid m.allocations = some a)
    (hBad : (!a.live || !isInBounds a off len || !isAligned a off al) = false) :
    readBytes m ⟨aid, off⟩ len al = .ok ((a.bytes.drop off).take len) := by
  unfold readBytes
  dsimp only
  rw [hFind]
  dsimp only
  rw [ite_bool_false hNZ]
  rw [ite_bool_false hBad]

private theorem execMemReplace_u64_ok (m : MemoryState) (p : PtrVal)
    (nBits : BitVec 128) (hNTr : truncateBits .i64 nBits = nBits)
    (hValid : refValidInMem m .mut (.int .i64 false) (.ptr p) = .ok ()) :
    ∃ (oldBits : BitVec 128) (m1 : MemoryState),
      execMemReplace m (.int .i64 false) p (.scalar ⟨.i64, false, nBits⟩) =
        .ok (.scalar ⟨.i64, false, oldBits⟩, m1) ∧
      truncateBits .i64 oldBits = oldBits := by
  have hNChk : checkValV2 (.scalar ⟨.i64, false, nBits⟩) (.int .i64 false) =
      true := checkVal_int_eq hNTr
  unfold refValidInMem at hValid
  dsimp only at hValid
  rw [ite_bool_false (b := !isSupportedV2PointeeTy (.int .i64 false)) rfl] at hValid
  cases hAid : p.allocId with
  | none =>
    rw [hAid] at hValid
    have hBad : (if (Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 8) = true then
        Except.error FaultKind.undefined else _) = Except.ok () := hValid
    rw [ite_bool_true (by rw [(by decide : Nat.blt 0 8 = true), Bool.or_true])]
      at hBad
    cases hBad
  | some aid =>
    rw [hAid] at hValid; dsimp only at hValid
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at hValid; cases hValid
    | some a =>
      rw [hFind, layoutOfTyV2_u64] at hValid; dsimp only at hValid
      cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat 8 ||
          !isAligned a p.offsetBytes.toNat 3) with
      | true => rw [hBad] at hValid; cases hValid
      | false =>
        rw [hBad] at hValid
        cases hMut : (Mutability.beq .mut .mut &&
            !Mutability.beq a.mutability .mut) with
        | true => rw [hMut] at hValid; cases hValid
        | false =>
          rw [hMut] at hValid
          cases hDec : decodeValV2 profileV2TargetEndian (.int .i64 false)
              ((a.bytes.drop p.offsetBytes.toNat).take 8) with
          | error k => rw [hDec] at hValid; cases hValid
          | ok optOld =>
            cases optOld with
            | none => rw [hDec] at hValid; cases hValid
            | some oldVal =>
              let ⟨oldBits, hOldEq, hOldTr⟩ := decodeValV2_u64_some hDec
              subst hOldEq
              have hLoad : loadIndirectV2 m (.int .i64 false)
                  ⟨aid, p.offsetBytes.toNat⟩ =
                  .ok (some (.scalar ⟨.i64, false, oldBits⟩)) := by
                unfold loadIndirectV2
                rw [layoutOfTyV2_u64]; dsimp only
                rw [readBytes_of_ok rfl hFind hBad]
                exact hDec
              have hLive : a.live = true := by
                cases hL : a.live with
                | false => rw [hL] at hBad; cases hBad
                | true => rfl
              have hMutEq : a.mutability = .mut := by
                cases hM : a.mutability
                · rw [hM] at hMut; cases hMut
                · rfl
              have hEnc : encodeValV2 profileV2TargetEndian (.int .i64 false)
                  (.scalar ⟨.i64, false, nBits⟩) =
                  .ok ((encodeUInt profileV2TargetEndian 8 nBits.toNat).map
                    (fun b => AllocByte.init b none)) := by
                change (if !checkValV2 (.scalar ⟨.i64, false, nBits⟩)
                      (.int .i64 false) then
                    Except.error FaultKind.unsupported
                  else
                    encodeVal profileV2TargetEndian (.int .i64 false)
                      (.scalar ⟨.i64, false, nBits⟩)) =
                  Except.ok ((encodeUInt profileV2TargetEndian 8
                      nBits.toNat).map (fun b => AllocByte.init b none))
                rw [ite_bool_false (by rw [hNChk]; rfl)]
                unfold encodeVal
                rw [ite_bool_false (by
                  have hV1 : checkVal (.scalar ⟨.i64, false, nBits⟩)
                      (.int .i64 false) = true := hNChk
                  rw [hV1]; rfl)]
                rfl
              have hLen8 : ((encodeUInt profileV2TargetEndian 8 nBits.toNat).map
                  (fun b => AllocByte.init b none)).length = 8 := by
                unfold encodeUInt profileV2TargetEndian
                rfl
              have hStore : ∃ m1, storeIndirectV2 m (.int .i64 false)
                  ⟨aid, p.offsetBytes.toNat⟩
                  (.scalar ⟨.i64, false, nBits⟩) = .ok m1 := by
                unfold storeIndirectV2
                rw [layoutOfTyV2_u64]; dsimp only
                rw [hEnc]; dsimp only
                unfold writeBytes; dsimp only
                rw [hFind]; dsimp only
                rw [hLen8, ite_bool_false (by decide)]
                rw [ite_bool_false hBad, hMutEq]
                exact ⟨_, rfl⟩
              let ⟨m1, hSt⟩ := hStore
              refine ⟨oldBits, m1, ?_, hOldTr⟩
              unfold execMemReplace
              rw [ite_bool_false (by rw [hNChk]; rfl)]
              have hRefsOk : (!refsValidInMem m (.int .i64 false)
                  (.scalar ⟨.i64, false, nBits⟩)) = false := by
                dsimp only [refsValidInMem]; rfl
              rw [ite_bool_eq_false hRefsOk, layoutOfTyV2_u64]; dsimp only
              rw [hAid]; dsimp only; rw [hFind]; dsimp only
              rw [ite_bool_false (by rw [hLive, hMutEq]; rfl)]
              rw [hLoad]; dsimp only; rw [hSt]

private theorem slice_and_replace_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_3 q) :
    WellFormedV2 (entryProgForBody Captured.program 3) q := by
  let ⟨hCM, hMatch, hRefs, hDisj⟩ := hValid
  let ⟨sPtr, sLen, dPtr, nBits, hArgs, hsW, hdW, hNTr⟩ :=
    checkArgsMatchV2_slice_mutU64_u64_inv hMatch
  have hNChk : checkValV2 (.scalar ⟨.i64, false, nBits⟩) (.int .i64 false) =
      true := checkVal_int_eq hNTr
  cases sPtr with
  | mk sAid sOff sw =>
    dsimp only at hsW; subst hsW
    cases dPtr with
    | mk dAid dOff dw =>
      dsimp only at hdW; subst hdW
      let sPtr : PtrVal := ⟨sAid, sOff, .isize⟩
      let dPtr : PtrVal := ⟨dAid, dOff, .isize⟩
      let m := entryMemoryWithCaller q.callerMem
      have hQ : q = ⟨[.slicePtr sPtr sLen, .ptr dPtr,
          .scalar ⟨.i64, false, nBits⟩], q.callerMem⟩ := by
        cases q; dsimp only at hArgs; rw [hArgs]
      have hRefs' :
          refsValidInMemList m
            [.ref .shared (.slice (.int .i8 false)),
             .ref .mut (.int .i64 false), .int .i64 false]
            [.slicePtr sPtr sLen, .ptr dPtr,
             .scalar ⟨.i64, false, nBits⟩] = true := by
        rw [← hArgs]; exact hRefs
      have hSliceValid :
          refValidInMem m .shared (.slice (.int .i8 false))
            (.slicePtr sPtr sLen) = .ok () := by
        dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
        cases h0 : refValidInMem m .shared (.slice (.int .i8 false))
            (.slicePtr sPtr sLen) with
        | error k => rw [h0] at hRefs'; cases hRefs'
        | ok u => cases u; rfl
      have hDstValid :
          refValidInMem m .mut (.int .i64 false) (.ptr dPtr) = .ok () := by
        dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
        rw [hSliceValid] at hRefs'; dsimp only at hRefs'
        cases h1 : refValidInMem m .mut (.int .i64 false) (.ptr dPtr) with
        | error k => rw [h1] at hRefs'; cases hRefs'
        | ok u => cases u; rfl
      let ⟨oldBits, m1, hReplace, hOldTr⟩ :=
        execMemReplace_u64_ok m dPtr nBits hNTr hDstValid
      have hOldChk : checkValV2 (.scalar ⟨.i64, false, oldBits⟩)
          (.int .i64 false) = true := checkVal_int_eq hOldTr
      have hInit : initStateV2 (entryProgForBody Captured.program 3) q =
          .ok ⟨[⟨3, 0, 0, [
            .immediate none,
            .immediate (some (.slicePtr sPtr sLen)),
            .immediate (some (.ptr dPtr)),
            .immediate (some (.scalar ⟨.i64, false, nBits⟩)),
            .dead, .dead, .dead, .dead, .dead
          ], none, none, none⟩], q.callerMem, m⟩ := by
        rw [hQ]
        have hDisjList : spansPairwiseDisjoint (refAccessSpansList
            ((Captured.body_3.locals.drop 1).take Captured.body_3.argumentCount)
            [.slicePtr sPtr sLen, .ptr dPtr,
             .scalar ⟨.i64, false, nBits⟩]) = true := by
          rw [← hArgs]; exact hDisj
        have hChkArgs : checkArgsMatchV2
            [.slicePtr sPtr sLen, .ptr dPtr, .scalar ⟨.i64, false, nBits⟩]
            ((Captured.body_3.locals.drop 1).take Captured.body_3.argumentCount) =
            true := by
          change checkArgsMatchV2
            [.slicePtr sPtr sLen, .ptr dPtr, .scalar ⟨.i64, false, nBits⟩]
            [.ref .shared (.slice (.int .i8 false)),
             .ref .mut (.int .i64 false), .int .i64 false] = true
          dsimp only [checkArgsMatchV2]; rw [hNChk]; rfl
        have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 3)
          (q := ⟨[.slicePtr sPtr sLen, .ptr dPtr,
            .scalar ⟨.i64, false, nBits⟩], q.callerMem⟩)
          (body := Captured.body_3)
          rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hChkArgs hRefs' hDisjList
        rw [h0]; rfl
      have hExec : execStateV2 (entryProgForBody Captured.program 3) 20
          ⟨[⟨3, 0, 0, [
            .immediate none,
            .immediate (some (.slicePtr sPtr sLen)),
            .immediate (some (.ptr dPtr)),
            .immediate (some (.scalar ⟨.i64, false, nBits⟩)),
            .dead, .dead, .dead, .dead, .dead
          ], none, none, none⟩], q.callerMem, m⟩
          (fun _ => True) := by
        -- bb0 stmts 0..1: storageLive 4, 5
        apply execOutcomeStateV2_step (by rfl)
        apply execOutcomeStateV2_step (by rfl)
        -- bb0 stmt 2: assign 5 (.ref .shared [1, .deref])
        apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
          (evalRvalueV2_ref_deref_ok rfl rfl rfl rfl hSliceValid)
          (writePlaceV2_immediate_ok rfl rfl rfl))
        -- bb0 term: sliceIsEmpty [move 5] -> 4, bb1
        have hIsEmptyCall : execCoreCallWithMem m (.sliceIsEmpty (.int .i8 false))
            [(.ref .shared (.slice (.int .i8 false)), .slicePtr sPtr sLen)]
            .bool = .ok (.bool (Nat.beq sLen.toNat 0), m) := by
          unfold execCoreCallWithMem; dsimp only
          unfold execCoreContractOp; dsimp only
          rw [ite_bool_false (by decide)]
          rw [hSliceValid]
        apply execOutcomeStateV2_step (evalStepV2_coreCall_ok rfl rfl rfl rfl rfl
          rfl rfl
          (evalArgOperandsV2_one_move rfl rfl rfl rfl)
          hIsEmptyCall
          (writePlaceV2_immediate_ok rfl rfl rfl))
        -- bb1 stmts 0..2: storageDead 5, storageLive 6, storageLive 7
        apply execOutcomeStateV2_step (by rfl)
        apply execOutcomeStateV2_step (by rfl)
        apply execOutcomeStateV2_step (by rfl)
        -- bb1 stmt 3: assign 7 (.ref .mut [2, .deref])
        apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
          (evalRvalueV2_ref_deref_ok rfl rfl rfl rfl hDstValid)
          (writePlaceV2_immediate_ok rfl rfl rfl))
        -- bb1 stmt 4: storageLive 8
        apply execOutcomeStateV2_step (by rfl)
        -- bb1 stmt 5: assign 8 (.use (.copy 3))
        apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
          (evalRvalueV2_use_copy_ok rfl rfl rfl rfl)
          (writePlaceV2_immediate_ok hNChk rfl rfl))
        -- bb1 term: coreCall memReplace [move 7, move 8] -> 6, bb2
        have hReplaceCall : execCoreCallWithMem m (.memReplace (.int .i64 false))
            [(.ref .mut (.int .i64 false), .ptr dPtr),
             (.int .i64 false, .scalar ⟨.i64, false, nBits⟩)]
            (.int .i64 false) = .ok (.scalar ⟨.i64, false, oldBits⟩, m1) := by
          unfold execCoreCallWithMem; dsimp only
          unfold execCoreContractOp
          exact hReplace
        apply execOutcomeStateV2_step (evalStepV2_coreCall_ok rfl rfl rfl rfl rfl
          rfl rfl
          (evalArgOperandsV2_two_move rfl rfl rfl rfl rfl rfl rfl rfl)
          hReplaceCall
          (writePlaceV2_immediate_ok hOldChk rfl rfl))
        -- bb2 stmts 0..1: storageDead 8, 7
        apply execOutcomeStateV2_step (by rfl)
        apply execOutcomeStateV2_step (by rfl)
        -- bb2 stmt 2: assign 0 (.aggregateTuple [move 4, move 6])
        have hTupChk : checkValV2
            (.tuple [.bool (Nat.beq sLen.toNat 0),
              .scalar ⟨.i64, false, oldBits⟩])
            (.tuple [.bool, .int .i64 false]) = true := by
          change checkValV2List [.bool (Nat.beq sLen.toNat 0),
              .scalar ⟨.i64, false, oldBits⟩]
            [.bool, .int .i64 false] = true
          dsimp only [checkValV2List]
          rw [hOldChk]; rfl
        apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
          (evalRvalueV2_aggregateTuple2_move_ok rfl rfl rfl rfl rfl rfl rfl rfl
            rfl hOldChk)
          (writePlaceV2_immediate_ok hTupChk rfl rfl))
        -- bb2 stmts 3..4: storageDead 6, 4
        apply execOutcomeStateV2_step (by rfl)
        apply execOutcomeStateV2_step (by rfl)
        -- bb2 term: return_
        apply execOutcomeStateV2_done
          (evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
        exact trivial
      exact wellFormedV2_of_exec hInit hExec

/-! ## Body 4: `take_option` (`Option::is_some` + `Option::take`) -/

private theorem decodeValV2_opt_u64_some {endian : TargetEndian}
    {bs : List AllocByte} {v : Val}
    (h : decodeValV2 endian (.option (.int .i64 false)) bs = .ok (some v)) :
    ∃ optBits : Option (BitVec 128),
      v = .optionVal (optBits.map (fun b => .scalar ⟨.i64, false, b⟩)) ∧
      (match optBits with
        | none => True
        | some b => truncateBits .i64 b = b) := by
  change (if !Nat.beq bs.length (Nat.pow 2 3 + 8) then
      Except.error FaultKind.unsupported
    else
      match initBytes? (bs.take (Nat.pow 2 3)) with
      | Option.none => Except.ok Option.none
      | Option.some tagRaw =>
        let tag := decodeUInt endian tagRaw
        if Nat.beq tag 0 then Except.ok (Option.some (Val.optionVal Option.none))
        else if Nat.beq tag 1 then
          match decodeValV2 endian (.int .i64 false)
              (bs.drop (Nat.pow 2 3)) with
          | Except.ok (Option.some innerV) =>
            Except.ok (Option.some (Val.optionVal (Option.some innerV)))
          | Except.ok Option.none => Except.ok Option.none
          | Except.error k => Except.error k
        else Except.ok Option.none) = Except.ok (Option.some v) at h
  cases hLen : Nat.beq bs.length (Nat.pow 2 3 + 8) with
  | false =>
    rw [ite_bool_true (b := !Nat.beq bs.length (Nat.pow 2 3 + 8))
      (by rw [hLen]; rfl)] at h
    cases h
  | true =>
    rw [ite_bool_false (b := !Nat.beq bs.length (Nat.pow 2 3 + 8))
      (by rw [hLen]; rfl)] at h
    cases hTag : initBytes? (bs.take (Nat.pow 2 3)) with
    | none => rw [hTag] at h; cases h
    | some tagRaw =>
      rw [hTag] at h; dsimp only at h
      cases hZ : Nat.beq (decodeUInt endian tagRaw) 0 with
      | true =>
        rw [ite_bool_true hZ] at h
        injection h with hv
        injection hv with hv'
        rw [← hv']
        exact ⟨none, rfl, trivial⟩
      | false =>
        rw [ite_bool_false hZ] at h
        cases hOne : Nat.beq (decodeUInt endian tagRaw) 1 with
        | false =>
          rw [ite_bool_false hOne] at h
          cases h
        | true =>
          rw [ite_bool_true hOne] at h
          cases hInner : decodeValV2 endian (.int .i64 false)
              (bs.drop (Nat.pow 2 3)) with
          | error k => rw [hInner] at h; cases h
          | ok optIn =>
            rw [hInner] at h
            cases optIn with
            | none => cases h
            | some innerV =>
              let ⟨bits, hEq, hTr⟩ := decodeValV2_u64_some hInner
              subst hEq
              injection h with hv
              injection hv with hv'
              rw [← hv']
              exact ⟨some bits, rfl, hTr⟩

private theorem option_ops_of_valid (m : MemoryState) (p : PtrVal)
    (hValid : refValidInMem m .mut (.option (.int .i64 false)) (.ptr p) =
      .ok ()) :
    refValidInMem m .shared (.option (.int .i64 false)) (.ptr p) = .ok () ∧
    ∃ optBits : Option (BitVec 128),
      (match optBits with
        | none => True
        | some b => truncateBits .i64 b = b) ∧
      loadOptionRefV2 m .shared (.int .i64 false) p =
        .ok (optBits.map (fun b => .scalar ⟨.i64, false, b⟩)) ∧
      ∃ m1, execMemReplace m (.option (.int .i64 false)) p (.optionVal none) =
        .ok (.optionVal (optBits.map (fun b => .scalar ⟨.i64, false, b⟩)), m1) := by
  unfold refValidInMem at hValid
  dsimp only at hValid
  rw [ite_bool_false (b := !isSupportedV2PointeeTy (.option (.int .i64 false))) rfl]
    at hValid
  cases hAid : p.allocId with
  | none =>
    rw [hAid] at hValid
    have hBad : (if (Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 16) = true then
        Except.error FaultKind.undefined else _) = Except.ok () := hValid
    rw [ite_bool_true (by rw [(by decide : Nat.blt 0 16 = true), Bool.or_true])]
      at hBad
    cases hBad
  | some aid =>
    rw [hAid] at hValid; dsimp only at hValid
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at hValid; cases hValid
    | some a =>
      rw [hFind, layoutOfTyV2_opt_u64] at hValid; dsimp only at hValid
      cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat 16 ||
          !isAligned a p.offsetBytes.toNat 3) with
      | true => rw [hBad] at hValid; cases hValid
      | false =>
        rw [hBad] at hValid
        cases hMut : (Mutability.beq .mut .mut &&
            !Mutability.beq a.mutability .mut) with
        | true => rw [hMut] at hValid; cases hValid
        | false =>
          rw [hMut] at hValid
          cases hDec : decodeValV2 profileV2TargetEndian
              (.option (.int .i64 false))
              ((a.bytes.drop p.offsetBytes.toNat).take 16) with
          | error k => rw [hDec] at hValid; cases hValid
          | ok optOld =>
            cases optOld with
            | none => rw [hDec] at hValid; cases hValid
            | some oldVal =>
              let ⟨optBits, hOptEq, hOptTr⟩ := decodeValV2_opt_u64_some hDec
              subst hOptEq
              have hSharedValid :
                  refValidInMem m .shared (.option (.int .i64 false)) (.ptr p) =
                    .ok () := by
                unfold refValidInMem
                dsimp only
                rw [ite_bool_false
                  (b := !isSupportedV2PointeeTy (.option (.int .i64 false))) rfl]
                rw [hAid]; dsimp only
                rw [hFind, layoutOfTyV2_opt_u64]; dsimp only
                rw [ite_bool_false hBad, ite_bool_false (by rfl)]
                rw [hDec]
              have hLoad : loadIndirectV2 m (.option (.int .i64 false))
                  ⟨aid, p.offsetBytes.toNat⟩ =
                  .ok (some (.optionVal
                    (optBits.map (fun b => .scalar ⟨.i64, false, b⟩)))) := by
                unfold loadIndirectV2
                rw [layoutOfTyV2_opt_u64]; dsimp only
                rw [readBytes_of_ok rfl hFind hBad]
                exact hDec
              have hLoadOpt : loadOptionRefV2 m .shared (.int .i64 false) p =
                  .ok (optBits.map (fun b => .scalar ⟨.i64, false, b⟩)) := by
                unfold loadOptionRefV2
                rw [ite_bool_false
                  (b := !isSizedNoRefV2Ty (.int .i64 false) ||
                    !isOptionPayloadSupportedV2 (.int .i64 false)) rfl]
                rw [hSharedValid]
                dsimp only; rw [hAid]; dsimp only; rw [hLoad]
              have hLive : a.live = true := by
                cases hL : a.live with
                | false => rw [hL] at hBad; cases hBad
                | true => rfl
              have hMutEq : a.mutability = .mut := by
                cases hM : a.mutability
                · rw [hM] at hMut; cases hMut
                · rfl
              let ⟨encBs, hEnc, hEncLen⟩ :
                  ∃ bs, encodeValV2 profileV2TargetEndian
                    (.option (.int .i64 false)) (.optionVal none) = .ok bs ∧
                    bs.length = 16 := ⟨_, rfl, rfl⟩
              have hStore : ∃ m1, storeIndirectV2 m (.option (.int .i64 false))
                  ⟨aid, p.offsetBytes.toNat⟩ (.optionVal none) = .ok m1 := by
                unfold storeIndirectV2
                rw [layoutOfTyV2_opt_u64]; dsimp only
                rw [hEnc]; dsimp only
                unfold writeBytes; dsimp only
                rw [hFind]; dsimp only
                rw [hEncLen, ite_bool_false (by decide)]
                rw [ite_bool_false hBad, hMutEq]
                exact ⟨_, rfl⟩
              let ⟨m1, hSt⟩ := hStore
              refine ⟨hSharedValid, optBits, hOptTr, hLoadOpt, m1, ?_⟩
              unfold execMemReplace
              rw [ite_bool_false (by decide)]
              have hRefsOk : (!refsValidInMem m (.option (.int .i64 false))
                  (.optionVal none)) = false := by
                dsimp only [refsValidInMem]; rfl
              rw [ite_bool_eq_false hRefsOk, layoutOfTyV2_opt_u64]; dsimp only
              rw [hAid]; dsimp only; rw [hFind]; dsimp only
              rw [ite_bool_false (by rw [hLive, hMutEq]; rfl)]
              rw [hLoad]; dsimp only; rw [hSt]

private theorem take_option_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_4 q) :
    WellFormedV2 (entryProgForBody Captured.program 4) q := by
  let ⟨hCM, hMatch, hRefs, _⟩ := hValid
  cases hArgs : q.args with
  | nil => rw [hArgs] at hMatch; cases hMatch
  | cons a0 r0 =>
    cases r0 with
    | cons _ _ =>
      rw [hArgs] at hMatch
      rw [show (Captured.body_4.locals.drop 1).take Captured.body_4.argumentCount =
          [.ref .mut (.option (.int .i64 false))] from rfl] at hMatch
      dsimp only [checkArgsMatchV2] at hMatch
      rw [Bool.and_false] at hMatch
      cases hMatch
    | nil =>
      rw [hArgs] at hMatch
      cases a0 with
      | ptr optPtr =>
        have hW : optPtr.width = .isize := by
          have hMatch' : (!isUnsizedTy (.option (.int .i64 false)) &&
              IntWidth.beq optPtr.width .isize) && true = true := hMatch
          cases hw : optPtr.width with
          | isize => rfl
          | i8 | i16 | i32 | i64 | i128 => rw [hw] at hMatch'; cases hMatch'
        cases optPtr with
        | mk optAid optOff ow =>
          dsimp only at hW; subst hW
          let optPtr : PtrVal := ⟨optAid, optOff, .isize⟩
          let m := entryMemoryWithCaller q.callerMem
          have hQ : q = ⟨[.ptr optPtr], q.callerMem⟩ := by
            cases q; dsimp only at hArgs; rw [hArgs]
          have hOptValid :
              refValidInMem m .mut (.option (.int .i64 false)) (.ptr optPtr) =
                .ok () := by
            have hRefs' : refsValidInMemList m
                [.ref .mut (.option (.int .i64 false))] [.ptr optPtr] = true := by
              rw [← hArgs]; exact hRefs
            dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
            cases h0 : refValidInMem m .mut (.option (.int .i64 false))
                (.ptr optPtr) with
            | error k => rw [h0] at hRefs'; cases hRefs'
            | ok u => cases u; rfl
          let ⟨hShValid, optBits, hOptTr, hLoadOpt, m1, hReplace⟩ :=
            option_ops_of_valid m optPtr hOptValid
          let optVal : Option Val :=
            optBits.map (fun b => Val.scalar ⟨.i64, false, b⟩)
          have hOldChk :
              checkValV2 (.optionVal optVal)
                (.option (.int .i64 false)) = true := by
            cases optBits with
            | none => rfl
            | some b => exact checkVal_int_eq hOptTr
          have hInit : initStateV2 (entryProgForBody Captured.program 4) q =
              .ok ⟨[⟨4, 0, 0, [
                .immediate none,
                .immediate (some (.ptr optPtr)),
                .dead, .dead, .dead, .dead
              ], none, none, none⟩], q.callerMem, m⟩ := by
            rw [hQ]
            have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 4)
              (q := ⟨[.ptr optPtr], q.callerMem⟩) (body := Captured.body_4)
              rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) rfl
              (by
                change refsValidInMem m (.ref .mut (.option (.int .i64 false)))
                    (.ptr optPtr) && true = true
                dsimp only [refsValidInMem]
                rw [hOptValid]; rfl)
              (by dsimp only [refAccessSpansList, refAccessSpans]
                  cases optAid <;> rfl)
            rw [h0]; rfl
          have hExec : execStateV2 (entryProgForBody Captured.program 4) 15
              ⟨[⟨4, 0, 0, [
                .immediate none,
                .immediate (some (.ptr optPtr)),
                .dead, .dead, .dead, .dead
              ], none, none, none⟩], q.callerMem, m⟩
              (fun _ => True) := by
            -- bb0 stmts 0..1: storageLive 2, 3
            apply execOutcomeStateV2_step (by rfl)
            apply execOutcomeStateV2_step (by rfl)
            -- bb0 stmt 2: assign 3 (.ref .shared [1, .deref])
            apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
              (evalRvalueV2_ref_deref_ok rfl rfl rfl rfl hShValid)
              (writePlaceV2_immediate_ok rfl rfl rfl))
            -- bb0 term: coreCall optionIsSome [move 3] -> 2, bb1
            have hIsSomeCall :
                execCoreCallWithMem m (.optionIsSome (.int .i64 false))
                  [(.ref .shared (.option (.int .i64 false)), .ptr optPtr)]
                  .bool = .ok (.bool optVal.isSome, m) := by
              unfold execCoreCallWithMem; dsimp only
              unfold execCoreContractOp
              dsimp only [MirTy.beq, IntWidth.beq]
              rw [hLoadOpt]; rfl
            apply execOutcomeStateV2_step (evalStepV2_coreCall_ok rfl rfl rfl rfl
              rfl rfl rfl
              (evalArgOperandsV2_one_move rfl rfl rfl rfl)
              hIsSomeCall
              (writePlaceV2_immediate_ok rfl rfl rfl))
            -- bb1 stmts 0..2: storageDead 3, storageLive 4, storageLive 5
            apply execOutcomeStateV2_step (by rfl)
            apply execOutcomeStateV2_step (by rfl)
            apply execOutcomeStateV2_step (by rfl)
            -- bb1 stmt 3: assign 5 (.ref .mut [1, .deref])
            apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
              (evalRvalueV2_ref_deref_ok rfl rfl rfl rfl hOptValid)
              (writePlaceV2_immediate_ok rfl rfl rfl))
            -- bb1 term: coreCall optionTake [move 5] -> 4, bb2
            have hTakeCall :
                execCoreCallWithMem m (.optionTake (.int .i64 false))
                  [(.ref .mut (.option (.int .i64 false)), .ptr optPtr)]
                  (.option (.int .i64 false)) =
                  .ok (.optionVal optVal, m1) := by
              unfold execCoreCallWithMem; dsimp only
              unfold execCoreContractOp
              exact hReplace
            apply execOutcomeStateV2_step (evalStepV2_coreCall_ok rfl rfl rfl rfl
              rfl rfl rfl
              (evalArgOperandsV2_one_move rfl rfl rfl rfl)
              hTakeCall
              (writePlaceV2_immediate_ok hOldChk rfl rfl))
            -- bb2 stmt 0: storageDead 5
            apply execOutcomeStateV2_step (by rfl)
            -- bb2 stmt 1: assign 0 (.aggregateTuple [move 2, move 4])
            have hTupChk : checkValV2
                (.tuple [.bool optVal.isSome, .optionVal optVal])
                (.tuple [.bool, .option (.int .i64 false)]) = true := by
              change checkValV2List [.bool optVal.isSome, .optionVal optVal]
                [.bool, .option (.int .i64 false)] = true
              dsimp only [checkValV2List]
              rw [hOldChk]; rfl
            apply execOutcomeStateV2_step (evalStepV2_assign_ok rfl rfl rfl rfl
              (evalRvalueV2_aggregateTuple2_move_ok rfl rfl rfl rfl rfl rfl rfl rfl
                rfl hOldChk)
              (writePlaceV2_immediate_ok hTupChk rfl rfl))
            -- bb2 stmts 2..3: storageDead 4, 2
            apply execOutcomeStateV2_step (by rfl)
            apply execOutcomeStateV2_step (by rfl)
            -- bb2 term: return_
            apply execOutcomeStateV2_done (by
              apply evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
              · cases optBits <;> rfl
              · cases optBits <;> rfl
              · cases optBits <;> rfl
              · cases optBits <;> rfl)
            exact trivial
          exact wellFormedV2_of_exec hInit hExec
      | optionVal optV => cases optV <;> cases hMatch
      | _ => cases hMatch

/-! ## Top-Level Profile v2 Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      cases hBody
      refine ⟨rfl, rfl, fun q hValid hSafe => ?_⟩
      have hSpec : Spec.subsliceSafety q := hSafe rfl
      have hRes := subslice_correct q hValid hSpec
      revert hRes
      cases q.args with
      | nil => intro h; exact False.elim h
      | cons v0 r0 =>
        cases v0 with
        | slicePtr _ _ =>
          cases r0 with
          | nil => intro h; exact False.elim h
          | cons v1 r1 =>
            cases v1 with
            | scalar _ =>
              cases r1 with
              | nil => intro h; exact False.elim h
              | cons v2 r2 =>
                cases v2 with
                | scalar _ =>
                  cases r2 with
                  | cons _ _ => intro h; exact False.elim h
                  | nil => intro h; exact h.1
                | _ => intro h; exact False.elim h
            | _ => intro h; exact False.elim h
        | _ => intro h; exact False.elim h
    | succ d1 =>
      cases d1 with
      | zero =>
        cases hBody
        refine ⟨rfl, rfl, fun q hValid hSafe => ?_⟩
        have hSpec : Spec.optUnwrapSafety q := hSafe rfl
        have hRes := opt_unwrap_correct q hValid hSpec
        revert hRes
        cases q.args with
        | nil => intro h; exact False.elim h
        | cons v0 r0 =>
          cases v0 with
          | optionVal optV =>
            cases optV with
            | none => intro h; exact False.elim h
            | some _ =>
              cases r0 with
              | cons _ _ => intro h; exact False.elim h
              | nil => intro h; exact h.1
          | _ => intro h; exact False.elim h
      | succ d2 =>
        cases d2 with
        | zero =>
          cases hBody
          exact ⟨rfl, rfl, fun q hValid _ => checked_scalar_correct q hValid⟩
        | succ d3 =>
          cases d3 with
          | zero =>
            cases hBody
            exact ⟨rfl, rfl, fun q hValid _ => slice_and_replace_correct q hValid⟩
          | succ d4 =>
            cases d4 with
            | zero =>
              cases hBody
              exact ⟨rfl, rfl, fun q hValid _ => take_option_correct q hValid⟩
            | succ _ => cases hBody
  · refine ⟨?_, ?_⟩
    · refine ⟨0, Captured.body_0, rfl, rfl, ?_⟩
      intro q hValid hSafe
      have hRes := subslice_correct q hValid hSafe
      revert hRes
      cases q.args with
      | nil => intro h; exact False.elim h
      | cons v0 r0 =>
        cases v0 with
        | slicePtr _ _ =>
          cases r0 with
          | nil => intro h; exact False.elim h
          | cons v1 r1 =>
            cases v1 with
            | scalar _ =>
              cases r1 with
              | nil => intro h; exact False.elim h
              | cons v2 r2 =>
                cases v2 with
                | scalar _ =>
                  cases r2 with
                  | cons _ _ => intro h; exact False.elim h
                  | nil => intro h; exact h.2
                | _ => intro h; exact False.elim h
            | _ => intro h; exact False.elim h
        | _ => intro h; exact False.elim h
    · refine ⟨1, Captured.body_1, rfl, rfl, ?_⟩
      intro q hValid hSafe
      have hRes := opt_unwrap_correct q hValid hSafe
      revert hRes
      cases q.args with
      | nil => intro h; exact False.elim h
      | cons v0 r0 =>
        cases v0 with
        | optionVal optV =>
          cases optV with
          | none => intro h; exact False.elim h
          | some _ =>
            cases r0 with
            | cons _ _ => intro h; exact False.elim h
            | nil => intro h; exact h.2
        | _ => intro h; exact False.elim h

end Proof
