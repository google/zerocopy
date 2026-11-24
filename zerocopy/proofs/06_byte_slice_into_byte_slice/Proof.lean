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
import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Step Helpers -/

theorem execOutcomeStateV2_step {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s s' : State}
    (hStep : evalStepV2 p s = .step s')
    (hNext : execOutcomeStateV2 p onDone onFault fuel s') :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hNext

theorem execOutcomeStateV2_done {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStepV2 p s = .done out)
    (hDone : onDone out) :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hDone

/-! ## Caller Memory Preservation -/

theorem natNotElem_cons_ne {x y : Nat} {ys : List Nat} :
    natNotElem x (y :: ys) = true → x ≠ y ∧ natNotElem x ys = true := by
  intro h
  unfold natNotElem at h
  cases hEq : Nat.beq x y with
  | true =>
    rw [hEq] at h
    cases h
  | false =>
    rw [hEq] at h
    exact ⟨(fun hxy => by subst hxy; rw [Nat.beq_refl] at hEq; cases hEq), h⟩

theorem findAllocation_append_of_not_in_prefix
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

theorem natNotElem_iff_not_mem (x : Nat) :
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

theorem extractCallerAllocations_suffix (m : MemoryState) :
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

theorem natNotElem_of_forall_ne {x : Nat} :
    ∀ {xs : List Nat}, (∀ y, y ∈ xs → x ≠ y) → natNotElem x xs = true :=
  fun h => (natNotElem_iff_not_mem x _).mpr h

theorem mem_map_reverse_append {x : Allocation} {pref : List Allocation}
    {y : AllocId}
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

theorem mem_map_self_append (pref : List Allocation) (x : Allocation) :
    x.allocId ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => exact .head _
  | cons _ _ ih => exact .tail _ ih

theorem mem_map_append_left {pref : List Allocation} {x : Allocation}
    {w : AllocId}
    (h : w ∈ pref.map Allocation.allocId) :
    w ∈ (pref ++ [x]).map Allocation.allocId := by
  induction pref with
  | nil => cases h
  | cons _ _ ih =>
    cases h with
    | head _ => exact .head _
    | tail _ h' => exact .tail _ (ih h')

theorem findAllocation_in_allocIdsValid (pref : List Allocation) :
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
              have hForall :=
                (natNotElem_iff_not_mem x.allocId seen).mp hNotElem
              have hNotPref :
                  natNotElem x.allocId (pref.map Allocation.allocId) = true :=
                natNotElem_of_forall_ne
                  (fun y hy => hForall y (hPrefSub y hy))
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
                    exact (natNotElem_iff_not_mem x.allocId _).mp hNot
                      x.allocId (mem_map_self_append pref x) rfl
                  | tail _ hZ =>
                    exact hSeenSub z hZ (natNotElem_of_forall_ne
                      (fun w hw => (natNotElem_iff_not_mem z _).mp hNot w
                        (mem_map_append_left hw))))
                (fun z hz => by
                  cases mem_map_reverse_append hz with
                  | inl hEqZ => subst hEqZ; exact .head _
                  | inr hInP => exact .tail _ (hPrefSub z hInP))
                hValid a hIn

theorem extractCallerMemory_entry (cm : CallerMemory)
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

/-! ## Byte-Slice Reference Validity -/

/-- Mutable slice validity implies shared slice validity: the only check that
depends on `isMut` is the allocation-mutability check, which a shared borrow
skips. -/
theorem sliceCheck_shared_of_mut {m : MemoryState} {sz al : Nat}
    {p : PtrVal} {len : UInt64} {v : Val}
    (h : sliceFromRawPartsCheck m true sz al p len = .ok v) :
    sliceFromRawPartsCheck m false sz al p len = .ok v := by
  unfold sliceFromRawPartsCheck at h ⊢
  try dsimp only at h ⊢
  cases hMax : Nat.blt (len.toNat * sz) isizeMaxBytes with
  | false => rw [hMax] at h; cases h
  | true =>
    rw [hMax] at h
    try dsimp only at h ⊢
    cases hAid : p.allocId with
    | none => rw [hAid] at h; exact h
    | some aid =>
      rw [hAid] at h
      try dsimp only at h ⊢
      cases hFind : findAllocation aid m.allocations with
      | none => rw [hFind] at h; cases h
      | some a =>
        rw [hFind] at h
        try dsimp only at h ⊢
        revert h
        cases (!a.live || !isInBounds a p.offsetBytes.toNat (len.toNat * sz) ||
            !isAligned a p.offsetBytes.toNat al) <;>
          cases Mutability.beq a.mutability .mut <;>
          cases isSliceAllInit
            ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * sz)) <;>
          intro h <;> first | exact h | cases h

theorem refValid_shared_of_mut {m : MemoryState} {ptr : PtrVal} {len : UInt64}
    (h : refValidInMem m .mut (.slice (.int .i8 false)) (.slicePtr ptr len) =
      .ok ()) :
    refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr ptr len) =
      .ok () := by
  unfold refValidInMem at h ⊢
  dsimp only [intLayout] at h ⊢
  cases hChk : sliceFromRawPartsCheck m (Mutability.beq .mut .mut) 1 0 ptr
      len with
  | error k =>
    rw [hChk] at h
    cases h
  | ok v =>
    have hSh : sliceFromRawPartsCheck m (Mutability.beq .shared .mut) 1 0 ptr
        len = .ok v :=
      sliceCheck_shared_of_mut hChk
    rw [hSh]

theorem refsStayInCallerMem_of_refValid {cm : CallerMemory}
    {reqMut retMut : Mutability} {ptr : PtrVal} {len : UInt64}
    (h : refValidInMem (entryMemoryWithCaller cm) reqMut
      (.slice (.int .i8 false)) (.slicePtr ptr len) = .ok ()) :
    refsStayInCallerMem cm (.ref retMut (.slice (.int .i8 false)))
      (.slicePtr ptr len) = true := by
  unfold refsStayInCallerMem
  dsimp only [refAllocIds]
  cases hAid : ptr.allocId with
  | none => rfl
  | some aid =>
    unfold refValidInMem sliceFromRawPartsCheck at h
    dsimp only [intLayout] at h
    cases hMax : Nat.blt (len.toNat * 1) isizeMaxBytes with
    | false => rw [hMax] at h; cases h
    | true =>
      rw [hMax, hAid] at h
      dsimp only at h
      cases hFind :
          findAllocation aid (entryMemoryWithCaller cm).allocations with
      | none => rw [hFind] at h; cases h
      | some a =>
        change ((findAllocation aid
          (entryMemoryWithCaller cm).allocations).isSome && true) = true
        rw [hFind]
        rfl

theorem refsValidInMem_of_refValid {m : MemoryState} {reqMut : Mutability}
    {ptr : PtrVal} {len : UInt64}
    (h : refValidInMem m reqMut (.slice (.int .i8 false)) (.slicePtr ptr len) =
      .ok ()) :
    refsValidInMem m (.ref reqMut (.slice (.int .i8 false)))
      (.slicePtr ptr len) = true := by
  dsimp only [refsValidInMem]
  rw [h]

theorem spansDisjoint_single {reqMut : Mutability} {ptr : PtrVal}
    {len : UInt64} :
    spansPairwiseDisjoint
      (refAccessSpans (.ref reqMut (.slice (.int .i8 false)))
        (.slicePtr ptr len)) = true := by
  dsimp only [refAccessSpans]
  cases ptr.allocId <;> rfl

/-! ## Entry Inversion -/

theorem checkValV2_slice_u8_inv {reqMut : Mutability} {v : Val}
    (h : checkValV2 v (.ref reqMut (.slice (.int .i8 false))) = true) :
    ∃ ptr len, v = .slicePtr ptr len ∧ ptr.width = .isize := by
  cases v with
  | slicePtr ptr len =>
    change IntWidth.beq ptr.width .isize = true at h
    cases hW : ptr.width with
    | i8 | i16 | i32 | i64 | i128 => rw [hW] at h; cases h
    | isize => exact ⟨ptr, len, rfl, hW⟩
  | scalar _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
  | rangeTo _ | rangeFrom _ | tuple _ | bytes _ => cases h

theorem checkArgsMatchV2_slice_u8_inv {reqMut : Mutability} {args : List Val}
    (h : checkArgsMatchV2 args [.ref reqMut (.slice (.int .i8 false))] =
      true) :
    ∃ (ptrAid : Option AllocId) (ptrOff : UInt64) (len : UInt64),
      args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len] := by
  cases args with
  | nil => cases h
  | cons v0 rest =>
    cases rest with
    | cons _ _ =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 (.ref reqMut (.slice (.int .i8 false))) <;>
        rw [hV0] at h <;> cases h
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 (.ref reqMut (.slice (.int .i8 false))) with
      | false => rw [hV0] at h; cases h
      | true =>
        let ⟨ptr, len, hv0, hPtrW⟩ := checkValV2_slice_u8_inv hV0
        subst hv0
        cases ptr with
        | mk ptrAid ptrOff ptrW =>
          dsimp only at hPtrW
          subst hPtrW
          exact ⟨ptrAid, ptrOff, len, rfl⟩

/-- Inverts `ValidEntryArgsV2` for a body whose single parameter is a
`&[u8]` or `&mut [u8]` reference. -/
theorem entry_inv {body : Body} {reqMut : Mutability} {q : Query}
    (hParams : (body.locals.drop 1).take body.argumentCount =
      [.ref reqMut (.slice (.int .i8 false))])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ (ptrAid : Option AllocId) (ptrOff : UInt64) (len : UInt64),
      q.args = [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len] ∧
      validCallerMemory q.callerMem = true ∧
      refValidInMem (entryMemoryWithCaller q.callerMem) reqMut
        (.slice (.int .i8 false)) (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len) =
        .ok () := by
  let ⟨hCM, hMatch, hRefs, _⟩ := hValid
  have hMatch' :
      checkArgsMatchV2 q.args [.ref reqMut (.slice (.int .i8 false))] = true :=
    by rw [← hParams]; exact hMatch
  let ⟨ptrAid, ptrOff, len, hArgs⟩ := checkArgsMatchV2_slice_u8_inv hMatch'
  refine ⟨ptrAid, ptrOff, len, hArgs, hCM, ?_⟩
  have hRefs' :
      refsValidInMemList (entryMemoryWithCaller q.callerMem)
        [.ref reqMut (.slice (.int .i8 false))]
        [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len] = true := by
    rw [← hArgs, ← hParams]; exact hRefs
  dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
  cases hR : refValidInMem (entryMemoryWithCaller q.callerMem) reqMut
      (.slice (.int .i8 false)) (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len) with
  | error k => rw [hR] at hRefs'; cases hRefs'
  | ok u => cases u; rfl

/-! ## Evaluation Helpers -/

theorem readPlaceV2_copy_local {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId} {ty : MirTy}
    {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate optVal))
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

theorem evalRvalueV2_useRetag_copy_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {ty : MirTy} {lid : LocalId}
    {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy ty = true)
    (hEq : MirTy.beq ty ty = true)
    (hRV : refsValidInMem mem ty v = true) :
    evalRvalueV2 bodyLocals locals mem ty (.useRetag (.copy ⟨lid, []⟩)) =
      .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [hEq, hRV]
  rfl

theorem initStateV2_ok_of {p : Program} {q : Query} {body : Body}
    (hPW : Nat.beq p.pointerWidthBits 64 = true)
    (hPV : Nat.beq p.mirProfileVersion 2 = true)
    (hCM : validCallerMemory q.callerMem = true)
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hNonEmpty : body.basicBlocks.isEmpty = false)
    (hArgLt : Nat.blt body.argumentCount body.locals.length = true)
    (hSto : storageAnnotationsInBounds body = true)
    (hDiscr : discriminantTypesValid body = true)
    (hCast : castTypesValid body = true)
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hArgs : checkArgsMatchV2 q.args
      ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0,
      initLocalsLoop body q.args 0 body.locals⟩],
      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  unfold initStateV2
  rw [hPW, hPV, hCM, hEntry]
  dsimp only
  rw [hNonEmpty, hArgLt, hSto, hDiscr, hCast, hLocs]
  rw [hArgs, hRefs, hDisj]
  rfl

theorem writePlaceDestV2_immediate_ok {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {val : Val}
    {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) =
      some locals') :
    writePlaceDestV2 locals mem (.local lid) ty val = .ok (locals', mem) := by
  unfold writePlaceDestV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]

theorem evalRefRvalueV2_deref_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {srcMut reqMut : Mutability} {pt : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some (.ref srcMut pt))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hMut : (Mutability.beq srcMut .shared && Mutability.beq reqMut .mut) =
      false)
    (hDst : MirTy.beq (.ref reqMut pt) (.ref reqMut pt) = true)
    (hRef : refValidInMem mem reqMut pt v = .ok ()) :
    evalRefRvalueV2 bodyLocals locals mem (.ref reqMut pt) reqMut
      ⟨lid, [.deref]⟩ = .ok (v, locals, mem) := by
  unfold evalRefRvalueV2
  rw [hTy, hSlot]
  dsimp only
  rw [ite_bool_false hMut]
  rw [ite_bool_false (by rw [hDst]; rfl)]
  rw [hRef]

theorem evalTerminatorV2_return_ok {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : MemoryState} {callerMem : CallerMemory}
    {retTy : MirTy} {retVal : Val}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalTerminatorV2 body bb frame mem callerMem =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]

/-- Converts an exact-outcome execution into the `Spec.stableBodyPost`
conclusion for one query. -/
theorem stable_of_exec {p : Program} {defId : DefId} {q : Query}
    {fuel : Nat} {ptr : PtrVal} {len : UInt64}
    (hArgs : q.args = [.slicePtr ptr len])
    (hExec : execProgV2 (entryProgForBody p defId) fuel q
      (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩)) :
    WellFormedV2 (entryProgForBody p defId) q ∧
    match q.args with
    | [.slicePtr ptr len] =>
      let out := TerminalOut.returned ⟨.slicePtr ptr len, q.callerMem⟩
      BehaviorV2 (entryProgForBody p defId) q out ∧
      SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)
    | _ => False := by
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  rw [hArgs]
  exact ⟨hRes.1, hRes.2.1, hRes.2.2.2 _ rfl⟩

/-! ## Per-Body Correctness -/

/-- `<&[u8] as IntoByteSlice>::into_byte_slice`: `_0 = useRetag(copy _1)`. -/
theorem body0_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    ∃ ptr len, q.args = [.slicePtr ptr len] ∧
      execProgV2 (entryProgForBody Captured.program 0) 8 q
        (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩) := by
  let ⟨ptrAid, ptrOff, len, hArgs, hCM, hRef⟩ :=
    entry_inv (reqMut := .shared) rfl hValid
  let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  refine ⟨ptr, len, hArgs, ?_⟩
  have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hRV := refsValidInMem_of_refValid hRef
  have hStay : refsStayInCallerMem q.callerMem
      (.ref .shared (.slice (.int .i8 false))) (.slicePtr ptr len) = true :=
    refsStayInCallerMem_of_refValid hRef
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  have hInit :
      initStateV2 (entryProgForBody Captured.program 0)
        ⟨[.slicePtr ptr len], q.callerMem⟩ =
      .ok (State.mk [FrameState.mk 0 0 0
        [.immediate none, .immediate (some (.slicePtr ptr len))]]
        q.callerMem m) := by
    have hRefsList :
        refsValidInMemList m
          ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount)
          [.slicePtr ptr len] = true := by
      change refsValidInMemList m [.ref .shared (.slice (.int .i8 false))]
        [.slicePtr ptr len] = true
      dsimp only [refsValidInMemList]
      rw [hRV]
      rfl
    have hDisjList :
        spansPairwiseDisjoint
          (refAccessSpansList
            ((Captured.body_0.locals.drop 1).take
              Captured.body_0.argumentCount)
            [.slicePtr ptr len]) = true := by
      change spansPairwiseDisjoint
        (refAccessSpansList [.ref .shared (.slice (.int .i8 false))]
          [.slicePtr ptr len]) = true
      dsimp only [refAccessSpansList, refAccessSpans]
      cases ptrAid <;> rfl
    exact initStateV2_ok_of (p := entryProgForBody Captured.program 0)
      (q := ⟨[.slicePtr ptr len], q.callerMem⟩) (body := Captured.body_0)
      rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl hRefsList hDisjList
  rw [hQ]
  unfold execProgV2
  rw [hInit]
  -- bb0 stmt 0: _0 = useRetag(copy _1)
  apply execOutcomeStateV2_step (by
    dsimp only [evalStepV2, entryProgForBody, Captured.program,
      Captured.body_0, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
      Trusted.MirSemantics.getElem?]
    rw [evalRvalueV2_useRetag_copy_ok (by rfl) (by rfl) (by rfl) (by rfl) hRV]
    dsimp only
    rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
  -- bb0 term: return_
  apply execOutcomeStateV2_done (by
    dsimp only [evalStepV2, entryProgForBody, Captured.program,
      Captured.body_0, Trusted.MirSemantics.getElem?]
    rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl) hStay
      hRV spansDisjoint_single, hExt]
    rfl)
  rfl

/-- `<&mut [u8] as IntoByteSlice>::into_byte_slice`: `_0 = &(*_1)`. -/
theorem body1_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    ∃ ptr len, q.args = [.slicePtr ptr len] ∧
      execProgV2 (entryProgForBody Captured.program 1) 8 q
        (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩) := by
  let ⟨ptrAid, ptrOff, len, hArgs, hCM, hRefMut⟩ :=
    entry_inv (reqMut := .mut) rfl hValid
  let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  refine ⟨ptr, len, hArgs, ?_⟩
  have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hRef := refValid_shared_of_mut hRefMut
  have hRVMut := refsValidInMem_of_refValid hRefMut
  have hRV := refsValidInMem_of_refValid hRef
  have hStay : refsStayInCallerMem q.callerMem
      (.ref .shared (.slice (.int .i8 false))) (.slicePtr ptr len) = true :=
    refsStayInCallerMem_of_refValid hRef
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  have hInit :
      initStateV2 (entryProgForBody Captured.program 1)
        ⟨[.slicePtr ptr len], q.callerMem⟩ =
      .ok (State.mk [FrameState.mk 1 0 0
        [.immediate none, .immediate (some (.slicePtr ptr len))]]
        q.callerMem m) := by
    have hRefsList :
        refsValidInMemList m
          ((Captured.body_1.locals.drop 1).take Captured.body_1.argumentCount)
          [.slicePtr ptr len] = true := by
      change refsValidInMemList m [.ref .mut (.slice (.int .i8 false))]
        [.slicePtr ptr len] = true
      dsimp only [refsValidInMemList]
      rw [hRVMut]
      rfl
    have hDisjList :
        spansPairwiseDisjoint
          (refAccessSpansList
            ((Captured.body_1.locals.drop 1).take
              Captured.body_1.argumentCount)
            [.slicePtr ptr len]) = true := by
      change spansPairwiseDisjoint
        (refAccessSpansList [.ref .mut (.slice (.int .i8 false))]
          [.slicePtr ptr len]) = true
      dsimp only [refAccessSpansList, refAccessSpans]
      cases ptrAid <;> rfl
    exact initStateV2_ok_of (p := entryProgForBody Captured.program 1)
      (q := ⟨[.slicePtr ptr len], q.callerMem⟩) (body := Captured.body_1)
      rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl hRefsList hDisjList
  rw [hQ]
  unfold execProgV2
  rw [hInit]
  -- bb0 stmt 0: _0 = &(*_1)
  apply execOutcomeStateV2_step (by
    dsimp only [evalStepV2, entryProgForBody, Captured.program,
      Captured.body_1, evalStatementV2, resolvePlaceDestV2,
      placeStaticTyV2, evalRvalueV2,
      Trusted.MirSemantics.getElem?]
    rw [evalRefRvalueV2_deref_ok (by rfl) (by rfl) (by rfl) (by rfl) hRef]
    dsimp only
    rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
  -- bb0 term: return_
  apply execOutcomeStateV2_done (by
    dsimp only [evalStepV2, entryProgForBody, Captured.program,
      Captured.body_1, Trusted.MirSemantics.getElem?]
    rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl) hStay
      hRV spansDisjoint_single, hExt]
    rfl)
  rfl

/-- `<&mut [u8] as IntoByteSliceMut>::into_byte_slice_mut`:
`StorageLive 2; _2 = &mut (*_1); _0 = &mut (*_2); StorageDead 2`. -/
theorem body2_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q) :
    ∃ ptr len, q.args = [.slicePtr ptr len] ∧
      execProgV2 (entryProgForBody Captured.program 2) 8 q
        (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩) := by
  let ⟨ptrAid, ptrOff, len, hArgs, hCM, hRef⟩ :=
    entry_inv (reqMut := .mut) rfl hValid
  let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  refine ⟨ptr, len, hArgs, ?_⟩
  have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hRV := refsValidInMem_of_refValid hRef
  have hStay : refsStayInCallerMem q.callerMem
      (.ref .mut (.slice (.int .i8 false))) (.slicePtr ptr len) = true :=
    refsStayInCallerMem_of_refValid hRef
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  have hInit :
      initStateV2 (entryProgForBody Captured.program 2)
        ⟨[.slicePtr ptr len], q.callerMem⟩ =
      .ok (State.mk [FrameState.mk 2 0 0
        [.immediate none, .immediate (some (.slicePtr ptr len)), .dead]]
        q.callerMem m) := by
    have hRefsList :
        refsValidInMemList m
          ((Captured.body_2.locals.drop 1).take Captured.body_2.argumentCount)
          [.slicePtr ptr len] = true := by
      change refsValidInMemList m [.ref .mut (.slice (.int .i8 false))]
        [.slicePtr ptr len] = true
      dsimp only [refsValidInMemList]
      rw [hRV]
      rfl
    have hDisjList :
        spansPairwiseDisjoint
          (refAccessSpansList
            ((Captured.body_2.locals.drop 1).take
              Captured.body_2.argumentCount)
            [.slicePtr ptr len]) = true := by
      change spansPairwiseDisjoint
        (refAccessSpansList [.ref .mut (.slice (.int .i8 false))]
          [.slicePtr ptr len]) = true
      dsimp only [refAccessSpansList, refAccessSpans]
      cases ptrAid <;> rfl
    exact initStateV2_ok_of (p := entryProgForBody Captured.program 2)
      (q := ⟨[.slicePtr ptr len], q.callerMem⟩) (body := Captured.body_2)
      rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl hRefsList hDisjList
  rw [hQ]
  unfold execProgV2
  rw [hInit]
  -- bb0 stmt 0: StorageLive 2
  apply execOutcomeStateV2_step (by rfl)
  -- bb0 stmt 1: _2 = &mut (*_1)
  apply execOutcomeStateV2_step (by
    dsimp only [evalStepV2, entryProgForBody, Captured.program,
      Captured.body_2, evalStatementV2, resolvePlaceDestV2,
      placeStaticTyV2, evalRvalueV2,
      Trusted.MirSemantics.getElem?]
    rw [evalRefRvalueV2_deref_ok (by rfl) (by rfl) (by rfl) (by rfl) hRef]
    dsimp only
    rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
  -- bb0 stmt 2: _0 = &mut (*_2)
  apply execOutcomeStateV2_step (by
    dsimp only [evalStepV2, entryProgForBody, Captured.program,
      Captured.body_2, evalStatementV2, resolvePlaceDestV2,
      placeStaticTyV2, evalRvalueV2,
      Trusted.MirSemantics.getElem?]
    rw [evalRefRvalueV2_deref_ok (by rfl) (by rfl) (by rfl) (by rfl) hRef]
    dsimp only
    rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
  -- bb0 stmt 3: StorageDead 2
  apply execOutcomeStateV2_step (by rfl)
  -- bb0 term: return_
  apply execOutcomeStateV2_done (by
    dsimp only [evalStepV2, entryProgForBody, Captured.program,
      Captured.body_2, Trusted.MirSemantics.getElem?]
    rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl) hStay
      hRV spansDisjoint_single, hExt]
    rfl)
  rfl

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, ?_⟩
      intro q hValid _
      let ⟨_, _, hArgs, hExec⟩ := body0_correct q hValid
      exact (stable_of_exec hArgs hExec).1
    | succ d =>
      cases d with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        refine ⟨rfl, by decide, ?_⟩
        intro q hValid _
        let ⟨_, _, hArgs, hExec⟩ := body1_correct q hValid
        exact (stable_of_exec hArgs hExec).1
      | succ d =>
        cases d with
        | zero =>
          change some Captured.body_2 = some body at hBody
          cases hBody
          refine ⟨rfl, by decide, ?_⟩
          intro q hValid _
          let ⟨_, _, hArgs, hExec⟩ := body2_correct q hValid
          exact (stable_of_exec hArgs hExec).1
        | succ _ =>
          change none = some body at hBody
          cases hBody
  · refine ⟨?_, ?_, ?_⟩
    · intro q hValid
      let ⟨_, _, hArgs, hExec⟩ := body0_correct q hValid
      exact (stable_of_exec hArgs hExec).2
    · intro q hValid
      let ⟨_, _, hArgs, hExec⟩ := body1_correct q hValid
      exact (stable_of_exec hArgs hExec).2
    · intro q hValid
      let ⟨_, _, hArgs, hExec⟩ := body2_correct q hValid
      exact (stable_of_exec hArgs hExec).2

end Proof
