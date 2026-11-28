-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Nat.Lemmas
import Init.Data.Int.Order
import Anneal.MirWp
import Anneal.MirWp.V2Memory
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

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
    (hStep : evalStepV2 p s = .done out)
    (hDone : onDone out) :
    execOutcomeStateV2 p onDone onFault (fuel + 1) s := by
  change (match evalStepV2 p s with
    | .step st' => execOutcomeStateV2 p onDone onFault fuel st'
    | .done out => onDone out
    | .fault k => onFault k)
  rw [hStep]
  exact hDone

private theorem allocId_le_maxAllocId {allocs : List Allocation} {a : Allocation}
    (h : a ∈ allocs) :
    a.allocId ≤ maxAllocId allocs := by
  induction allocs with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head _ =>
      change a.allocId ≤ Nat.max a.allocId (maxAllocId xs)
      exact Nat.le_max_left _ _
    | tail _ hIn =>
      change a.allocId ≤ Nat.max x.allocId (maxAllocId xs)
      exact Nat.le_trans (ih hIn) (Nat.le_max_right _ _)

private theorem findAllocation_cons_ne {aid : AllocId} {x : Allocation}
    {xs : List Allocation} (hNe : x.allocId ≠ aid) :
    findAllocation aid (x :: xs) = findAllocation aid xs := by
  change (if Nat.beq x.allocId aid then some x else findAllocation aid xs) =
    findAllocation aid xs
  cases hEq : Nat.beq x.allocId aid with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe

private theorem extractCallerMemory_cons_fresh {cm : CallerMemory}
    {x : Allocation} (hGt : maxAllocId cm.allocations < x.allocId)
    {next : AllocId} :
    extractCallerMemory cm { nextAllocId := next, allocations := x :: cm.allocations } =
      extractCallerMemory cm (entryMemoryWithCaller cm) := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    apply congrArg CallerMemory.mk
    have hEq : ∀ suff : List Allocation,
        (∀ a, a ∈ suff → a.allocId ≤ maxAllocId allocs) →
        extractCallerAllocations
          { nextAllocId := next, allocations := x :: allocs } suff =
          extractCallerAllocations (entryMemoryWithCaller ⟨allocs⟩) suff := by
      intro suff hBound
      induction suff with
      | nil => rfl
      | cons a rest ih =>
        unfold extractCallerAllocations
        have hLe : a.allocId ≤ maxAllocId allocs := hBound a (.head _)
        have hNe : x.allocId ≠ a.allocId :=
          Nat.ne_of_gt (Nat.lt_of_le_of_lt hLe hGt)
        rw [findAllocation_cons_ne hNe]
        change (findAllocation a.allocId allocs).getD a :: _ = _
        rw [ih (fun b hb => hBound b (.tail _ hb))]
        rfl
    exact hEq allocs (fun a ha => allocId_le_maxAllocId ha)

private theorem checkVal_u8_inv {v : Val}
    (h : checkValV2 v (.int .i8 false) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨.i8, false, bits⟩ ∧
      ScalarVal.wf ⟨.i8, false, bits⟩ = true ∧
      (!checkValV2 (.scalar ⟨.i8, false, bits⟩) (.int .i8 false)) = false := by
  cases v with
  | scalar sv =>
    cases sv with
    | mk w sg bits =>
      have h' :
          (match (if ScalarVal.wf { width := w, signed := sg, bits := bits } =
              true then some (MirTy.int w sg) else none) with
            | some vTy => vTy.beq (.int .i8 false)
            | none => false) = true := h
      cases hWf : ScalarVal.wf { width := w, signed := sg, bits := bits } with
      | false => rw [hWf] at h'; cases h'
      | true =>
        rw [hWf] at h'
        cases w <;> cases sg <;> cases h'
        exact ⟨bits, rfl, hWf, by rw [h]; rfl⟩
  | _ => first | cases h | (rename_i o; cases o <;> cases h)

private theorem checkArgs_u8 {args : List Val}
    (h : checkArgsMatchV2 args [.int .i8 false] = true) :
    ∃ bits : BitVec 128,
      args = [.scalar ⟨.i8, false, bits⟩] ∧
      ScalarVal.wf ⟨.i8, false, bits⟩ = true ∧
      (!checkValV2 (.scalar ⟨.i8, false, bits⟩) (.int .i8 false)) = false := by
  cases args with
  | nil => cases h
  | cons a0 rest =>
    cases rest with
    | cons a1 rest1 =>
      unfold checkArgsMatchV2 at h
      cases h0 : checkValV2 a0 (.int .i8 false) <;> rw [h0] at h <;> cases h
    | nil =>
      unfold checkArgsMatchV2 at h
      cases h0 : checkValV2 a0 (.int .i8 false) with
      | false => rw [h0] at h; cases h
      | true =>
        let ⟨bits, hEq, hWf, hNot⟩ := checkVal_u8_inv h0
        exact ⟨bits, by rw [hEq], hWf, hNot⟩

private theorem rm2_natNotElem_false_of_mem {x : Nat} {xs : List Nat}
    (h : x ∈ xs) : natNotElem x xs = false := by
  induction h with
  | head _ =>
    unfold natNotElem
    rw [Nat.beq_refl]
    rfl
  | tail _ _ ih =>
    unfold natNotElem
    rw [ih, Bool.and_false]

private theorem rm2_mem_allocIdsOf {a : Allocation} {l : List Allocation}
    (h : a ∈ l) : a.allocId ∈ allocIdsOf l := by
  induction h with
  | head _ => unfold allocIdsOf; exact .head _
  | tail _ _ ih => unfold allocIdsOf; exact .tail _ ih

private theorem rm2_calleeLive_nil_of_sub {ids f : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids) →
      calleeLiveAllocations ids f l = []
  | [], _ => rfl
  | a :: _, h => by
    unfold calleeLiveAllocations
    rw [rm2_natNotElem_false_of_mem (h a (.head _)), Bool.and_false,
      Bool.false_and]
    exact rm2_calleeLive_nil_of_sub (fun b hb => h b (.tail _ hb))

/-- Returning from an unmodified entry memory exposes no callee-created heap
allocation, so the Profile v2 return memory is the extracted caller memory. -/
private theorem rm2_extractReturnMemoryV2_entry (cm : CallerMemory)
    (locals : List LocalSlot) :
    extractReturnMemoryV2 cm (entryMemoryWithCaller cm) locals =
      extractCallerMemory cm (entryMemoryWithCaller cm) := by
  unfold extractReturnMemoryV2
  rw [rm2_calleeLive_nil_of_sub (ids := allocIdsOf cm.allocations)
      (l := (entryMemoryWithCaller cm).allocations)
      (fun _ ha => rm2_mem_allocIdsOf (l := cm.allocations) ha),
    List.append_nil]

private def mkS (bb st : Nat) (locs : List LocalSlot)
    (cm : CallerMemory) (mem : MemoryState) : State :=
  ⟨[⟨0, bb, st, locs, none, none, none⟩], cm, mem⟩

private theorem body0_static_admitted :
    BodyStaticAdmittedV2 Captured.program Captured.body_0 = true := by
  decide

private theorem ite_bool_false {α : Type _} {b : Bool} {t e : α}
    (h : b = false) :
    (if b = true then t else e) = e := by
  rw [h]; rfl

private theorem body0_safeContract :
    BodySatisfiesSafeContractV2 Captured.program 0 Captured.body_0
      Spec.ebpfRegAllowAbort := by
  refine safeContract_soundness_of_execV2_base.2.1
    Captured.program 0 Captured.body_0 Spec.ebpfRegAllowAbort
    rfl body0_static_admitted (fun q hValid _ => ?_)
  cases q with
  | mk args cm =>
    let ⟨hMem, hArgs, _, _⟩ := hValid
    let ⟨bits, hEq, hWf, hSv⟩ := checkArgs_u8 hArgs
    subst hEq
    let sv : ScalarVal := ⟨.i8, false, bits⟩
    have hTr : truncateBits .i8 bits = bits := by
      unfold ScalarVal.wf at hWf
      exact eq_of_beq hWf
    let mem := entryMemoryWithCaller cm
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.scalar sv], cm⟩ =
        .ok (mkS 0 0
          [.immediate none, .immediate (some (.scalar sv)),
           .dead, .dead, .dead, .dead]
          cm mem) :=
      initStateV2_ok_of_admitted (p := entryProgForBody Captured.program 0)
        rfl body0_static_admitted hValid
    have hCopy4 :
        evalStepV2 (entryProgForBody Captured.program 0)
          (mkS 0 3 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate none, .immediate none, .dead] cm mem) =
        .step (mkS 0 4 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate none,
            .immediate (some (.scalar sv)), .dead] cm mem) := by
      change (match (if (!checkValV2 (Val.scalar sv) (MirTy.int IntWidth.i8 false)) = true then
          Except.error FaultKind.unsupported
        else
          Except.ok
            ([LocalSlot.immediate none, LocalSlot.immediate (some (Val.scalar sv)),
              LocalSlot.immediate (some Val.unit), LocalSlot.immediate none,
              LocalSlot.immediate (some (Val.scalar sv)), LocalSlot.dead], mem)) with
        | Except.error k => StepResult.fault k
        | Except.ok (locals', mem') => StepResult.step (mkS 0 4 locals' cm mem')) = _
      rw [hSv]
      rfl
    let bLt : Bool :=
      decide (Int.ofNat (truncateBits .i8 bits).toNat < Int.ofNat 16)
    have hLtStep :
        evalStepV2 (entryProgForBody Captured.program 0)
          (mkS 0 4 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate none,
            .immediate (some (.scalar sv)), .dead] cm mem) =
        .step (mkS 0 5 [.immediate none, .immediate (some (.scalar sv)),
            .immediate (some .unit), .immediate (some (.bool bLt)),
            .immediate none, .dead] cm mem) := by
      have hBin :
          evalBinOp .lt (.scalar sv)
            (.scalar ⟨.i8, false, BitVec.ofNat 128 16⟩) =
          .ok (.bool bLt) := rfl
      change (match (match evalBinOp .lt (.scalar sv)
            (.scalar ⟨.i8, false, BitVec.ofNat 128 16⟩) with
          | Except.error k => Except.error k
          | Except.ok res =>
            Except.ok (res,
              [LocalSlot.immediate none, LocalSlot.immediate (some (Val.scalar sv)),
               LocalSlot.immediate (some Val.unit), LocalSlot.immediate none,
               LocalSlot.immediate none, LocalSlot.dead], mem)) with
        | Except.error k => StepResult.fault k
        | Except.ok (val, locals1, mem1) =>
          match writePlaceDestV2 locals1 mem1 (.local 3) .bool val with
          | Except.error k => StepResult.fault k
          | Except.ok (locals2, mem2) =>
            StepResult.step (mkS 0 5 locals2 cm mem2)) = _
      rw [hBin]
      have hChkBool : (!checkValV2 (.bool bLt) .bool) = false := by
        cases bLt <;> rfl
      change (match (if (!checkValV2 (.bool bLt) .bool) = true then
            Except.error FaultKind.unsupported
          else
            Except.ok
              ([LocalSlot.immediate none, LocalSlot.immediate (some (Val.scalar sv)),
                LocalSlot.immediate (some Val.unit),
                LocalSlot.immediate (some (Val.bool bLt)),
                LocalSlot.immediate none, LocalSlot.dead], mem)) with
        | Except.error k => StepResult.fault k
        | Except.ok (locals2, mem2) =>
          StepResult.step (mkS 0 5 locals2 cm mem2)) = _
      rw [hChkBool]
      rfl
    cases hBLt : bLt with
    | false =>
      have hGe16 : 16 ≤ bits.toNat := by
        have hNotLtI : ¬ (Int.ofNat (truncateBits .i8 bits).toNat < Int.ofNat 16) :=
          of_decide_eq_false hBLt
        rw [hTr] at hNotLtI
        have hNotLt : ¬ (bits.toNat < 16) := fun h => hNotLtI (Int.ofNat_lt.mpr h)
        exact Nat.le_of_not_lt hNotLt
      refine ⟨10, ?_⟩
      unfold execProgV2
      rw [hInit]
      refine execOutcomeStateV2_step (s' := mkS 0 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .dead, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 3
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step hCopy4 ?_
      have hLtStepF := hLtStep
      rw [hBLt] at hLtStepF
      refine execOutcomeStateV2_step hLtStepF ?_
      refine execOutcomeStateV2_step (s' := mkS 2 0
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 2 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 2 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .immediate none] cm mem) rfl ?_
      let roRawBytes : List RodataByte :=
        List.append
          [RodataByte.init 97, RodataByte.init 115, RodataByte.init 115,
           RodataByte.init 101, RodataByte.init 114, RodataByte.init 116,
           RodataByte.init 105, RodataByte.init 111, RodataByte.init 110,
           RodataByte.init 32, RodataByte.init 102, RodataByte.init 97,
           RodataByte.init 105, RodataByte.init 108, RodataByte.init 101,
           RodataByte.init 100]
          [RodataByte.init 58, RodataByte.init 32, RodataByte.init 100,
           RodataByte.init 115, RodataByte.init 116, RodataByte.init 32,
           RodataByte.init 60, RodataByte.init 32, RodataByte.init 49,
           RodataByte.init 54]
      let roAid : AllocId := mem.nextAllocId
      let roAlloc : Allocation := {
        allocId := roAid
        bytes := roRawBytes.map rodataByteToAllocByte
        alignLog2 := 0
        mutability := .shared
        live := true
      }
      let mem1 : MemoryState := {
        nextAllocId := roAid + 1
        allocations := roAlloc :: mem.allocations
      }
      have hFindRo : findAllocation roAid mem1.allocations = some roAlloc := by
        change (if Nat.beq roAid roAid then some roAlloc else _) = some roAlloc
        rw [Nat.beq_refl]; rfl
      have hRefRo :
          refValidInMem mem1 .shared .str
            (.slicePtr ⟨some roAid, UInt64.ofNat 0, .isize⟩ (UInt64.ofNat 26)) =
          .ok () := by
        dsimp only [refValidInMem, sliceFromRawPartsCheck, sliceRefRawCheck]
        rw [hFindRo]
        rfl
      have hUtf8Ro :
          (!strSliceUtf8InMem mem1 ⟨some roAid, UInt64.ofNat 0, .isize⟩
            (UInt64.ofNat 26)) = false := by
        dsimp only [strSliceUtf8InMem]
        rw [hFindRo]
        rfl
      let roConst : ConstOperand :=
        ⟨.ref .shared .str, .rodataRef roRawBytes 0 0 (some 26)⟩
      let abortLocals : List LocalSlot :=
        [.immediate none, .immediate (some (.scalar sv)),
         .immediate (some .unit), .immediate none, .dead, .immediate none]
      have hRodata :
          evalOperandToSlotV2 Captured.body_0.locals abortLocals mem
            (.constant roConst) =
          .ok (.ref .shared .str,
            some (.slicePtr ⟨some roAid, UInt64.ofNat 0, .isize⟩
              (UInt64.ofNat 26)),
            abortLocals, mem1) := by
        dsimp only [evalOperandToSlotV2, evalRodataRefConstV2, roConst,
          allocRodataMemory, MemoryState.reserveAllocId]
        have hG1 :
            (!Nat.blt roRawBytes.length isizeMaxBytes ||
              !Nat.ble 0 29 || !Nat.blt 0 (Nat.pow 2 64)) = false := by
          decide
        have hG2 : (!Nat.blt 26 (Nat.pow 2 64)) = false := by decide
        have hG3 : Mutability.beq .shared .mut = false := rfl
        rw [ite_bool_false hG1, ite_bool_false hG2, ite_bool_false hG3, hRefRo]
        dsimp only
        rw [ite_bool_false hUtf8Ro]
      have hAbortStep :
          evalStepV2 (entryProgForBody Captured.program 0)
            (mkS 2 2 abortLocals cm mem) =
          .done (.aborted (extractCallerMemory cm mem1)) := by
        change (match (match evalOperandToSlotV2 Captured.body_0.locals
              abortLocals mem (.constant roConst) with
            | Except.error k => Except.error k
            | Except.ok (_, none, _, _) => Except.error FaultKind.undefined
            | Except.ok (ty, some v, locals1, mem1') =>
              Except.ok ([(ty, v)], locals1, mem1')) with
          | Except.error k => StepResult.fault k
          | Except.ok (typedArgs, _, mem1') =>
            match validatePanicAbortArgs mem1' typedArgs with
            | Except.error k => StepResult.fault k
            | Except.ok () =>
              evalCorePanicAbort .abort .unreachable
                (extractCallerMemory cm mem1') false) = _
        rw [hRodata]
        dsimp only [validatePanicAbortArgs, IntWidth.beq]
        rw [hRefRo]
        dsimp only
        rw [ite_bool_false hUtf8Ro]
        rfl
      have hRoGt : maxAllocId cm.allocations < roAid := by
        change maxAllocId cm.allocations <
          Nat.max entryMemory.nextAllocId (maxAllocAndProvId cm.allocations + 1)
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_left _ _))
          (Nat.le_max_right _ _)
      have hCmEq : extractCallerMemory cm mem1 = cm :=
        (extractCallerMemory_cons_fresh hRoGt).trans
          (extractCallerMemory_entry cm hMem)
      exact execOutcomeStateV2_done hAbortStep ⟨rfl, hGe16, hCmEq⟩
    | true =>
      have hLt16 : bits.toNat < 16 := by
        have hLtI : Int.ofNat (truncateBits .i8 bits).toNat < Int.ofNat 16 :=
          of_decide_eq_true hBLt
        rw [hTr] at hLtI
        exact Int.ofNat_lt.mp hLtI
      refine ⟨15, ?_⟩
      unfold execProgV2
      rw [hInit]
      refine execOutcomeStateV2_step (s' := mkS 0 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .dead, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 0 3
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step hCopy4 ?_
      have hLtStepT := hLtStep
      rw [hBLt] at hLtStepT
      refine execOutcomeStateV2_step hLtStepT ?_
      refine execOutcomeStateV2_step (s' := mkS 1 0
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .immediate none, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 1
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 2
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .immediate none, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 3
        [.immediate none, .immediate (some (.scalar sv)), .immediate (some .unit),
         .dead, .dead, .dead] cm mem) rfl ?_
      refine execOutcomeStateV2_step (s' := mkS 1 4
        [.immediate none, .immediate (some (.scalar sv)),
         .dead, .dead, .dead, .dead] cm mem) rfl ?_
      have hWrite0 :
          evalStepV2 (entryProgForBody Captured.program 0)
            (mkS 1 4 [.immediate none, .immediate (some (.scalar sv)),
              .dead, .dead, .dead, .dead] cm mem) =
          .step (mkS 1 5 [.immediate (some (.scalar sv)),
              .immediate (some (.scalar sv)),
              .dead, .dead, .dead, .dead] cm mem) := by
        change (match (if (!checkValV2 (Val.scalar sv) (MirTy.int IntWidth.i8 false)) = true then
            Except.error FaultKind.unsupported
          else
            Except.ok
              ([LocalSlot.immediate (some (Val.scalar sv)),
                LocalSlot.immediate (some (Val.scalar sv)),
                LocalSlot.dead, LocalSlot.dead, LocalSlot.dead, LocalSlot.dead], mem)) with
          | Except.error k => StepResult.fault k
          | Except.ok (locals', mem') => StepResult.step (mkS 1 5 locals' cm mem')) = _
        rw [hSv]
        rfl
      refine execOutcomeStateV2_step hWrite0 ?_
      exact execOutcomeStateV2_done rfl ⟨hLt16, rfl,
        (rm2_extractReturnMemoryV2_entry cm _).trans
          (extractCallerMemory_entry cm hMem)⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      exact ⟨rfl, body0_static_admitted, fun q hValid _ =>
        (body0_safeContract.2.2 q hValid trivial).1⟩
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · exact body0_safeContract

end Proof
