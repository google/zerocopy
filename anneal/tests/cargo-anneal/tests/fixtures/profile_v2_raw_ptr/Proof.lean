-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.List.Lemmas
import Spec
import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp


/-! ## Step & Arithmetic Helpers -/

theorem lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem blt_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

theorem uint64_ofNat_toNat (x : UInt64) : UInt64.ofNat x.toNat = x := by
  cases x with
  | ofBitVec bv =>
    have hNat : (BitVec.ofNat 64 bv.toNat).toNat = bv.toNat :=
      Nat.mod_eq_of_lt bv.isLt
    exact congrArg UInt64.ofBitVec (bitVec_eq_of_toNat_eq hNat)

theorem toNat_uint64_ofNat_lt {n : Nat} (h : n < Nat.pow 2 64) :
    (UInt64.ofNat n).toNat = n :=
  Nat.mod_eq_of_lt h

theorem scalarVal_wf_isize {sv : ScalarVal} (hWf : ScalarVal.wf sv = true)
    (hW : sv.width = .isize) :
    truncateBits .isize sv.bits = sv.bits := by
  unfold ScalarVal.wf at hWf
  rw [hW] at hWf
  exact eq_of_beq hWf

theorem truncateBits_isize_toNat_lt {sv : ScalarVal} (hW : sv.width = .isize)
    (hWf : ScalarVal.wf sv = true) :
    sv.bits.toNat < Nat.pow 2 64 := by
  have hEq := scalarVal_wf_isize hWf hW
  rw [← hEq, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

theorem toNat_truncateBits_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    (truncateBits .isize (BitVec.ofNat 128 n)).toNat = n := by
  rw [toNat_truncateBits]
  have h128 : n < Nat.pow 2 128 := Nat.lt_trans h (by decide)
  change Nat.mod (Nat.mod n (Nat.pow 2 128)) (intWidthModulus .isize) = n
  have hMod : Nat.mod n (Nat.pow 2 128) = n := Nat.mod_eq_of_lt h128
  rw [hMod]
  exact Nat.mod_eq_of_lt h

theorem scalarWf_isize_truncateBits (n : Nat) :
    ScalarVal.wf ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 n)⟩ = true :=
  scalarWf_truncateBits .isize false (BitVec.ofNat 128 n)

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

/-! ## CallerMemory Preservation & Subslice Lemmas -/

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
    change (if Nat.beq a.allocId a.allocId then some a else findAllocation a.allocId suff) = some a
    rw [Nat.beq_refl]
    rfl
  | cons x xs ih =>
    have hCons : natNotElem a.allocId (x.allocId :: xs.map Allocation.allocId) = true := hDisj
    let ⟨hNe, hRest⟩ := natNotElem_cons_ne hCons
    change (if Nat.beq x.allocId a.allocId then some x else findAllocation a.allocId (xs ++ a :: suff)) = some a
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
    have hFoundA : findAllocation a.allocId m.allocations = some a := hFind a (.head _)
    have hTail : extractCallerAllocations m rest = rest :=
      extractCallerAllocations_suffix m (pref ++ [a]) rest
        (by rw [hEq, List.append_assoc]; rfl)
        (fun b hb => hFind b (.tail _ hb))
    change (findAllocation a.allocId m.allocations).getD a :: extractCallerAllocations m rest = a :: rest
    rw [hFoundA, hTail]
    rfl

theorem natNotElem_of_forall_ne {x : Nat} :
    ∀ {xs : List Nat}, (∀ y, y ∈ xs → x ≠ y) → natNotElem x xs = true :=
  fun h => (natNotElem_iff_not_mem x _).mpr h

theorem mem_map_reverse_append {x : Allocation} {pref : List Allocation} {y : AllocId}
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

theorem mem_map_append_left {pref : List Allocation} {x : Allocation} {w : AllocId}
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
      (∀ z, z ∈ seen → natNotElem z (pref.map Allocation.allocId) = true → False) →
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
              have hNotPref : natNotElem x.allocId (pref.map Allocation.allocId) = true :=
                natNotElem_of_forall_ne (fun y hy => hForall y (hPrefSub y hy))
              exact findAllocation_append_of_not_in_prefix pref x xs hNotPref
            | tail _ hIn =>
              have hEq : pref ++ x :: xs = (pref ++ [x]) ++ xs := by
                rw [List.append_assoc]; rfl
              rw [hEq]
              exact findAllocation_in_allocIdsValid (pref ++ [x]) xs (x.allocId :: seen)
                (fun z hz hNot => by
                  cases hz with
                  | head _ =>
                    exact (natNotElem_iff_not_mem x.allocId _).mp hNot x.allocId
                      (mem_map_self_append pref x) rfl
                  | tail _ hZ =>
                    exact hSeenSub z hZ (natNotElem_of_forall_ne (fun w hw =>
                      (natNotElem_iff_not_mem z _).mp hNot w (mem_map_append_left hw))))
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
    have hEq := extractCallerAllocations_suffix (entryMemoryWithCaller ⟨allocs⟩) [] allocs rfl
      (findAllocation_in_allocIdsValid [] allocs []
        (fun _ hz => by cases hz) (fun _ hz => by cases hz) hValid)
    rw [hEq]


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
    (hArgs : checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0, initLocalsLoop body q.args 0 body.locals⟩],
      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  unfold initStateV2
  rw [hPW, hPV, hCM, hEntry]
  dsimp only
  rw [hNonEmpty, hArgLt, hSto, hDiscr, hCast, hLocs]
  rw [hArgs, hRefs, hDisj]
  rfl

theorem writePlaceV2_immediate_ok {bodyLocals : List MirTy} {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) = some locals') :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val = .ok (locals', mem) := by
  unfold writePlaceV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]


private theorem list_drop_take_four_len (off : Nat) (bs : List AllocByte)
    (hLe : off + 4 ≤ bs.length) :
    ((bs.drop off).take 4).length = 4 := by
  induction off generalizing bs with
  | zero =>
    cases bs with
    | nil => cases hLe
    | cons _ r0 =>
      cases r0 with
      | nil => dsimp only [List.length] at hLe; exact absurd hLe (by decide)
      | cons _ r1 =>
        cases r1 with
        | nil => dsimp only [List.length] at hLe; exact absurd hLe (by decide)
        | cons _ r2 =>
          cases r2 with
          | nil => dsimp only [List.length] at hLe; exact absurd hLe (by decide)
          | cons _ _ => rfl
  | succ k ih =>
    cases bs with
    | nil => cases hLe
    | cons _ rest =>
      dsimp only [List.drop]
      apply ih
      exact Nat.le_of_succ_le_succ (by
        rw [Nat.succ_add] at hLe
        exact hLe)

private theorem isSliceAllInit_take_four (bs : List AllocByte)
    (hLen : bs.length = 4) (hInit : isSliceAllInit bs = true) :
    ∃ b0 b1 b2 b3 p0 p1 p2 p3,
      bs = [.init b0 p0, .init b1 p1, .init b2 p2, .init b3 p3] := by
  cases bs with
  | nil => cases hLen
  | cons x0 r0 =>
    cases x0 with
    | uninit => exact Bool.noConfusion hInit
    | init b0 p0 =>
      cases r0 with
      | nil => cases hLen
      | cons x1 r1 =>
        cases x1 with
        | uninit => exact Bool.noConfusion hInit
        | init b1 p1 =>
          cases r1 with
          | nil => cases hLen
          | cons x2 r2 =>
            cases x2 with
            | uninit => exact Bool.noConfusion hInit
            | init b2 p2 =>
              cases r2 with
              | nil => cases hLen
              | cons x3 r3 =>
                cases x3 with
                | uninit => exact Bool.noConfusion hInit
                | init b3 p3 =>
                  cases r3 with
                  | nil => exact ⟨b0, b1, b2, b3, p0, p1, p2, p3, rfl⟩
                  | cons _ _ => cases hLen

private theorem truncateBits_i32_of_lt (n : Nat) (hLt : n < 2 ^ 32) :
    truncateBits .i32 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
  unfold truncateBits
  dsimp only [IntWidth.bitWidth]
  apply BitVec.eq_of_toNat_eq
  have h128 : n < 2 ^ 128 := Nat.lt_trans hLt (by decide)
  change (n % 2 ^ 128) % 2 ^ 32 % 2 ^ 128 = n % 2 ^ 128
  rw [Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt hLt, Nat.mod_eq_of_lt h128]

private theorem natOfLeBytes_lt : ∀ (bs : List UInt8),
    natOfLeBytes bs < 256 ^ bs.length
  | [] => by unfold natOfLeBytes; decide
  | b :: rest => by
    unfold natOfLeBytes
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hr := natOfLeBytes_lt rest
    have hStep : b.toNat + 256 * natOfLeBytes rest < 256 + 256 * (256 ^ rest.length - 1) := by
      have hMul : 256 * natOfLeBytes rest ≤ 256 * (256 ^ rest.length - 1) :=
        Nat.mul_le_mul_left 256 (Nat.le_pred_of_lt hr)
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hb _) (Nat.add_le_add_left hMul 256)
    have hPowPos : 1 ≤ 256 ^ rest.length := Nat.pow_pos (by decide)
    have hEq : 256 + 256 * (256 ^ rest.length - 1) = 256 ^ (rest.length + 1) := by
      have h1 : 256 * (1 + (256 ^ rest.length - 1)) = 256 + 256 * (256 ^ rest.length - 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [← h1, Nat.add_sub_cancel' hPowPos, Nat.pow_succ, Nat.mul_comm]
    dsimp only [List.length]
    rw [← hEq]
    exact hStep

private theorem decodeUInt_little_four_lt (b0 b1 b2 b3 : UInt8) :
    decodeUInt TargetEndian.little [b0, b1, b2, b3] < 2 ^ 32 := by
  unfold decodeUInt
  have hLt := natOfLeBytes_lt [b0, b1, b2, b3]
  have hEq : 256 ^ [b0, b1, b2, b3].length = 2 ^ 32 := by
    change 256 ^ 4 = 2 ^ 32
    decide
  rw [hEq] at hLt
  exact hLt

/-- Profile v2 decodes memory little-endian, matching the 64-bit
little-endian targets that capture admits. -/
theorem profileV2_little_endian_canary :
    decodeUInt profileV2TargetEndian [1, 0, 0, 0] = 1 := rfl

private theorem loadU32_ok (cm : CallerMemory) (pv : PtrVal) (aid : AllocId)
    (a : Allocation)
    (hFind : findAllocation aid cm.allocations = some a)
    (hLive : a.live = true)
    (hBounds : isInBounds a pv.offsetBytes.toNat 4 = true)
    (hAlign : isAligned a pv.offsetBytes.toNat 2 = true)
    (hInit : isSliceAllInit ((a.bytes.drop pv.offsetBytes.toNat).take 4) = true) :
    ∃ sv : ScalarVal,
      loadIndirectV2 (entryMemoryWithCaller cm) (.int .i32 false)
        ⟨aid, pv.offsetBytes.toNat⟩ = .ok (some (.scalar sv)) ∧
      checkValV2 (.scalar sv) (.int .i32 false) = true := by
  unfold loadIndirectV2
  dsimp only [layoutOfTyV2, layoutOfTy, intLayout]
  have hRead : readBytes (entryMemoryWithCaller cm) ⟨aid, pv.offsetBytes.toNat⟩ 4 2 =
      .ok ((a.bytes.drop pv.offsetBytes.toNat).take 4) := by
    unfold readBytes entryMemoryWithCaller
    rw [ite_bool_false (b := Nat.beq 4 0) rfl]
    dsimp only
    rw [hFind]
    dsimp only
    rw [ite_bool_false (by rw [hLive, hBounds, hAlign]; rfl)]
  rw [hRead]
  have hLe : pv.offsetBytes.toNat + 4 ≤ a.bytes.length := by
    unfold isInBounds at hBounds
    exact Nat.le_of_ble_eq_true hBounds
  have hTakeLen := list_drop_take_four_len pv.offsetBytes.toNat a.bytes hLe
  match isSliceAllInit_take_four _ hTakeLen hInit with
  | ⟨b0, b1, b2, b3, p0, p1, p2, p3, hEq⟩ =>
    rw [hEq]
    have hTrunc := truncateBits_i32_of_lt _ (decodeUInt_little_four_lt b0 b1 b2 b3)
    have hBne : (truncateBits IntWidth.i32 (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) !=
        BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) = false := by
      rw [hTrunc]
      exact bne_self_eq_false _
    have hDec : decodeValV2 profileV2TargetEndian (.int .i32 false)
        [.init b0 p0, .init b1 p1, .init b2 p2, .init b3 p3] =
        .ok (some (.scalar ⟨.i32, false,
          truncateBits .i32 (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3]))⟩)) := by
      change (match (if (truncateBits .i32 (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) !=
            BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) then
            Except.error FaultKind.unsupported
          else
            Except.ok (Val.scalar ⟨.i32, false,
              truncateBits .i32 (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3]))⟩)) with
        | Except.ok v => Except.ok (some v)
        | Except.error k => Except.error k) = _
      rw [ite_bool_false hBne]
    refine ⟨_, hDec, ?_⟩
    unfold checkValV2 checkVal Val.ty?
    dsimp only
    rw [hTrunc]
    have hEq : (truncateBits .i32 (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) ==
        BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) = true := by
      rw [hTrunc]; exact beq_self_eq_true _
    change (match (if (truncateBits .i32 (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) ==
        BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) then some (MirTy.int .i32 false) else none) with
      | some vTy => MirTy.beq vTy (.int .i32 false)
      | none => false) = true
    rw [hEq]; rfl

private theorem storeU8_ok (cm : CallerMemory) (pv : PtrVal) (aid : AllocId)
    (a : Allocation) (sv : ScalarVal)
    (hSvWf : checkValV2 (.scalar sv) (.int .i8 false) = true)
    (hFind : findAllocation aid cm.allocations = some a)
    (hLive : a.live = true)
    (hMut : a.mutability = .mut)
    (hBounds : isInBounds a pv.offsetBytes.toNat 1 = true) :
    ∃ mem' : MemoryState,
      storeIndirectV2 (entryMemoryWithCaller cm) (.int .i8 false)
        ⟨aid, pv.offsetBytes.toNat⟩ (.scalar sv) = .ok mem' := by
  unfold storeIndirectV2
  dsimp only [layoutOfTyV2, layoutOfTy, intLayout]
  have hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) (.scalar sv) =
      .ok ((encodeUInt profileV2TargetEndian 1 sv.bits.toNat).map (fun b => AllocByte.init b none)) := by
    unfold encodeValV2
    rw [ite_bool_false (by rw [hSvWf]; rfl)]
    unfold encodeVal
    rw [ite_bool_false (by
      have hV1 : checkVal (.scalar sv) (.int .i8 false) = true := hSvWf
      rw [hV1]; rfl)]
    rfl
  rw [hEnc]
  dsimp only
  have hLen1 : ((encodeUInt profileV2TargetEndian 1 sv.bits.toNat).map (fun b => AllocByte.init b none)).length = 1 := rfl
  unfold writeBytes entryMemoryWithCaller
  rw [hLen1]
  rw [ite_bool_false (b := Nat.beq 1 0) rfl]
  dsimp only
  rw [hFind]
  dsimp only
  have hAlign0 : isAligned a pv.offsetBytes.toNat 0 = true := by
    unfold isAligned
    have h0 : Nat.ble 0 a.alignLog2 = true := Nat.ble_eq_true_of_le (Nat.zero_le _)
    have hMod : Nat.mod pv.offsetBytes.toNat 1 = 0 := Nat.mod_one _
    have hPow : Nat.pow 2 0 = 1 := rfl
    rw [h0, hPow, hMod]; rfl
  rw [ite_bool_false (by rw [hLive, hBounds, hAlign0]; rfl)]
  rw [hMut]
  exact ⟨_, rfl⟩


private theorem execStateV2_step {p : Program} {n : Nat} {s s' : State} {post : TerminalOut → Prop}
    (hStep : evalStepV2 p s = .step s') (hRest : execStateV2 p n s' post) :
    execStateV2 p (n + 1) s post := by
  unfold execStateV2 execOutcomeStateV2
  change match evalStepV2 p s with
    | .step st' => execStateV2 p n st' post
    | .done out => post out
    | .fault _ => False
  rw [hStep]
  exact hRest

private theorem execStateV2_done {p : Program} {n : Nat} {s : State} {out : TerminalOut}
    {post : TerminalOut → Prop}
    (hDone : evalStepV2 p s = .done out) (hPost : post out) :
    execStateV2 p (n + 1) s post := by
  unfold execStateV2 execOutcomeStateV2
  change match evalStepV2 p s with
    | .step st' => execStateV2 p n st' post
    | .done o => post o
    | .fault _ => False
  rw [hDone]
  exact hPost

private theorem loadU32_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hSafe : Spec.loadU32Safety q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q ∧
    match q.args with
    | [.ptr pv] =>
      match pv.allocId with
      | none => False
      | some aid =>
        ∃ v : Val,
          loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i32 false)
            ⟨aid, pv.offsetBytes.toNat⟩ = .ok (some v) ∧
          BehaviorV2 (entryProgForBody Captured.program 0) q
            (TerminalOut.returned ⟨v, q.callerMem⟩)
    | _ => False := by
  have hCallerValid := hValid.1
  have hArgsMatch := hValid.2.1
  have hRefs := hValid.2.2.1
  have hDisj := hValid.2.2.2
  cases q with
  | mk args cm =>
    dsimp only at hCallerValid hArgsMatch hRefs hDisj
    unfold Spec.loadU32Safety at hSafe
    dsimp only at hSafe
    cases args with
    | nil => exact False.elim hSafe
    | cons a0 rest =>
      cases rest with
      | cons _ _ => cases a0 <;> (change False at hSafe; exact False.elim hSafe)
      | nil =>
        cases a0 with
        | scalar _ | nonZero _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _
        | char _ | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ =>
          exact False.elim hSafe
        | ptr pv =>
          dsimp only at hSafe
          cases hAid : pv.allocId with
          | none => rw [hAid] at hSafe; exact False.elim hSafe
          | some aid =>
            rw [hAid] at hSafe
            dsimp only at hSafe
            match hSafe with
            | ⟨a, hFind, hLive, hBounds, hAlign, hInit⟩ =>
              match loadU32_ok cm pv aid a hFind hLive hBounds hAlign hInit with
              | ⟨sv, hLoad, hVWf⟩ =>
                have hStep0 : initStateV2 (entryProgForBody Captured.program 0) ⟨[.ptr pv], cm⟩ =
                    .ok ⟨[⟨0, 0, 0, [.immediate none, .immediate (some (.ptr pv))]⟩],
                      cm, entryMemoryWithCaller cm⟩ :=
                  initStateV2_ok_of (p := entryProgForBody Captured.program 0) (q := ⟨[.ptr pv], cm⟩) (body := Captured.body_0)
                    rfl rfl hCallerValid rfl rfl rfl rfl rfl rfl rfl
                    hArgsMatch hRefs hDisj
                have hReadP : readPlaceV2 Captured.body_0.locals
                    [.immediate none, .immediate (some (.ptr pv))]
                    (entryMemoryWithCaller cm) false ⟨1, [.deref]⟩ =
                    .ok (.int .i32 false, some (.scalar sv),
                      [.immediate none, .immediate (some (.ptr pv))],
                      entryMemoryWithCaller cm) := by
                  unfold readPlaceV2
                  change (match pv.allocId with
                    | none => _
                    | some aid =>
                      match loadIndirectV2 (entryMemoryWithCaller cm) (MirTy.int IntWidth.i32 false)
                          ⟨aid, pv.offsetBytes.toNat⟩ with
                      | Except.error k => Except.error k
                      | Except.ok optVal => Except.ok (MirTy.int IntWidth.i32 false, optVal,
                          [LocalSlot.immediate none, LocalSlot.immediate (some (Val.ptr pv))],
                          entryMemoryWithCaller cm)) = _
                  rw [hAid]
                  dsimp only
                  rw [hLoad]
                have hStep1 : evalStepV2 (entryProgForBody Captured.program 0)
                    ⟨[⟨0, 0, 0, [.immediate none, .immediate (some (.ptr pv))]⟩],
                      cm, entryMemoryWithCaller cm⟩ =
                    .step ⟨[⟨0, 0, 1, [.immediate (some (Val.scalar sv)), .immediate (some (.ptr pv))]⟩],
                      cm, entryMemoryWithCaller cm⟩ := by
                  unfold evalStepV2
                  change (match evalRvalueV2 Captured.body_0.locals
                      [.immediate none, .immediate (some (.ptr pv))]
                      (entryMemoryWithCaller cm) (.int .i32 false)
                      (.use (.copy ⟨1, [.deref]⟩)) with
                    | Except.error k => StepResult.fault k
                    | Except.ok (val, l1, m1) =>
                      match writePlaceV2 Captured.body_0.locals l1 m1 ⟨0, []⟩ (.int .i32 false) val with
                      | Except.error k => StepResult.fault k
                      | Except.ok (l2, m2) => StepResult.step (State.mk [FrameState.mk 0 0 1 l2] cm m2)) = _
                  have hRv : evalRvalueV2 Captured.body_0.locals
                      [.immediate none, .immediate (some (.ptr pv))]
                      (entryMemoryWithCaller cm) (.int .i32 false)
                      (.use (.copy ⟨1, [.deref]⟩)) =
                      .ok (.scalar sv, [.immediate none, .immediate (some (.ptr pv))],
                        entryMemoryWithCaller cm) := by
                    unfold evalRvalueV2 evalOperandToSlotV2
                    dsimp only
                    rw [hReadP]; rfl
                  rw [hRv]
                  dsimp only
                  rw [writePlaceV2_immediate_ok hVWf rfl rfl]
                have hStep2 : evalStepV2 (entryProgForBody Captured.program 0)
                    ⟨[⟨0, 0, 1, [.immediate (some (Val.scalar sv)), .immediate (some (.ptr pv))]⟩],
                      cm, entryMemoryWithCaller cm⟩ =
                    .done (.returned ⟨.scalar sv, cm⟩) := by
                  change StepResult.done (TerminalOut.returned ⟨.scalar sv, extractCallerMemory cm (entryMemoryWithCaller cm)⟩) = _
                  rw [extractCallerMemory_entry cm hCallerValid]
                have hExec : execProgV2 (entryProgForBody Captured.program 0) 4 ⟨[.ptr pv], cm⟩
                    (fun out => out = TerminalOut.returned ⟨.scalar sv, cm⟩) := by
                  unfold execProgV2
                  rw [hStep0]
                  exact execStateV2_step hStep1 (execStateV2_done hStep2 rfl)
                have hRes := spec_and_behaviorV2_of_exec_eq hExec
                refine ⟨hRes.1, ?_⟩
                dsimp only
                rw [hAid]
                exact ⟨.scalar sv, hLoad, hRes.2.1⟩

private theorem storeU8_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q)
    (hSafe : Spec.storeU8Safety q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q ∧
    match q.args with
    | [.ptr pv, .scalar sv] =>
      match pv.allocId with
      | none => False
      | some aid =>
        ∃ mem' : MemoryState,
          storeIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
            ⟨aid, pv.offsetBytes.toNat⟩ (.scalar sv) = .ok mem' ∧
          BehaviorV2 (entryProgForBody Captured.program 1) q
            (TerminalOut.returned ⟨.unit, extractCallerMemory q.callerMem mem'⟩)
    | _ => False := by
  have hCallerValid := hValid.1
  have hArgsMatch := hValid.2.1
  have hRefs := hValid.2.2.1
  have hDisj := hValid.2.2.2
  cases q with
  | mk args cm =>
    dsimp only at hCallerValid hArgsMatch hRefs hDisj
    unfold Spec.storeU8Safety at hSafe
    dsimp only at hSafe
    cases args with
    | nil => exact False.elim hSafe
    | cons a0 r0 =>
      cases r0 with
      | nil => cases a0 <;> exact False.elim hSafe
      | cons a1 r1 =>
        cases r1 with
        | cons _ _ => cases a0 <;> (try exact False.elim hSafe); cases a1 <;> exact False.elim hSafe
        | nil =>
          cases a0 with
          | scalar _ | nonZero _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _
          | char _ | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ =>
            exact False.elim hSafe
          | ptr pv =>
            cases a1 with
            | ptr _ | nonZero _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _
            | char _ | ordering _ | unit | enumVal _ _ | tuple _ | bytes _ =>
              exact False.elim hSafe
            | scalar sv =>
              dsimp only at hSafe
              cases hAid : pv.allocId with
              | none => rw [hAid] at hSafe; exact False.elim hSafe
              | some aid =>
                rw [hAid] at hSafe
                dsimp only at hSafe
                match hSafe with
                | ⟨a, hFind, hLive, hMut, hBounds⟩ =>
                  have hArgsMatch' := hArgsMatch
                  dsimp only [checkArgsMatchV2, Captured.body_1, List.drop, List.take,
                    List.foldr, Bool.and_true] at hArgsMatch'
                  have hPvWf : checkValV2 (.ptr pv) (.rawPtr .mut (.int .i8 false)) = true := by
                    cases h1 : checkValV2 (.ptr pv) (.rawPtr .mut (.int .i8 false)) with
                    | true => rfl
                    | false => rw [h1] at hArgsMatch'; exact Bool.noConfusion hArgsMatch'
                  have hSvWf : checkValV2 (.scalar sv) (.int .i8 false) = true := by
                    rw [hPvWf] at hArgsMatch'
                    cases h2 : checkValV2 (.scalar sv) (.int .i8 false) with
                    | true => rfl
                    | false => rw [h2] at hArgsMatch'; exact Bool.noConfusion hArgsMatch'
                  match storeU8_ok cm pv aid a sv hSvWf hFind hLive hMut hBounds with
                  | ⟨mem', hStore⟩ =>
                    have hStep0 : initStateV2 (entryProgForBody Captured.program 1) ⟨[.ptr pv, .scalar sv], cm⟩ =
                        .ok ⟨[⟨1, 0, 0, [
                            .immediate (some .unit),
                            .immediate (some (.ptr pv)),
                            .immediate (some (.scalar sv)),
                            .dead
                          ]⟩], cm, entryMemoryWithCaller cm⟩ :=
                      initStateV2_ok_of (p := entryProgForBody Captured.program 1) (q := ⟨[.ptr pv, .scalar sv], cm⟩) (body := Captured.body_1)
                        rfl rfl hCallerValid rfl rfl rfl rfl rfl rfl rfl
                        hArgsMatch hRefs hDisj
                    have hStep1 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 0, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .dead]⟩],
                          cm, entryMemoryWithCaller cm⟩ =
                        .step ⟨[⟨1, 0, 1, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none]⟩],
                          cm, entryMemoryWithCaller cm⟩ := rfl
                    have hStep2 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 1, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none]⟩],
                          cm, entryMemoryWithCaller cm⟩ =
                        .step ⟨[⟨1, 0, 2, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate (some (.scalar sv))]⟩],
                          cm, entryMemoryWithCaller cm⟩ := by
                      unfold evalStepV2
                      change (match writePlaceV2 Captured.body_1.locals
                          [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none]
                          (entryMemoryWithCaller cm) ⟨3, []⟩ (.int .i8 false) (.scalar sv) with
                        | Except.error k => StepResult.fault k
                        | Except.ok (l2, m2) => StepResult.step (State.mk [FrameState.mk 1 0 2 l2] cm m2)) = _
                      rw [writePlaceV2_immediate_ok hSvWf rfl rfl]
                    have hWp3 : writePlaceV2 Captured.body_1.locals
                        [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none]
                        (entryMemoryWithCaller cm) ⟨1, [.deref]⟩ (.int .i8 false) (.scalar sv) =
                        .ok ([.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none], mem') := by
                      unfold writePlaceV2
                      rw [ite_bool_false (by rw [hSvWf]; rfl)]
                      change (match pv.allocId with
                        | none => _
                        | some aid =>
                          match findAllocation aid (entryMemoryWithCaller cm).allocations with
                          | none => Except.error FaultKind.undefined
                          | some a =>
                            if !a.live || !Mutability.beq a.mutability .mut then
                              Except.error FaultKind.undefined
                            else
                              match storeIndirectV2 (entryMemoryWithCaller cm) (.int .i8 false)
                                  ⟨aid, pv.offsetBytes.toNat⟩ (.scalar sv) with
                              | Except.ok mem1 => Except.ok ([LocalSlot.immediate (some Val.unit), LocalSlot.immediate (some (Val.ptr pv)), LocalSlot.immediate (some (Val.scalar sv)), LocalSlot.immediate none], mem1)
                              | Except.error k => Except.error k) = _
                      rw [hAid]
                      dsimp only [entryMemoryWithCaller]
                      rw [hFind]
                      dsimp only
                      rw [ite_bool_false (by rw [hLive, hMut]; rfl)]
                      change (match storeIndirectV2 (entryMemoryWithCaller cm) (.int .i8 false)
                          ⟨aid, pv.offsetBytes.toNat⟩ (.scalar sv) with
                        | Except.ok mem1 => Except.ok (_, mem1)
                        | Except.error k => Except.error k) = _
                      rw [hStore]
                    have hStep3 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 2, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate (some (.scalar sv))]⟩],
                          cm, entryMemoryWithCaller cm⟩ =
                        .step ⟨[⟨1, 0, 3, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none]⟩],
                          cm, mem'⟩ := by
                      unfold evalStepV2
                      change (match writePlaceV2 Captured.body_1.locals
                          [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none]
                          (entryMemoryWithCaller cm) ⟨1, [.deref]⟩ (.int .i8 false) (.scalar sv) with
                        | Except.error k => StepResult.fault k
                        | Except.ok (l2, m2) => StepResult.step (State.mk [FrameState.mk 1 0 3 l2] cm m2)) = _
                      rw [hWp3]
                    have hStep4 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 3, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .immediate none]⟩],
                          cm, mem'⟩ =
                        .step ⟨[⟨1, 0, 4, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .dead]⟩],
                          cm, mem'⟩ := rfl
                    have hStep5 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 4, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .dead]⟩],
                          cm, mem'⟩ =
                        .step ⟨[⟨1, 0, 5, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .dead]⟩],
                          cm, mem'⟩ := rfl
                    have hStep6 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 5, [.immediate (some .unit), .immediate (some (.ptr pv)), .immediate (some (.scalar sv)), .dead]⟩],
                          cm, mem'⟩ =
                        .done (.returned ⟨.unit, extractCallerMemory cm mem'⟩) := rfl
                    have hExec : execProgV2 (entryProgForBody Captured.program 1) 8 ⟨[.ptr pv, .scalar sv], cm⟩
                        (fun out => out = TerminalOut.returned ⟨.unit, extractCallerMemory cm mem'⟩) := by
                      unfold execProgV2
                      rw [hStep0]
                      exact execStateV2_step hStep1
                        (execStateV2_step hStep2
                          (execStateV2_step hStep3
                            (execStateV2_step hStep4
                              (execStateV2_step hStep5
                                (execStateV2_done hStep6 rfl)))))
                    have hRes := spec_and_behaviorV2_of_exec_eq hExec
                    refine ⟨hRes.1, ?_⟩
                    dsimp only
                    rw [hAid]
                    exact ⟨mem', hStore, hRes.2.1⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hFound
    cases defId with
    | zero =>
      have hEq : Captured.body_0 = body := Option.some.inj hFound
      subst hEq
      refine ⟨hFound, rfl, fun q hValid hSafe => ?_⟩
      exact (loadU32_correct q hValid (hSafe rfl)).1
    | succ n =>
      cases n with
      | zero =>
        have hEq : Captured.body_1 = body := Option.some.inj hFound
        subst hEq
        refine ⟨hFound, rfl, fun q hValid hSafe => ?_⟩
        exact (storeU8_correct q hValid (hSafe rfl)).1
      | succ _ => cases hFound
  · refine ⟨?_, ?_⟩
    · intro q hValid hSafe
      exact (loadU32_correct q hValid hSafe).2
    · intro q hValid hSafe
      exact (storeU8_correct q hValid hSafe).2

end Proof
