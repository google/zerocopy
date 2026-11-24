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

theorem findAllocation_mem {aid : AllocId} :
    ∀ {allocs : List Allocation} {a : Allocation},
      findAllocation aid allocs = some a → a ∈ allocs
  | [], _, h => by cases h
  | x :: xs, a, h => by
    change (if Nat.beq x.allocId aid then some x else findAllocation aid xs) = some a at h
    cases hEq : Nat.beq x.allocId aid with
    | true =>
      rw [hEq] at h
      cases h
      exact .head _
    | false =>
      rw [hEq] at h
      exact .tail _ (findAllocation_mem h)

theorem allocIdsValid_bytes_lt :
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
            | tail _ hIn => exact allocIdsValid_bytes_lt (x.allocId :: seen) xs hValid a hIn

theorem entryMemoryWithCaller_bytes_lt (cm : CallerMemory)
    (hValid : validCallerMemory cm = true) :
    ∀ aid a, findAllocation aid (entryMemoryWithCaller cm).allocations = some a →
      a.bytes.length < isizeMaxBytes := by
  intro aid a hFind
  exact allocIdsValid_bytes_lt [] cm.allocations hValid a (findAllocation_mem hFind)

theorem isSliceAllInit_take_le :
    ∀ (xs : List AllocByte) (n m : Nat),
      m ≤ n → isSliceAllInit (xs.take n) = true → isSliceAllInit (xs.take m) = true
  | _, _, 0, _, _ => rfl
  | [], _, m + 1, _, _ => by
    rw [List.take_nil]
    rfl
  | .uninit :: _, n + 1, m + 1, _, h => by
    cases h
  | .init _ _ :: xs, n + 1, m + 1, hLe, h => by
    exact isSliceAllInit_take_le xs n m (Nat.le_of_succ_le_succ hLe) h
  | _ :: _, 0, m + 1, hLe, _ => False.elim (Nat.not_succ_le_zero m hLe)

theorem isSliceAllInit_drop :
    ∀ (xs : List AllocByte) (k : Nat),
      isSliceAllInit xs = true → isSliceAllInit (xs.drop k) = true
  | xs, 0, h => h
  | [], _ + 1, _ => rfl
  | .uninit :: _, _ + 1, h => by cases h
  | .init _ _ :: xs, k + 1, h => isSliceAllInit_drop xs k h

theorem isSliceAllInit_drop_take :
    ∀ (bs : List AllocByte) (off len start subLen : Nat),
      start + subLen ≤ len →
      isSliceAllInit ((bs.drop off).take len) = true →
      isSliceAllInit ((bs.drop (off + start)).take subLen) = true
  | [], off, len, start, subLen, _, _ => by
    rw [List.drop_nil, List.take_nil]
    rfl
  | _ :: bs, o + 1, len, start, subLen, hSub, hInit => by
    have hAdd : o + 1 + start = (o + start) + 1 := Nat.succ_add o start
    rw [hAdd]
    exact isSliceAllInit_drop_take bs o len start subLen hSub hInit
  | b :: bs, 0, len, 0, subLen, hSub, hInit => by
    rw [Nat.zero_add]
    rw [Nat.zero_add] at hSub
    exact isSliceAllInit_take_le (b :: bs) len subLen hSub hInit
  | b :: bs, 0, 0, s + 1, subLen, hSub, _ => by
    have hFalse : s + 1 + subLen ≤ 0 := hSub
    exact False.elim (Nat.not_succ_le_zero (s + subLen) (by rw [Nat.succ_add] at hFalse; exact hFalse))
  | .uninit :: _, 0, l + 1, _, _, _, hInit => by
    cases hInit
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

theorem sliceFromRawPartsCheck_ok_val
    {m : MemoryState} {isMut : Bool} {es ea : Nat} {p : PtrVal} {len : UInt64} {v : Val}
    (h : sliceFromRawPartsCheck m isMut es ea p len = .ok v) :
    v = .slicePtr p len := by
  have h0 :
      (if !Nat.blt (len.toNat * es) isizeMaxBytes then
        Except.error FaultKind.undefined
      else
        match p.allocId with
        | none =>
          if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 (len.toNat * es) then
            Except.error FaultKind.undefined
          else if !Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 ea)) 0 then
            Except.error FaultKind.undefined
          else
            Except.ok (Val.slicePtr p len)
        | some aid =>
          match findAllocation aid m.allocations with
          | none => Except.error FaultKind.undefined
          | some a =>
            if !a.live || !isInBounds a p.offsetBytes.toNat (len.toNat * es) ||
                !isAligned a p.offsetBytes.toNat ea then
              Except.error FaultKind.undefined
            else if isMut && !Mutability.beq a.mutability .mut then
              Except.error FaultKind.undefined
            else if !isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * es)) then
              Except.error FaultKind.undefined
            else
              Except.ok (Val.slicePtr p len)) = Except.ok v := h
  cases hMax : Nat.blt (len.toNat * es) isizeMaxBytes with
  | false => rw [hMax] at h0; cases h0
  | true =>
    rw [hMax] at h0
    have h0' : (match p.allocId with
      | none =>
        if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 (len.toNat * es) then
          Except.error FaultKind.undefined
        else if !Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 ea)) 0 then
          Except.error FaultKind.undefined
        else
          Except.ok (Val.slicePtr p len)
      | some aid =>
        match findAllocation aid m.allocations with
        | none => Except.error FaultKind.undefined
        | some a =>
          if !a.live || !isInBounds a p.offsetBytes.toNat (len.toNat * es) ||
              !isAligned a p.offsetBytes.toNat ea then
            Except.error FaultKind.undefined
          else if isMut && !Mutability.beq a.mutability .mut then
            Except.error FaultKind.undefined
          else if !isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * es)) then
            Except.error FaultKind.undefined
          else
            Except.ok (Val.slicePtr p len)) = Except.ok v := h0
    cases hAid : p.allocId with
    | none =>
      rw [hAid] at h0'
      dsimp only at h0'
      cases hZ : (Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 (len.toNat * es)) with
      | true => rw [hZ] at h0'; cases h0'
      | false =>
        rw [hZ] at h0'
        cases hAl : (!Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 ea)) 0) with
        | true => rw [hAl] at h0'; cases h0'
        | false =>
          rw [hAl] at h0'
          injection h0' with hv
          exact hv.symm
    | some aid =>
      rw [hAid] at h0'
      dsimp only at h0'
      cases hFind : findAllocation aid m.allocations with
      | none => rw [hFind] at h0'; cases h0'
      | some a =>
        rw [hFind] at h0'
        dsimp only at h0'
        cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat (len.toNat * es) ||
            !isAligned a p.offsetBytes.toNat ea) with
        | true => rw [hBad] at h0'; cases h0'
        | false =>
          rw [hBad] at h0'
          cases hMut : (isMut && !Mutability.beq a.mutability .mut) with
          | true => rw [hMut] at h0'; cases h0'
          | false =>
            rw [hMut] at h0'
            cases hInit : (!isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * es))) with
            | true => rw [hInit] at h0'; cases h0'
            | false =>
              rw [hInit] at h0'
              injection h0' with hv
              exact hv.symm

theorem sliceFromRawPartsCheck_u8_to_subslice
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
          pSub = { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + start) } ∧
          ptr.offsetBytes.toNat + start < Nat.pow 2 64 ∧
          pSub.offsetBytes.toNat = ptr.offsetBytes.toNat + start) := by
  unfold sliceFromRawPartsCheck at hOrig
  dsimp only at hOrig
  rw [Nat.mul_one] at hOrig
  cases hMax : Nat.blt len.toNat isizeMaxBytes with
  | false => rw [hMax] at hOrig; cases hOrig
  | true =>
    rw [hMax] at hOrig
    have hLenLtMax : len.toNat < isizeMaxBytes := lt_of_blt_true hMax
    have hStartLtMax : start < isizeMaxBytes :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right start subLen) hSub) hLenLtMax
    have hSubLtMax : subLen < isizeMaxBytes :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left subLen start) hSub) hLenLtMax
    have hSubU64 : (UInt64.ofNat subLen).toNat = subLen :=
      toNat_uint64_ofNat_lt (Nat.lt_trans hSubLtMax (by decide))
    cases hAid : ptr.allocId with
    | none =>
      rw [hAid] at hOrig
      dsimp only at hOrig
      cases hZero : Nat.beq ptr.offsetBytes.toNat 0 with
      | true => rw [hZero] at hOrig; cases hOrig
      | false =>
        cases hLenPos : Nat.blt 0 len.toNat with
        | true => rw [hZero, hLenPos] at hOrig; cases hOrig
        | false =>
          have hLenZero : len.toNat = 0 := by
            cases hN : len.toNat with
            | zero => rfl
            | succ k =>
              have hPos : Nat.blt 0 (k + 1) = true := blt_true_of_lt (Nat.zero_lt_succ k)
              rw [hN] at hLenPos; cases hLenPos.symm.trans hPos
          have hSum0 : start + subLen = 0 := Nat.eq_zero_of_le_zero (hLenZero ▸ hSub)
          have hStart0 : start = 0 :=
            Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hSum0))
          have hSub0 : subLen = 0 :=
            Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hSum0))
          subst hStart0; subst hSub0
          refine ⟨ptr, ?_, ?_, ?_, ?_, ?_⟩
          · change (if !Nat.blt (0 * 1) isizeMaxBytes then Except.error FaultKind.undefined else
              match ptr.allocId with
              | none => if Nat.beq (0 * 1) 0 then Except.ok ptr else Except.error FaultKind.undefined
              | some aid =>
                match findAllocation aid m.allocations with
                | none => Except.error FaultKind.undefined
                | some a =>
                  if !a.live || !Nat.ble (ptr.offsetBytes.toNat + 0 * 1) a.bytes.length then
                    Except.error FaultKind.undefined
                  else
                    Except.ok { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + 0 * 1) }) =
                Except.ok ptr
            have hMul0 : 0 * 1 = 0 := rfl
            rw [hMul0]
            have hZeroLtMax : Nat.blt 0 isizeMaxBytes = true := by decide
            rw [hZeroLtMax]
            rw [hAid]
            rfl
          · unfold sliceFromRawPartsCheck
            dsimp only
            rw [Nat.mul_one, hSubU64]
            have hZeroLtMax : Nat.blt 0 isizeMaxBytes = true := by decide
            rw [hZeroLtMax]
            have hPow0 : Nat.pow 2 0 = 1 := rfl
            have hMod1 : Nat.mod ptr.offsetBytes.toNat 1 = 0 := Nat.mod_one _
            rw [hAid, hZero, hPow0, hMod1]
            rfl
          · exact hAid
          · rfl
          · rfl
    | some aid =>
      rw [hAid] at hOrig
      dsimp only at hOrig
      cases hFind : findAllocation aid m.allocations with
      | none => rw [hFind] at hOrig; cases hOrig
      | some a =>
        rw [hFind] at hOrig
        dsimp only at hOrig
        cases hLive : a.live with
        | false => rw [hLive] at hOrig; cases hOrig
        | true =>
          rw [hLive] at hOrig
          cases hBounds : isInBounds a ptr.offsetBytes.toNat len.toNat with
          | false => rw [hBounds] at hOrig; cases hOrig
          | true =>
            rw [hBounds] at hOrig
            cases hAlign : isAligned a ptr.offsetBytes.toNat 0 with
            | false => rw [hAlign] at hOrig; cases hOrig
            | true =>
              rw [hAlign] at hOrig
              cases hMutChk : (isMut && !Mutability.beq a.mutability .mut) with
              | true => rw [hMutChk] at hOrig; cases hOrig
              | false =>
                rw [hMutChk] at hOrig
                cases hInit : isSliceAllInit ((a.bytes.drop ptr.offsetBytes.toNat).take len.toNat) with
                | false => rw [hInit] at hOrig; cases hOrig
                | true =>
                  have hBoundsNat : ptr.offsetBytes.toNat + len.toNat ≤ a.bytes.length := by
                    unfold isInBounds at hBounds
                    exact Nat.le_of_ble_eq_true hBounds
                  have hStartIn : ptr.offsetBytes.toNat + start ≤ a.bytes.length :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _) hSub) _) hBoundsNat
                  have hEndIn : ptr.offsetBytes.toNat + start + subLen ≤ a.bytes.length :=
                    Nat.le_trans (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hSub _) hBoundsNat
                  have hAllocLt' : a.bytes.length < isizeMaxBytes := hAllocLt aid a hFind
                  have hStartLt64 : ptr.offsetBytes.toNat + start < Nat.pow 2 64 :=
                    Nat.lt_trans (Nat.lt_of_le_of_lt hStartIn hAllocLt') (by decide)
                  let pSub : PtrVal :=
                    { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + start) }
                  have hPSubOff : pSub.offsetBytes.toNat = ptr.offsetBytes.toNat + start :=
                    toNat_uint64_ofNat_lt hStartLt64
                  refine ⟨pSub, ?_, ?_, ?_, rfl, ?_⟩
                  · change (if !Nat.blt (start * 1) isizeMaxBytes then Except.error FaultKind.undefined else
                      match ptr.allocId with
                      | none => if Nat.beq (start * 1) 0 then Except.ok ptr else Except.error FaultKind.undefined
                      | some aid' =>
                        match findAllocation aid' m.allocations with
                        | none => Except.error FaultKind.undefined
                        | some a' =>
                          if !a'.live || !Nat.ble (ptr.offsetBytes.toNat + start * 1) a'.bytes.length then
                            Except.error FaultKind.undefined
                          else
                            Except.ok { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + start * 1) }) =
                        Except.ok pSub
                    rw [Nat.mul_one]
                    have hStartBlt : Nat.blt start isizeMaxBytes = true := blt_true_of_lt hStartLtMax
                    rw [hStartBlt]
                    rw [ite_bool_false (by decide : (!true) = false), hAid]
                    dsimp only
                    rw [hFind]
                    dsimp only
                    rw [hLive]
                    have hBleStart : Nat.ble (ptr.offsetBytes.toNat + start) a.bytes.length = true :=
                      Nat.ble_eq_true_of_le hStartIn
                    rw [hBleStart]
                    rw [ite_bool_false (by decide : (!true || !true) = false)]
                    dsimp only [pSub]
                    rw [hAid]
                  · unfold sliceFromRawPartsCheck
                    dsimp only
                    rw [Nat.mul_one, hSubU64]
                    have hSubBlt : Nat.blt subLen isizeMaxBytes = true := blt_true_of_lt hSubLtMax
                    rw [hSubBlt]
                    rw [ite_bool_false (by decide : (!true) = false)]
                    have hPSubAid : pSub.allocId = some aid := hAid
                    rw [hPSubAid]
                    dsimp only
                    rw [hFind]
                    dsimp only
                    rw [hLive, hPSubOff]
                    have hInB : isInBounds a (ptr.offsetBytes.toNat + start) subLen = true := by
                      unfold isInBounds
                      exact Nat.ble_eq_true_of_le hEndIn
                    have hAl0 : isAligned a (ptr.offsetBytes.toNat + start) 0 = true := by
                      unfold isAligned
                      have hPow0 : Nat.pow 2 0 = 1 := rfl
                      have hMod1 : Nat.mod (ptr.offsetBytes.toNat + start) 1 = 0 := Nat.mod_one _
                      rw [Nat.ble_eq_true_of_le (Nat.zero_le a.alignLog2), hPow0, hMod1,
                        Nat.beq_refl]
                      rfl
                    have hMutOk : (isMutOut && !Mutability.beq a.mutability .mut) = false := by
                      cases isMutOut with
                      | false => rfl
                      | true =>
                        cases hMut with
                        | inl hF => cases hF
                        | inr hT => subst hT; exact hMutChk
                    have hInitSub : isSliceAllInit ((a.bytes.drop (ptr.offsetBytes.toNat + start)).take subLen) = true :=
                      isSliceAllInit_drop_take a.bytes ptr.offsetBytes.toNat len.toNat start subLen hSub hInit
                    rw [hInB, hAl0, hMutOk, hInitSub]
                    rfl
                  · exact hAid
                  · dsimp only
                    refine ⟨?_, hStartLt64, hPSubOff⟩
                    dsimp only [pSub]
                    rw [hAid]

theorem sliceFromRawPartsCheck_u8_zero_ptr
    {m : MemoryState} {isMut isMutOut : Bool} {ptr : PtrVal} {len : UInt64}
    {subLen : Nat}
    (hAllocLt : ∀ aid a, findAllocation aid m.allocations = some a →
      a.bytes.length < isizeMaxBytes)
    (hMut : isMutOut = false ∨ isMut = true)
    (hOrig : sliceFromRawPartsCheck m isMut 1 0 ptr len = .ok (.slicePtr ptr len))
    (hSub : subLen ≤ len.toNat) :
    ptrAddInMem m 1 ptr 0 = .ok ptr ∧
    sliceFromRawPartsCheck m isMutOut 1 0 ptr (UInt64.ofNat subLen) =
      .ok (.slicePtr ptr (UInt64.ofNat subLen)) := by
  have h := sliceFromRawPartsCheck_u8_to_subslice hAllocLt hMut hOrig (start := 0) (subLen := subLen)
    (by rw [Nat.zero_add]; exact hSub)
  let ⟨pSub, hAdd, hChk, _, _, hEq⟩ := h
  have hPEq : pSub = ptr := by
    cases hAid : ptr.allocId with
    | none => rw [hAid] at hEq; exact hEq
    | some aid =>
      rw [hAid] at hEq
      have hSubEq := hEq.1
      rw [Nat.add_zero, uint64_ofNat_toNat] at hSubEq
      cases ptr; rw [← hAid] at hSubEq; exact hSubEq
  subst hPEq
  exact ⟨hAdd, hChk⟩

theorem refValidInMem_of_sliceCheck {m : MemoryState} {reqMut : Mutability}
    {ptr : PtrVal} {len : UInt64}
    (hChk : sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len =
      .ok (.slicePtr ptr len)) :
    refValidInMem m reqMut (.slice (.int .i8 false)) (.slicePtr ptr len) = .ok () := by
  unfold refValidInMem
  dsimp only [intLayout]
  rw [hChk]

theorem sliceCheck_of_refValidInMem {m : MemoryState} {reqMut : Mutability}
    {ptr : PtrVal} {len : UInt64}
    (hValid : refValidInMem m reqMut (.slice (.int .i8 false)) (.slicePtr ptr len) = .ok ()) :
    sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len =
      .ok (.slicePtr ptr len) := by
  unfold refValidInMem at hValid
  dsimp only [intLayout] at hValid
  cases hChk : sliceFromRawPartsCheck m (Mutability.beq reqMut .mut) 1 0 ptr len with
  | error k => rw [hChk] at hValid; cases hValid
  | ok v =>
    have hv := sliceFromRawPartsCheck_ok_val hChk
    subst hv
    rfl

theorem refsStayInCallerMem_of_sliceCheck
    {cm : CallerMemory} {isMut : Bool} {ptr pR : PtrVal} {len lenL lenR : UInt64}
    {m1 m2 : Mutability}
    (hOrig : sliceFromRawPartsCheck (entryMemoryWithCaller cm) isMut 1 0 ptr len =
      .ok (.slicePtr ptr len))
    (hAllocEq : pR.allocId = ptr.allocId) :
    refsStayInCallerMem cm
      (.tuple [.ref m1 (.slice (.int .i8 false)), .ref m2 (.slice (.int .i8 false))])
      (.tuple [.slicePtr ptr lenL, .slicePtr pR lenR]) = true := by
  unfold refsStayInCallerMem refAllocIds refAllocIdsList refAllocIds
  dsimp only [refAllocIdsList, refAllocIds]
  rw [hAllocEq]
  cases hAid : ptr.allocId with
  | none => rfl
  | some aid =>
    unfold sliceFromRawPartsCheck at hOrig
    dsimp only at hOrig
    cases hMax : Nat.blt (len.toNat * 1) isizeMaxBytes with
    | false => rw [hMax] at hOrig; cases hOrig
    | true =>
      rw [hMax, hAid] at hOrig
      dsimp only at hOrig
      cases hFind : findAllocation aid (entryMemoryWithCaller cm).allocations with
      | none => rw [hFind] at hOrig; cases hOrig
      | some a =>
        have hSome : (findAllocation aid cm.allocations).isSome = true := by
          change (findAllocation aid (entryMemoryWithCaller cm).allocations).isSome = true
          rw [hFind]
          rfl
        change ((findAllocation aid cm.allocations).isSome &&
            ((findAllocation aid cm.allocations).isSome && true)) = true
        rw [hSome]
        rfl

/-! ## Entry Inversion & Shared `split_at_unchecked` Correctness -/

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

theorem checkValV2_isize_inv {v : Val}
    (h : checkValV2 v (.int .isize false) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨.isize, false, bits⟩ ∧
      ScalarVal.wf ⟨.isize, false, bits⟩ = true := by
  cases v with
  | scalar sv =>
    have hCV : checkVal (.scalar sv) (.int .isize false) = true := h
    let ⟨bits, hEq, hTrunc⟩ := checkVal_int_iff.mp hCV
    have hWf : ScalarVal.wf ⟨.isize, false, bits⟩ = true := by
      unfold ScalarVal.wf
      dsimp only
      rw [hTrunc]
      exact beq_self_eq_true bits
    exact ⟨bits, hEq, hWf⟩
  | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _ | ptr _
  | rangeTo _ | rangeFrom _ | tuple _ | bytes _ => cases h

theorem spansPairwiseDisjoint_slice_u8_pair
    {ptr pR : PtrVal} {lenL lenR : UInt64} {m1 m2 : Mutability}
    (hDisj : (m1 = .shared ∧ m2 = .shared) ∨
      (match ptr.allocId with
       | none => pR = ptr
       | some aid =>
         pR.allocId = some aid ∧
         ptr.offsetBytes.toNat + lenL.toNat = pR.offsetBytes.toNat)) :
    spansPairwiseDisjoint
      (refAccessSpansList [.ref m1 (.slice (.int .i8 false)), .ref m2 (.slice (.int .i8 false))]
        [.slicePtr ptr lenL, .slicePtr pR lenR]) = true := by
  cases hDisj with
  | inl hSh =>
    let ⟨hm1, hm2⟩ := hSh
    subst hm1; subst hm2
    dsimp only [refAccessSpansList, refAccessSpans]
    cases ptr.allocId <;> cases pR.allocId <;> rfl
  | inr hMut =>
    dsimp only [refAccessSpansList, refAccessSpans]
    cases hAid : ptr.allocId with
    | none =>
      rw [hAid] at hMut
      subst hMut
      rw [hAid]
      rfl
    | some aid =>
      rw [hAid] at hMut
      rw [hMut.1]
      change spansPairwiseDisjoint
        [(Mutability.beq m1 .mut, aid, ptr.offsetBytes.toNat, lenL.toNat * 1),
         (Mutability.beq m2 .mut, aid, pR.offsetBytes.toNat, lenR.toNat * 1)] = true
      dsimp only [spansPairwiseDisjoint, spanDisjointWith, spanDisjoint]
      cases hM : (Mutability.beq m1 .mut || Mutability.beq m2 .mut) with
      | false => rfl
      | true =>
        have hBle : Nat.ble (ptr.offsetBytes.toNat + lenL.toNat * 1) pR.offsetBytes.toNat = true := by
          rw [Nat.mul_one, hMut.2]
          exact Nat.ble_eq_true_of_le (Nat.le_refl _)
        rw [hBle, Nat.beq_refl]
        cases Nat.beq (lenL.toNat * 1) 0 <;> cases Nat.beq (lenR.toNat * 1) 0 <;> rfl

theorem initLocalsLoop_body0 (ptrAid : Option AllocId) (ptrOff : UInt64) (len : UInt64)
    (midBits : BitVec 128) :
    initLocalsLoop Captured.body_0
      [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len, .scalar ⟨.isize, false, midBits⟩]
      0 Captured.body_0.locals =
    [.immediate none,
     .immediate (some (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len)),
     .immediate (some (.scalar ⟨.isize, false, midBits⟩)),
     .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead] :=
  rfl

theorem checkArgsMatchV2_slice_u8_isize_inv {reqMut : Mutability} {args : List Val}
    (h : checkArgsMatchV2 args [.ref reqMut (.slice (.int .i8 false)), .int .isize false] = true) :
    ∃ (ptr : PtrVal) (len : UInt64) (midBits : BitVec 128),
      args = [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩] ∧
      ptr.width = .isize ∧
      ScalarVal.wf ⟨.isize, false, midBits⟩ = true := by
  cases args with
  | nil => cases h
  | cons v0 rest =>
    cases rest with
    | nil =>
      dsimp only [checkArgsMatchV2] at h
      cases hV0 : checkValV2 v0 (.ref reqMut (.slice (.int .i8 false))) <;>
        rw [hV0] at h <;> cases h
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 (.ref reqMut (.slice (.int .i8 false))) <;> rw [hV0] at h
        · cases h
        · cases hV1 : checkValV2 v1 (.int .isize false) <;> rw [hV1] at h
          · cases h
          · cases h
      | nil =>
        dsimp only [checkArgsMatchV2] at h
        cases hV0 : checkValV2 v0 (.ref reqMut (.slice (.int .i8 false))) with
        | false => rw [hV0] at h; cases h
        | true =>
          rw [hV0] at h
          cases hV1 : checkValV2 v1 (.int .isize false) with
          | false => rw [hV1] at h; cases h
          | true =>
            let ⟨ptr, len, hv0, hPtrW⟩ := checkValV2_slice_u8_inv hV0
            let ⟨midBits, hv1, hMidWf⟩ := checkValV2_isize_inv hV1
            subst hv0; subst hv1
            exact ⟨ptr, len, midBits, rfl, hPtrW, hMidWf⟩

theorem readPlaceV2_copy_local {bodyLocals : List MirTy} {locals : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true) :
    readPlaceV2 bodyLocals locals mem false ⟨lid, []⟩ = .ok (ty, optVal, locals, mem) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [hSup]
  change (if false = true then Except.error FaultKind.unsupported else _) = _
  rw [ite_bool_false rfl]
  rfl

theorem readPlaceV2_move_local {bodyLocals : List MirTy} {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {optVal : Option Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some ty)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate optVal))
    (hSup : isSupportedV2LocalTy ty = true)
    (hSet : Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) = some locals') :
    readPlaceV2 bodyLocals locals mem true ⟨lid, []⟩ = .ok (ty, optVal, locals', mem) := by
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

theorem evalRvalueV2_use_copy_ok {bodyLocals : List MirTy} {locals : List LocalSlot}
    {mem : MemoryState} {dstTy : MirTy} {lid : LocalId} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some dstTy)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate (some v)))
    (hSup : isSupportedV2LocalTy dstTy = true)
    (hEq : MirTy.beq dstTy dstTy = true) :
    evalRvalueV2 bodyLocals locals mem dstTy (.use (.copy ⟨lid, []⟩)) = .ok (v, locals, mem) := by
  unfold evalRvalueV2 evalOperandToSlotV2
  dsimp only
  rw [readPlaceV2_copy_local hTy hSlot hSup]
  dsimp only
  rw [hEq]
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
    (hArgs : checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0,
      initLocalsLoop body q.args 0 body.locals, none, none, none⟩],
      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  unfold initStateV2
  rw [hPW, hPV, hCM, hEntry]
  dsimp only
  rw [hNonEmpty, hArgLt, hSto, hDiscr, hCast, hLocs]
  rw [hArgs, hRefs, hDisj]
  rfl

theorem writePlaceDestV2_immediate_ok {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) = some locals') :
    writePlaceDestV2 locals mem (.local lid) ty val = .ok (locals', mem) := by
  unfold writePlaceDestV2
  rw [ite_bool_false (by rw [hCheck]; rfl)]
  dsimp only
  rw [hSlot]
  dsimp only
  rw [hSet]

theorem writePlaceV2_immediate_ok {bodyLocals : List MirTy} {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hCheck : checkValV2 val ty = true)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.immediate (some val)) = some locals') :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val = .ok (locals', mem) := by
  unfold writePlaceV2 resolvePlaceDestV2
  dsimp only
  exact writePlaceDestV2_immediate_ok hCheck hSlot hSet

theorem execCoreCallOp_sliceGetUncheckedRangeFrom_shared_ok {m : MemoryState}
    {p pOut : PtrVal} {len lenOut startOff : UInt64}
    (hRef : refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr p len) = .ok ())
    (hGet : sliceGetUncheckedCheck m p len.toNat startOff.toNat len.toNat =
      .ok (.slicePtr pOut lenOut)) :
    execCoreCallOp m .sliceGetUncheckedRangeFrom
      [(.ref .shared (.slice (.int .i8 false)), .slicePtr p len),
       (.rangeFrom (.int .isize false), .rangeFrom startOff)]
      (.ref .shared (.slice (.int .i8 false))) = .ok (.slicePtr pOut lenOut) := by
  unfold execCoreCallOp
  change (if false = true then _ else _) = _
  rw [ite_bool_false rfl]
  rw [hRef]
  exact hGet

theorem evalRefRvalueV2_deref_ok {bodyLocals : List MirTy} {locals : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {srcMut reqMut : Mutability} {pt : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some (.ref srcMut pt))
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (.immediate (some v)))
    (hMut : (Mutability.beq srcMut .shared && Mutability.beq reqMut .mut) = false)
    (hDst : MirTy.beq (.ref reqMut pt) (.ref reqMut pt) = true)
    (hRef : refValidInMem mem reqMut pt v = .ok ()) :
    evalRefRvalueV2 bodyLocals locals mem (.ref reqMut pt) reqMut ⟨lid, [.deref]⟩ =
      .ok (v, locals, mem) := by
  unfold evalRefRvalueV2
  rw [hTy, hSlot]
  dsimp only
  rw [ite_bool_false hMut]
  rw [ite_bool_false (by rw [hDst]; rfl)]
  rw [hRef]

theorem evalTerminatorV2_return_ok {body : Body} {bb : BasicBlock} {frame : FrameState}
    {mem : MemoryState} {callerMem : CallerMemory} {retTy : MirTy} {retVal : Val}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 = some (.immediate (some retVal)))
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

theorem split_at_shared_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hSafe : Spec.splitAtSafety q) :
    match q.args with
    | [.slicePtr ptr len, .scalar mid] =>
      let pR :=
        match ptr.allocId with
        | none => ptr
        | some _ =>
          { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + mid.bits.toNat) }
      let lenL := UInt64.ofNat mid.bits.toNat
      let lenR := UInt64.ofNat (len.toNat - mid.bits.toNat)
      WellFormedV2 (entryProgForBody Captured.program 0) q ∧
      (∃ out : TerminalOut,
        BehaviorV2 (entryProgForBody Captured.program 0) q out ∧
        out = TerminalOut.returned
          ⟨.tuple [.slicePtr ptr lenL, .slicePtr pR lenR], q.callerMem⟩ ∧
        lenL.toNat + lenR.toNat = len.toNat)
    | _ => False := by
  let ⟨hCM, hMatch, hRefs, _⟩ := hValid
  have hMatch' :
      checkArgsMatchV2 q.args [.ref .shared (.slice (.int .i8 false)), .int .isize false] = true :=
    hMatch
  let ⟨ptr, len, midBits, hArgs, hPtrW, hMidWf⟩ := checkArgsMatchV2_slice_u8_isize_inv hMatch'
  unfold Spec.splitAtSafety at hSafe
  rw [hArgs] at hSafe
  cases ptr with
  | mk ptrAid ptrOff ptrW =>
    dsimp only at hPtrW
    subst hPtrW
    have hMidLe : midBits.toNat ≤ len.toNat := hSafe
    have hLenLt64 : len.toNat < Nat.pow 2 64 := len.toBitVec.isLt
    have hMidLt64 : midBits.toNat < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt hMidLe hLenLt64
    have hSubLt64 : len.toNat - midBits.toNat < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hLenLt64
    have hLenLNat : (UInt64.ofNat midBits.toNat).toNat = midBits.toNat :=
      toNat_uint64_ofNat_lt hMidLt64
    have hLenRNat : (UInt64.ofNat (len.toNat - midBits.toNat)).toNat =
        len.toNat - midBits.toNat :=
      toNat_uint64_ofNat_lt hSubLt64
    have hSumLen : (UInt64.ofNat midBits.toNat).toNat +
        (UInt64.ofNat (len.toNat - midBits.toNat)).toNat = len.toNat := by
      rw [hLenLNat, hLenRNat]
      exact Nat.add_sub_of_le hMidLe
    let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
    let m : MemoryState := entryMemoryWithCaller q.callerMem
    have hQ : q = ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ := by
      cases q; dsimp only at hArgs; rw [hArgs]
    have hRefValid0 :
        refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr ptr len) = .ok () := by
      have hRefs' :
          refsValidInMemList m
            [.ref .shared (.slice (.int .i8 false)), .int .isize false]
            [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩] = true := by
        rw [← hArgs]; exact hRefs
      dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
      cases hR : refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr ptr len) with
      | error k => rw [hR] at hRefs'; cases hRefs'
      | ok u => cases u; rfl
    have hOrig : sliceFromRawPartsCheck m false 1 0 ptr len = .ok (.slicePtr ptr len) :=
      sliceCheck_of_refValidInMem hRefValid0
    have hAllocLt := entryMemoryWithCaller_bytes_lt q.callerMem hCM
    have hZeroL := sliceFromRawPartsCheck_u8_zero_ptr hAllocLt (.inl rfl) hOrig hMidLe
    have hSubR := sliceFromRawPartsCheck_u8_to_subslice hAllocLt (.inl rfl) hOrig
      (start := midBits.toNat) (subLen := len.toNat - midBits.toNat)
      (by rw [Nat.add_sub_of_le hMidLe]; exact Nat.le_refl _)
    let ⟨pR, hPtrAddR, hSliceR, hPRAlloc, hPRW, hPRSpec⟩ := hSubR
    have hPRSpecEq : pR =
        match ptr.allocId with
        | none => ptr
        | some _ =>
          { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + midBits.toNat) } := by
      dsimp only [ptr] at hPRSpec ⊢
      cases hAid : ptrAid with
      | none => rw [hAid] at hPRSpec; exact hPRSpec
      | some aid => rw [hAid] at hPRSpec; exact hPRSpec.1
    let lenL := UInt64.ofNat midBits.toNat
    let lenR := UInt64.ofNat (len.toNat - midBits.toNat)
    let expectedOut : TerminalOut :=
      .returned ⟨.tuple [.slicePtr ptr lenL, .slicePtr pR lenR], q.callerMem⟩
    have hRefValidL :
        refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr ptr lenL) = .ok () :=
      refValidInMem_of_sliceCheck hZeroL.2
    have hRefValidR :
        refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr pR lenR) = .ok () :=
      refValidInMem_of_sliceCheck hSliceR
    have hGetTo :
        sliceGetUncheckedCheck m ptr len.toNat 0 lenL.toNat =
          .ok (.slicePtr ptr lenL) := by
      unfold sliceGetUncheckedCheck
      rw [hLenLNat]
      rw [Nat.ble_eq_true_of_le (Nat.zero_le _), Nat.ble_eq_true_of_le hMidLe]
      change (if false = true then _ else _) = _
      rw [ite_bool_false rfl]
      rw [hZeroL.1]
      dsimp only
      rw [Nat.sub_zero]
    have hGetFrom :
        sliceGetUncheckedCheck m ptr len.toNat lenL.toNat len.toNat =
          .ok (.slicePtr pR lenR) := by
      unfold sliceGetUncheckedCheck
      rw [hLenLNat]
      rw [Nat.ble_eq_true_of_le hMidLe, Nat.ble_eq_true_of_le (Nat.le_refl _)]
      change (if false = true then _ else _) = _
      rw [ite_bool_false rfl]
      rw [hPtrAddR]
    have hStay :
        refsStayInCallerMem q.callerMem
          (.tuple [.ref .shared (.slice (.int .i8 false)),
                   .ref .shared (.slice (.int .i8 false))])
          (.tuple [.slicePtr ptr lenL, .slicePtr pR lenR]) = true :=
      refsStayInCallerMem_of_sliceCheck hOrig hPRAlloc
    have hDisjOut :
        spansPairwiseDisjoint
          (refAccessSpansList
            [.ref .shared (.slice (.int .i8 false)),
             .ref .shared (.slice (.int .i8 false))]
            [.slicePtr ptr lenL, .slicePtr pR lenR]) = true :=
      spansPairwiseDisjoint_slice_u8_pair (.inl ⟨rfl, rfl⟩)
    have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
      extractCallerMemory_entry q.callerMem hCM
    have hInitDisj :
        spansPairwiseDisjoint
          (refAccessSpansList [.ref .shared (.slice (.int .i8 false)), .int .isize false]
            [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩]) = true := by
      dsimp only [refAccessSpansList, refAccessSpans]
      cases ptrAid <;> rfl
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ =
        .ok (State.mk [FrameState.mk 0 0 0
          [.immediate none,
           .immediate (some (.slicePtr ptr len)),
           .immediate (some (.scalar ⟨.isize, false, midBits⟩)),
           .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]
          none none none]
          q.callerMem m) := by
      have hChkArgs :
          checkArgsMatchV2 [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩]
            ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount) = true := by
        change checkArgsMatchV2 [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩]
          [.ref .shared (.slice (.int .i8 false)), .int .isize false] = true
        dsimp only [checkArgsMatchV2, checkValV2, checkVal, Val.ty?]
        rw [hMidWf]
        rfl
      have hRefsList :
          refsValidInMemList m
            ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount)
            [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩] = true := by
        change refsValidInMemList m
          [.ref .shared (.slice (.int .i8 false)), .int .isize false]
          [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩] = true
        dsimp only [refsValidInMemList, refsValidInMem]
        rw [hRefValid0]
        rfl
      have hDisjList :
          spansPairwiseDisjoint
            (refAccessSpansList
              ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount)
              [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩]) = true :=
        hInitDisj
      have h0 := initStateV2_ok_of (p := entryProgForBody Captured.program 0)
        (q := ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩)
        (body := Captured.body_0)
        rfl rfl hCM rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hChkArgs hRefsList hDisjList
      rw [h0]
      exact congrArg (fun ls => Except.ok
        (State.mk [FrameState.mk 0 0 0 ls none none none] q.callerMem m))
        (initLocalsLoop_body0 ptrAid ptrOff len midBits)
    have hExec :
        execProgV2 (entryProgForBody Captured.program 0) 32
          ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩
          (fun o => o = expectedOut) := by
      unfold execProgV2
      rw [hInit]
      -- bb0 stmts 0,1,2: storageLive 3,4,5
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 stmt 3: assign 5 (.ref .shared [1, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2,
          writePlaceDestV2, checkValV2, Trusted.MirSemantics.getElem?,
          Trusted.MirSemantics.setElem?]
        rw [hRefValid0]
        rfl)
      -- bb0 stmts 4,5: storageLive 6,7
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 stmt 6: assign 7 (.use (.copy 2))
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, Trusted.MirSemantics.getElem?]
        rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hMidWf]; rfl)
          (by rfl) (by rfl)])
      -- bb0 stmts 7,8: aggregateRangeTo -> 6, storageDead 7
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2,
          Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 term: coreCall sliceGetUncheckedRangeTo -> 4, bb1
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalArgOperandsV2, evalOperandToSlotV2,
          Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only [execCoreCallOp, writePlaceV2, jumpToBlock, checkValV2,
          Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
        rw [hRefValid0, hGetTo]
        rfl)
      -- bb1 stmt 0: assign 3 (.ref .shared [4, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2,
          writePlaceDestV2, checkValV2, Trusted.MirSemantics.getElem?,
          Trusted.MirSemantics.setElem?]
        rw [hRefValidL]
        rfl)
      -- bb1 stmts 1..5: storageDead 6,5; storageLive 8,9,10
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 stmt 6: assign 10 (.ref .shared [1, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2,
          writePlaceDestV2, checkValV2, Trusted.MirSemantics.getElem?,
          Trusted.MirSemantics.setElem?]
        rw [hRefValid0]
        rfl)
      -- bb1 stmts 7,8: storageLive 11,12
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 stmt 9: assign 12 (.use (.copy 2))
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, Trusted.MirSemantics.getElem?]
        rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hMidWf]; rfl)
          (by rfl) (by rfl)])
      -- bb1 stmts 10,11: aggregateRangeFrom -> 11, storageDead 12
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2,
          Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 term: coreCall sliceGetUncheckedRangeFrom -> 9, bb2
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalArgOperandsV2, evalOperandToSlotV2,
          Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [execCoreCallOp_sliceGetUncheckedRangeFrom_shared_ok hRefValid0 hGetFrom]
        dsimp only
        rw [writePlaceV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hPRW]; rfl)
          (by rfl) (by rfl)]
        rfl)
      -- bb2 stmt 0: assign 8 (.ref .shared [9, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2, Trusted.MirSemantics.getElem?]
        rw [evalRefRvalueV2_deref_ok (by rfl) (by rfl) (by rfl) (by rfl) hRefValidR]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hPRW]; rfl)
          (by rfl) (by rfl)])
      -- bb2 stmts 1..7: storageDead 11,10; aggregateTuple -> 0;
      -- storageDead 8,3,9,4.
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2, evalArgOperandsV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [ite_bool_false (by
          change (!checkValV2List [.slicePtr ptr lenL, .slicePtr pR lenR]
            [.ref .shared (.slice (.int .i8 false)),
             .ref .shared (.slice (.int .i8 false))]) = false
          dsimp only [checkValV2List, checkValV2]; rw [hPRW]; rfl)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by change checkValV2 (.tuple [.slicePtr ptr lenL, .slicePtr pR lenR]) _ = true
              dsimp only [checkValV2, checkValV2List]; rw [hPRW]; rfl)
          (by rfl) (by rfl)])
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb2 term: return_
      apply execOutcomeStateV2_done (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          Trusted.MirSemantics.getElem?]
        rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl) hStay
          (by dsimp only [refsValidInMem, refsValidInMemList]; rw [hRefValidL, hRefValidR]; rfl)
          hDisjOut, hExt]
        rfl)
      rfl
    have hRes := spec_and_behaviorV2_of_exec_eq hExec
    rw [← hQ] at hRes
    rw [hArgs]
    refine ⟨hRes.1, expectedOut, hRes.2.1, ?_, hSumLen⟩
    dsimp only [expectedOut]
    rw [hPRSpecEq]

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, ?_⟩
      intro q hValid hSafe
      have hId0 : Captured.body_0.identity = Spec.splitAtSharedIdentity := by decide
      have hPre : Spec.splitAtSafety q := by
        have hS := hSafe rfl
        change Spec.safetyPre Captured.body_0.identity q at hS
        unfold Spec.safetyPre at hS
        rw [hId0] at hS
        split at hS
        · exact hS
        · exact absurd rfl (by assumption)
      have hCor := split_at_shared_correct q hValid hPre
      let ⟨_, _, _, hArgs, _, _⟩ := checkArgsMatchV2_slice_u8_isize_inv hValid.2.1
      rw [hArgs] at hCor
      exact hCor.1
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · intro q hValid hSafe
    have hCor := split_at_shared_correct q hValid hSafe
    let ⟨_, _, _, hArgs, _, _⟩ := checkArgsMatchV2_slice_u8_isize_inv hValid.2.1
    rw [hArgs] at hCor ⊢
    exact hCor.2

end Proof
