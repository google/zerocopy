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

/-! ## Profile v2 Return Memory -/

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

/-- If the call created no allocation outside the caller's ids, the Profile v2
return memory is exactly the updated caller memory. -/
private theorem rm2_extractReturnMemoryV2_eq {cm : CallerMemory}
    {mem : MemoryState} (locals : List LocalSlot)
    (h : ∀ a, a ∈ mem.allocations → a.allocId ∈ allocIdsOf cm.allocations) :
    extractReturnMemoryV2 cm mem locals = extractCallerMemory cm mem := by
  unfold extractReturnMemoryV2
  rw [rm2_calleeLive_nil_of_sub h, List.append_nil]

private theorem rm2_extractReturnMemoryV2_entry (cm : CallerMemory)
    (locals : List LocalSlot) :
    extractReturnMemoryV2 cm (entryMemoryWithCaller cm) locals =
      extractCallerMemory cm (entryMemoryWithCaller cm) :=
  rm2_extractReturnMemoryV2_eq locals (fun _ ha => rm2_mem_allocIdsOf ha)

private theorem rm2_calleeLive_nil_of_dead {ids f : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids ∨ a.live = false) →
      calleeLiveAllocations ids f l = []
  | [], _ => rfl
  | a :: _, h => by
    unfold calleeLiveAllocations
    cases h a (.head _) with
    | inl hIn =>
      rw [rm2_natNotElem_false_of_mem hIn, Bool.and_false, Bool.false_and]
      exact rm2_calleeLive_nil_of_dead (fun b hb => h b (.tail _ hb))
    | inr hDead =>
      simp only [hDead, Bool.false_and]
      exact rm2_calleeLive_nil_of_dead (fun b hb => h b (.tail _ hb))

/-- Return memory equals the updated caller memory when every allocation is
either a caller allocation or dead. -/
private theorem rm2_extractReturnMemoryV2_eq_dead {cm : CallerMemory}
    {mem : MemoryState} (locals : List LocalSlot)
    (h : ∀ a, a ∈ mem.allocations →
      a.allocId ∈ allocIdsOf cm.allocations ∨ a.live = false) :
    extractReturnMemoryV2 cm mem locals = extractCallerMemory cm mem := by
  unfold extractReturnMemoryV2
  rw [rm2_calleeLive_nil_of_dead h, List.append_nil]

/-- A callee `.shared` (`.rodata`) allocation prepended to caller memory is not
caller-visible on return. -/
private theorem rm2_extractReturnMemoryV2_cons_shared {cm : CallerMemory}
    {n : Nat} {a : Allocation} {locals : List LocalSlot}
    (hA : a.mutability = .shared) :
    extractReturnMemoryV2 cm ⟨n, a :: cm.allocations⟩ locals =
      extractCallerMemory cm ⟨n, a :: cm.allocations⟩ := by
  unfold extractReturnMemoryV2
  have hTail : calleeLiveAllocations (allocIdsOf cm.allocations)
      (frameLocalAllocIds locals) cm.allocations = [] :=
    rm2_calleeLive_nil_of_sub (fun _ hb => rm2_mem_allocIdsOf hb)
  have hHead : calleeLiveAllocations (allocIdsOf cm.allocations)
      (frameLocalAllocIds locals) (a :: cm.allocations) = [] := by
    unfold calleeLiveAllocations
    rw [hA]
    simp only [show Mutability.beq Mutability.shared Mutability.mut = false
      from rfl, Bool.and_false, Bool.false_and]
    exact hTail
  change (⟨(extractCallerMemory cm ⟨n, a :: cm.allocations⟩).allocations ++
    calleeLiveAllocations (allocIdsOf cm.allocations)
      (frameLocalAllocIds locals) (a :: cm.allocations)⟩ : CallerMemory) = _
  rw [hHead, List.append_nil]

private theorem rm2_mem_replaceAllocation_ids {a' : Allocation}
    {ids : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids) →
      ∀ a, a ∈ replaceAllocation a' l → a.allocId ∈ ids
  | [], _, _, h => by cases h
  | b :: _, hl, a, ha => by
    unfold replaceAllocation at ha
    cases hB : Nat.beq b.allocId a'.allocId with
    | true =>
      rw [hB, ite_eq_left rfl] at ha
      cases ha with
      | head _ =>
        rw [← Nat.eq_of_beq_eq_true hB]
        exact hl b (.head _)
      | tail _ hr => exact hl a (.tail _ hr)
    | false =>
      rw [hB, ite_eq_right (fun h => Bool.noConfusion h)] at ha
      cases ha with
      | head _ => exact hl b (.head _)
      | tail _ hr =>
        exact rm2_mem_replaceAllocation_ids (fun c hc => hl c (.tail _ hc)) a hr

private theorem rm2_writeBytes_ids {ids : List AllocId} {m m' : MemoryState}
    {place : MemPlace} {al : Nat} {bs : List AllocByte}
    (h : writeBytes m place al bs = .ok m')
    (hm : ∀ b, b ∈ m.allocations → b.allocId ∈ ids) :
    ∀ b, b ∈ m'.allocations → b.allocId ∈ ids := by
  unfold writeBytes at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact hm
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; exact rm2_mem_replaceAllocation_ids hm

private theorem rm2_storeIndirectV2_ids {ids : List AllocId}
    {m m' : MemoryState} {ty : MirTy} {place : MemPlace} {v : Val}
    (h : storeIndirectV2 m ty place v = .ok m')
    (hm : ∀ b, b ∈ m.allocations → b.allocId ∈ ids) :
    ∀ b, b ∈ m'.allocations → b.allocId ∈ ids := by
  unfold storeIndirectV2 at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact rm2_writeBytes_ids h hm


/-! ## Profile v2 Decoder Unfolding -/

private theorem dv2_int (e : TargetEndian) (w : IntWidth) (s : Bool)
    (bs : List AllocByte) :
    decodeValV2 e (.int w s) bs = decodeVal e (.int w s) bs := rfl

private theorem dv2_array (e : TargetEndian) (elem : MirTy) (len : Nat)
    (bs : List AllocByte) :
    decodeValV2 e (.array elem len) bs =
      (match layoutOfTyV2 elem with
       | none => .error .unsupported
       | some elemLay =>
         if !Nat.beq bs.length (len * elemLay.size) then
           .error .unsupported
         else
           match decodeFixedChunks elemLay.size (decodeValV2 e elem) len bs with
           | .error k => .error k
           | .ok none => .ok none
           | .ok (some vs) => .ok (some (.array vs))) := rfl

private theorem dv2_struct (e : TargetEndian) (l : StructLayout) (fs : List MirTy)
    (bs : List AllocByte) :
    decodeValV2 e (.struct_ l fs) bs =
      (match layoutOfTyV2 (.struct_ l fs) with
       | none => .error .unsupported
       | some lay =>
         if !Nat.beq bs.length lay.size then
           .error .unsupported
         else
           match decodeStructFieldsV2 e bs l.fieldOffsets fs with
           | .error k => .error k
           | .ok none => .ok none
           | .ok (some vs) => .ok (some (.tuple vs))) := rfl

private theorem dsf_nil (e : TargetEndian) (bs : List AllocByte) :
    decodeStructFieldsV2 e bs [] [] = .ok (some []) := rfl

private theorem dsf_cons (e : TargetEndian) (bs : List AllocByte) (off : Nat)
    (offs : List Nat) (ty : MirTy) (tys : List MirTy) :
    decodeStructFieldsV2 e bs (off :: offs) (ty :: tys) =
      (match layoutOfTyV2 ty with
       | none => .error .unsupported
       | some fl =>
         match decodeValV2 e ty ((bs.drop off).take fl.size),
             decodeStructFieldsV2 e bs offs tys with
         | .error k, _ => .error k
         | _, .error k => .error k
         | .ok none, _ => .ok none
         | _, .ok none => .ok none
         | .ok (some v), .ok (some vs) => .ok (some (v :: vs))) := rfl

/-! ## Profile v2 Layout Unfolding -/

private theorem lv2_int (w : IntWidth) (s : Bool) :
    layoutOfTyV2 (.int w s) = some (intLayout w) := rfl

private theorem lv2_struct (l : StructLayout) (fs : List MirTy) :
    layoutOfTyV2 (.struct_ l fs) = layoutOfArrayV2 (.struct_ l fs) := rfl

private theorem lv2_array (e : MirTy) (n : Nat) :
    layoutOfTyV2 (.array e n) =
      (match layoutOfArrayV2 e with
       | none => none
       | some elemLay => some ⟨n * elemLay.size, elemLay.alignLog2⟩) := rfl

/-! ## Arithmetic, BitVec, and CallerMemory Helpers -/

theorem lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem le_of_ble_true {a b : Nat} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

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
    | true => rw [hEq] at h; cases h; exact .head _
    | false => rw [hEq] at h; exact .tail _ (findAllocation_mem h)

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

/-- A pointer offset inside an entry allocation, plus at most the
allocation's own size, stays below `2^64`. -/
theorem entry_offset_blt_pow64 {cm : CallerMemory} {aid : AllocId} {a : Allocation}
    {n : Nat} (hValid : validCallerMemory cm = true)
    (hFind : findAllocation aid (entryMemoryWithCaller cm).allocations = some a)
    (hLe : n ≤ a.bytes.length) : Nat.blt n (Nat.pow 2 64) = true := by
  have hLt : a.bytes.length < isizeMaxBytes :=
    allocIdsValid_bytes_lt [] cm.allocations hValid a (findAllocation_mem hFind)
  exact Nat.blt_eq.mpr (Nat.lt_trans (Nat.lt_of_le_of_lt hLe hLt) (by decide))

theorem findAllocation_allocId_eq {aid : AllocId} :
    ∀ {allocs : List Allocation} {a : Allocation},
      findAllocation aid allocs = some a → a.allocId = aid
  | [], _, h => by cases h
  | x :: xs, a, h => by
    change (if Nat.beq x.allocId aid then some x else findAllocation aid xs) = some a at h
    cases hEq : Nat.beq x.allocId aid with
    | true =>
      rw [hEq] at h; cases h
      exact Nat.eq_of_beq_eq_true hEq
    | false =>
      rw [hEq] at h
      exact findAllocation_allocId_eq h

theorem allocId_le_maxAllocId {allocs : List Allocation} {a : Allocation} (h : a ∈ allocs) :
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

theorem findAllocation_cons_ne {aid : AllocId} {x : Allocation} {xs : List Allocation}
    (hNe : x.allocId ≠ aid) :
    findAllocation aid (x :: xs) = findAllocation aid xs := by
  change (if Nat.beq x.allocId aid then some x else findAllocation aid xs) = findAllocation aid xs
  cases hEq : Nat.beq x.allocId aid with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe

theorem findAllocation_append_left_of_lt {aid : AllocId} {xs ys : List Allocation}
    (hFound : ∃ a, findAllocation aid xs = some a) :
    findAllocation aid (xs ++ ys) = findAllocation aid xs := by
  induction xs with
  | nil =>
    rcases hFound with ⟨_, h⟩
    cases h
  | cons x xs ih =>
    change (if Nat.beq x.allocId aid then some x else findAllocation aid (xs ++ ys)) =
      (if Nat.beq x.allocId aid then some x else findAllocation aid xs)
    cases hEq : Nat.beq x.allocId aid with
    | true => rfl
    | false =>
      apply ih
      rcases hFound with ⟨a, h⟩
      change (if Nat.beq x.allocId aid then some x else findAllocation aid xs) = some a at h
      rw [hEq] at h
      exact ⟨a, h⟩

theorem findAllocation_append_single_fresh {xs : List Allocation} {x : Allocation}
    (hFresh : ∀ a, a ∈ xs → a.allocId ≠ x.allocId) :
    findAllocation x.allocId (xs ++ [x]) = some x := by
  induction xs with
  | nil =>
    change (if Nat.beq x.allocId x.allocId then some x else none) = some x
    rw [Nat.beq_refl]
    rfl
  | cons hd tl ih =>
    have hNe : hd.allocId ≠ x.allocId := hFresh hd (.head _)
    have hBeq : Nat.beq hd.allocId x.allocId = false := by
      cases hEq : Nat.beq hd.allocId x.allocId with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe
    change (if Nat.beq hd.allocId x.allocId then some hd else findAllocation x.allocId (tl ++ [x])) =
      some x
    rw [hBeq]
    exact ih (fun a ha => hFresh a (.tail _ ha))

theorem extractCallerAllocations_of_found (m : MemoryState) :
    ∀ (suff : List Allocation),
      (∀ a, a ∈ suff → findAllocation a.allocId m.allocations = some a) →
      extractCallerAllocations m suff = suff
  | [], _ => rfl
  | a :: rest, hFind => by
    change (findAllocation a.allocId m.allocations).getD a :: extractCallerAllocations m rest = a :: rest
    rw [hFind a (.head _), extractCallerAllocations_of_found m rest (fun b hb => hFind b (.tail _ hb))]
    rfl

theorem extractCallerMemory_append_single {cm : CallerMemory} {x : Allocation}
    (hValid : validCallerMemory cm = true) :
    extractCallerMemory cm {
      nextAllocId := (entryMemoryWithCaller cm).nextAllocId + 1
      allocations := cm.allocations ++ [x]
    } = cm := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    have hSelf : ∀ a, a ∈ allocs → findAllocation a.allocId allocs = some a :=
      findAllocation_in_allocIdsValid [] allocs [] (fun _ h => by cases h)
        (fun _ h => by cases h) hValid
    have hApp : ∀ a, a ∈ allocs → findAllocation a.allocId (allocs ++ [x]) = some a := by
      intro a ha
      rw [findAllocation_append_left_of_lt ⟨a, hSelf a ha⟩]
      exact hSelf a ha
    rw [extractCallerAllocations_of_found _ allocs hApp]

theorem extractCallerMemory_cons_fresh {cm : CallerMemory} {x : Allocation}
    (hGt : maxAllocId cm.allocations < x.allocId) :
    ∀ {next : AllocId},
      extractCallerMemory cm { nextAllocId := next, allocations := x :: cm.allocations } =
        extractCallerMemory cm (entryMemoryWithCaller cm) := by
  intro next
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    apply congrArg CallerMemory.mk
    have hEq : ∀ suff : List Allocation,
        (∀ a, a ∈ suff → a.allocId ≤ maxAllocId allocs) →
        extractCallerAllocations { nextAllocId := next, allocations := x :: allocs } suff =
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

theorem initStateV2_ok_of {p : Program} {q : Query} {body : Body}
    (hPW : Nat.beq p.pointerWidthBits 64 = true)
    (hPV : Nat.beq p.mirProfileVersion 2 = true)
    (hCM : validCallerMemory q.callerMem = true)
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hNonEmpty : body.basicBlocks.isEmpty = false)
    (hArgLt : Nat.blt body.argumentCount body.locals.length = true)
    (hSto : storageAnnotationsInBounds body = true)
    (hDiscr : discriminantTypesValidV2 body = true)
    (hCast : castTypesValid body = true)
    (hAssert : assertConditionTypesValid body = true := by rfl)
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hArgs : checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true)
    (hNoRaw : tyListHasRawPtrV2
      ((body.locals.drop 1).take body.argumentCount) = false := by rfl) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0, initLocalsLoop body q.args 0 body.locals, none, none, none⟩],
      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  have hE : entryMemoryForArgsV2 q.callerMem
      ((body.locals.drop 1).take body.argumentCount) q.args =
        entryMemoryWithCaller q.callerMem := by
    unfold entryMemoryForArgsV2; dsimp only; rw [hNoRaw]; rfl
  unfold initStateV2
  rw [hPW, hPV, hCM, hEntry]
  dsimp only
  rw [hNonEmpty, hArgLt, hSto, hDiscr, hCast, hAssert, hLocs]
  rw [hArgs, hE, hRefs, hDisj]
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
  change (if true = true then match Trusted.MirSemantics.setElem? locals lid (liveUninitSlot ty) with
    | some locals1 => Except.ok (ty, optVal, locals1, mem)
    | none => Except.error FaultKind.unsupported else _) = _
  rw [hSet]
  rfl

theorem evalTerminatorV2_return_ok {body : Body} {bb : BasicBlock} {frame : FrameState}
    {mem : MemoryState} {callerMem : CallerMemory} {retTy : MirTy} {retVal : Val}
    {ps : PanicStrategy} {hLocal oc : Bool}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 = some (.immediate (some retVal)))
    (hNoRodata : hasEscapingRodataPtr callerMem mem retTy retVal = false)
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true)
    (hIds : ∀ a, a ∈ mem.allocations →
      a.allocId ∈ allocIdsOf callerMem.allocations := by
      exact fun _ ha => rm2_mem_allocIdsOf ha) :
    evalTerminatorV2 body bb frame mem callerMem ps hLocal oc =
      .done (.returned ⟨retVal, extractCallerMemory callerMem mem⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false hNoRodata, ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]
  rw [rm2_extractReturnMemoryV2_eq _ hIds]

/-! ## Inversion Helpers for Scalar, Enum, and Array Entry Values -/

private theorem checkValV2_scalar_inv {v : Val} {w : IntWidth} {s : Bool}
    (h : checkValV2 v (.int w s) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ ScalarVal.wf ⟨w, s, bits⟩ = true := by
  have h1 : checkVal v (.int w s) = true := by
    cases v with
    | scalar sv => unfold checkValV2 at h; exact h
    | bool _ | unit | char _ | ordering _ | tuple _ | enumVal _ _
    | ptr _ | vec _ _ _ | range _ _ | slicePtr _ _ | array _ | rangeTo _ | rangeFrom _ | bytes _ => cases h
    | optionVal o => cases o <;> cases h
    | boxPtr _ o => cases o <;> cases h
  exact let ⟨bits, hv, hTrunc⟩ := checkVal_int_iff.mp h1; ⟨bits, hv, beq_iff_eq.mpr hTrunc⟩

/-! ## Bodies 0-2: `make_pair`, `pair_tag`, `digest_byte` -/

/-! ## Reference, Byte, and List Helpers -/

private theorem checkValV2_ref_ptr_inv {reqMut : Mutability} {pt : MirTy}
    {hNonSlice : ∀ elem, pt ≠ .slice elem} {v : Val}
    (h : checkValV2 v (.ref reqMut pt) = true)
    (hNonStr : pt ≠ .str := by intro h; cases h) :
    ∃ p : PtrVal, v = .ptr p ∧ p.width = .isize := by
  cases pt with
  | slice elem => exact absurd rfl (hNonSlice elem)
  | str => exact absurd rfl hNonStr
  | _ =>
    cases v with
    | ptr p =>
      cases p with
      | mk aid off pw =>
        unfold checkValV2 at h
        dsimp only at h
        cases hW : IntWidth.beq pw .isize with
        | false =>
          rw [hW] at h
          cases h
        | true =>
          have hEqW : pw = .isize := by cases pw <;> first | rfl | cases hW
          exact ⟨⟨aid, off, pw⟩, rfl, hEqW⟩
    | bool _ | scalar _ | unit | char _ | ordering _ | tuple _ | enumVal _ _
    | vec _ _ _ | range _ _ | slicePtr _ _ | array _ | rangeTo _ | rangeFrom _ | bytes _ => cases h
    | optionVal o => cases o <;> cases h
    | boxPtr _ o => cases o <;> cases h

private theorem scalarWf_i8_ofNat_lt {n : Nat} (hLt : n < 256) :
    ScalarVal.wf ⟨.i8, false, BitVec.ofNat 128 n⟩ = true := by
  have hT : truncateBits .i8 (BitVec.ofNat 128 n) = BitVec.ofNat 128 n := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits, BitVec.toNat_ofNat]
    change (n % Nat.pow 2 128) % 256 = n % Nat.pow 2 128
    have h128 : n < Nat.pow 2 128 := Nat.lt_trans hLt (by decide)
    rw [Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt hLt]
  unfold ScalarVal.wf
  exact beq_iff_eq.mpr hT

private theorem checkValV2_u8_ofNat_lt {n : Nat} (hLt : n < 256) :
    checkValV2 (.scalar ⟨.i8, false, BitVec.ofNat 128 n⟩) (.int .i8 false) = true := by
  have hWf := scalarWf_i8_ofNat_lt hLt
  unfold ScalarVal.wf at hWf
  unfold checkValV2
  exact checkVal_int_iff.mpr ⟨_, rfl, eq_of_beq hWf⟩

private theorem decodeValV2_u8_uninit :
    decodeValV2 profileV2TargetEndian (.int .i8 false) [.uninit] = .ok none := by
  rw [dv2_int]
  unfold decodeVal layoutOfTy
  dsimp only [intLayout]
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  rfl

private theorem decodeValV2_u8_init (b : UInt8) (prov : Option AllocId) :
    decodeValV2 profileV2TargetEndian (.int .i8 false) [.init b prov] =
      .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)) := by
  have hBLt : b.toNat < 256 := b.toBitVec.isLt
  have hTrunc : truncateBits .i8 (BitVec.ofNat 128 b.toNat) = BitVec.ofNat 128 b.toNat := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits, BitVec.toNat_ofNat]
    change (b.toNat % Nat.pow 2 128) % 256 = b.toNat % Nat.pow 2 128
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hBLt (by decide)), Nat.mod_eq_of_lt hBLt]
  rw [dv2_int]
  unfold decodeVal layoutOfTy
  dsimp only [intLayout, initBytes?, decodeUInt]
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  have hDecB : natOfLeBytes [b] = b.toNat := by
    dsimp only [natOfLeBytes]; rw [Nat.mul_zero, Nat.add_zero]
  change (match evalConstLit (.int .i8 false) (.scalar (BitVec.ofNat 128 (natOfLeBytes [b]))) with
    | Except.ok v => Except.ok (some v)
    | Except.error k => Except.error k) = _
  rw [hDecB]
  dsimp only [evalConstLit]
  rw [hTrunc]
  rw [ite_bool_false (bne_self_eq_false _)]

private theorem getElem_drop_take_1 {off : Nat} {bs : List AllocByte} {x : AllocByte}
    (h : Trusted.MirSemantics.getElem? bs off = some x) :
    (bs.drop off).take 1 = [x] := by
  induction off generalizing bs with
  | zero =>
    cases bs with
    | nil => cases h
    | cons hd tl => cases h; rfl
  | succ k ih =>
    cases bs with
    | nil => cases h
    | cons _ tl => exact ih h

private theorem getElem?_some_of_lt :
    ∀ {bs : List AllocByte} {k : Nat}, k < bs.length →
      ∃ x, Trusted.MirSemantics.getElem? bs k = some x
  | [], _, h => by cases h
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: tl, k + 1, h => getElem?_some_of_lt (bs := tl) (Nat.lt_of_succ_lt_succ h)

private theorem take_take_of_le {α : Type} :
    ∀ (l : List α) (n m : Nat), n ≤ m → (l.take m).take n = l.take n
  | _, 0, _, _ => rfl
  | _, _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | [], _ + 1, _ + 1, _ => rfl
  | a :: l, n + 1, m + 1, h =>
    congrArg (a :: ·) (take_take_of_le l n m (Nat.le_of_succ_le_succ h))

private theorem take_drop_take {α : Type} :
    ∀ (l : List α) (k n m : Nat), k + n ≤ m →
      ((l.take m).drop k).take n = (l.drop k).take n
  | l, 0, n, m, h => take_take_of_le l n m (by rw [Nat.zero_add] at h; exact h)
  | _, k + 1, _, 0, h =>
    absurd (Nat.le_trans (Nat.le_add_right (k + 1) _) h) (Nat.not_succ_le_zero k)
  | [], _ + 1, _, _ + 1, _ => rfl
  | _ :: l, k + 1, n, m + 1, h =>
    take_drop_take l k n m
      (Nat.le_of_succ_le_succ (by rw [Nat.add_right_comm k 1 n] at h; exact h))

/-- `isAligned` at alignment `2^0` holds at every offset. -/
private theorem isAligned_zero (a : Allocation) (off : Nat) : isAligned a off 0 = true := by
  unfold isAligned
  change (Nat.ble 0 a.alignLog2 && Nat.beq (off % 1) 0) = true
  rw [Nat.mod_one, Nat.beq_refl, Nat.ble_eq.mpr (Nat.zero_le _)]
  rfl

/-- One-byte `u8` load from an in-bounds live allocation byte. -/
private theorem loadIndirectV2_u8 {m : MemoryState} {aid : AllocId} {a : Allocation}
    {off : Nat} {x : AllocByte}
    (hFind : findAllocation aid m.allocations = some a) (hLive : a.live = true)
    (hInB : isInBounds a off 1 = true)
    (hGet : Trusted.MirSemantics.getElem? a.bytes off = some x) :
    loadIndirectV2 m (.int .i8 false) ⟨aid, off⟩ =
      decodeValV2 profileV2TargetEndian (.int .i8 false) [x] := by
  unfold loadIndirectV2
  dsimp only [lv2_int, lv2_array, lv2_struct, layoutOfTy, intLayout]
  unfold readBytes
  rw [hFind]
  dsimp only
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; (rw [hLive, hInB, isAligned_zero]; rfl)
  rw [getElem_drop_take_1 hGet]

/-! ## Body 0: `make_pair` -/

private theorem make_pair_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q ∧
    match q.args with
    | [tag, value] =>
      BehaviorV2 (entryProgForBody Captured.program 0) q
        (TerminalOut.returned ⟨.tuple [tag, value], q.callerMem⟩)
    | _ => False := by
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  cases hList : q.args with
  | nil => rw [hList] at hArgs; cases hArgs
  | cons v0 rest =>
    cases rest with
    | nil =>
      rw [hList] at hArgs
      dsimp only [Captured.body_0, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.int .i8 false) <;> rw [hV0] at hArgs <;> cases hArgs
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hList] at hArgs
        dsimp only [Captured.body_0, checkArgsMatchV2, List.drop, List.take] at hArgs
        cases hV0 : checkValV2 v0 (.int .i8 false) <;>
          cases hV1 : checkValV2 v1 (.int .i32 false) <;>
          rw [hV0, hV1] at hArgs <;> cases hArgs
      | nil =>
        rw [hList] at hArgs
        dsimp only [Captured.body_0, checkArgsMatchV2, List.drop, List.take] at hArgs
        cases hV0 : checkValV2 v0 (.int .i8 false) with
        | false => rw [hV0] at hArgs; cases hArgs
        | true =>
          cases hV1 : checkValV2 v1 (.int .i32 false) with
          | false => rw [hV0, hV1] at hArgs; cases hArgs
          | true =>
            let ⟨bits0, hv0, _⟩ := checkValV2_scalar_inv hV0
            let ⟨bits1, hv1, _⟩ := checkValV2_scalar_inv hV1
            subst hv0
            subst hv1
            let expectedOut : TerminalOut :=
              .returned ⟨.tuple [.scalar ⟨.i8, false, bits0⟩,
                .scalar ⟨.i32, false, bits1⟩], q.callerMem⟩
            have hInit : initStateV2 (entryProgForBody Captured.program 0) q =
                .ok ⟨[⟨0, 0, 0,
                    initLocalsLoop Captured.body_0 q.args 0 Captured.body_0.locals, none, none, none⟩],
                  q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
              apply initStateV2_ok_of (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
                (by decide) (by decide) (by decide) (by decide) (by decide)
              · rw [hList]; exact hArgs
              · exact hRefs
              · exact hDisj
            have hLocs :
                initLocalsLoop Captured.body_0 q.args 0 Captured.body_0.locals =
                  [.immediate none,
                   .immediate (some (.scalar ⟨.i8, false, bits0⟩)),
                   .immediate (some (.scalar ⟨.i32, false, bits1⟩)),
                   .dead, .dead] := by
              rw [hList]; rfl
            have hExec : execProgV2 (entryProgForBody Captured.program 0) 10 q
                (fun o => o = expectedOut) := by
              unfold execProgV2
              rw [hInit, hLocs]
              -- bb0 stmt 0: storageLive 3
              apply execOutcomeStateV2_step (by rfl)
              -- bb0 stmt 1: _3 = copy _1
              apply execOutcomeStateV2_step (by
                dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                    List.nil_append, entryProgForBody, Captured.program,
                  Captured.body_0, List.append, Trusted.MirSemantics.getElem?,
                  evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                  placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2]
                rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
                dsimp only
                rw [ite_bool_false]; rotate_left; decide
                dsimp only
                rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
              -- bb0 stmt 2: storageLive 4
              apply execOutcomeStateV2_step (by rfl)
              -- bb0 stmt 3: _4 = copy _2
              apply execOutcomeStateV2_step (by
                dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                    List.nil_append, entryProgForBody, Captured.program,
                  Captured.body_0, List.append, Trusted.MirSemantics.getElem?,
                  evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                  placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2]
                rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
                dsimp only
                rw [ite_bool_false]; rotate_left; decide
                dsimp only
                rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)
              -- bb0 stmt 4: _0 = Pair { tag: move _3, value: move _4 }
              apply execOutcomeStateV2_step (by
                dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                    List.nil_append, entryProgForBody, Captured.program,
                  Captured.body_0, List.append, Trusted.MirSemantics.getElem?,
                  evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                  placeStaticTyV2, evalRvalueV2, evalArgOperandsV2, evalOperandToSlotV2]
                rw [ite_bool_false]; rotate_left; decide
                rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
                dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
                rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
                dsimp only [argValues]
                have hCL : checkValV2List [.scalar ⟨.i8, false, bits0⟩,
                    .scalar ⟨.i32, false, bits1⟩]
                    [.int .i8 false, .int .i32 false] = true := by
                  dsimp only [checkValV2List]; rw [hV0, hV1]; rfl
                have hChk : checkValV2 (.tuple [.scalar ⟨.i8, false, bits0⟩,
                    .scalar ⟨.i32, false, bits1⟩])
                    (.struct_ ⟨2921967349, 8, 2, [4, 0]⟩
                      [.int .i8 false, .int .i32 false]) = true := by
                  unfold checkValV2; exact hCL
                simp only [hCL]
                rw [ite_bool_false]; rotate_left; rfl
                dsimp only
                rw [writePlaceDestV2_immediate_ok hChk (by rfl) (by rfl)]; rfl)
              -- bb0 stmt 5..6: storageDead 4, storageDead 3
              apply execOutcomeStateV2_step (by rfl)
              apply execOutcomeStateV2_step (by rfl)
              -- bb0: return
              apply execOutcomeStateV2_done (by
                dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                    List.nil_append, entryProgForBody, Captured.program,
                  Captured.body_0, List.append, Trusted.MirSemantics.getElem?]
                rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
                  (by rfl) (by rfl) (by rfl) (by rfl)]
                rw [extractCallerMemory_entry q.callerMem hCM]
                rfl)
              rfl
            have hRes := spec_and_behaviorV2_of_exec_eq hExec
            exact ⟨hRes.1, hRes.2.1⟩

/-! ## Body 1: `pair_tag` -/

local notation "pairTy" => MirTy.struct_ (StructLayout.mk 2921967349 8 2 [4, 0])
  [MirTy.int IntWidth.i8 false, MirTy.int IntWidth.i32 false]

private theorem layoutOfTyV2_pair : layoutOfTyV2 pairTy = some ⟨8, 2⟩ := by rfl

private theorem projectMemoryLayoutV2_pair_tag :
    projectMemoryLayoutV2 pairTy [.field 0 (.int .i8 false)] = .ok (.int .i8 false, 4) := by
  rfl

private theorem refValidInMem_pair_inv {m : MemoryState} {p : PtrVal}
    (hRef : refValidInMem m .shared pairTy (.ptr p) = .ok ()) :
    ∃ (aid : AllocId) (a : Allocation),
      p.allocId = some aid ∧
      findAllocation aid m.allocations = some a ∧
      a.live = true ∧
      isInBounds a p.offsetBytes.toNat 8 = true ∧
      isAligned a p.offsetBytes.toNat 2 = true ∧
      ∃ w, decodeValV2 profileV2TargetEndian pairTy
        ((a.bytes.drop p.offsetBytes.toNat).take 8) = .ok (some w) := by
  unfold refValidInMem at hRef
  rw [layoutOfTyV2_pair] at hRef
  dsimp only at hRef
  cases hAid : p.allocId with
  | none =>
    rw [hAid] at hRef
    dsimp only at hRef
    have hZ : (Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 8) = true := by
      cases Nat.beq p.offsetBytes.toNat 0 <;> rfl
    rw [hZ] at hRef
    cases hRef
  | some aid =>
    rw [hAid] at hRef
    dsimp only at hRef
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at hRef; cases hRef
    | some a =>
      rw [hFind] at hRef
      dsimp only at hRef
      cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat 8 ||
          !isAligned a p.offsetBytes.toNat 2) with
      | true => rw [hBad] at hRef; cases hRef
      | false =>
        rw [hBad] at hRef
        rw [ite_bool_false] at hRef; rotate_left; rfl
        have hLive : a.live = true := by
          cases hL : a.live with
          | true => rfl
          | false => rw [hL] at hBad; cases hBad
        have hInB : isInBounds a p.offsetBytes.toNat 8 = true := by
          cases hI : isInBounds a p.offsetBytes.toNat 8 with
          | true => rfl
          | false => rw [hI] at hBad; cases hL : a.live <;> rw [hL] at hBad <;> cases hBad
        have hAl : isAligned a p.offsetBytes.toNat 2 = true := by
          cases hA : isAligned a p.offsetBytes.toNat 2 with
          | true => rfl
          | false =>
            rw [hA] at hBad
            cases hL : a.live <;> cases hI : isInBounds a p.offsetBytes.toNat 8 <;>
              rw [hL, hI] at hBad <;> cases hBad
        cases hDec : decodeValV2 profileV2TargetEndian pairTy
            ((a.bytes.drop p.offsetBytes.toNat).take 8) with
        | error _ => rw [hDec] at hRef; cases hRef
        | ok r =>
          cases r with
          | none => rw [hDec] at hRef; cases hRef
          | some w => exact ⟨aid, a, rfl, hFind, hLive, hInB, hAl, w, hDec⟩

/-- A successfully decoded `Pair` has an initialized `tag` byte at offset 4. -/
private theorem pair_tag_byte_init {bs : List AllocByte} {off : Nat} {x : AllocByte}
    {w : Val}
    (hGet : Trusted.MirSemantics.getElem? bs (off + 4) = some x)
    (hDec : decodeValV2 profileV2TargetEndian pairTy ((bs.drop off).take 8) =
      .ok (some w)) :
    ∃ (b : UInt8) (prov : Option AllocId), x = .init b prov := by
  cases x with
  | init b prov => exact ⟨b, prov, rfl⟩
  | uninit =>
    exfalso
    rw [dv2_struct] at hDec
    rw [layoutOfTyV2_pair] at hDec
    dsimp only at hDec
    cases hLen : Nat.beq ((bs.drop off).take 8).length 8 with
    | false =>
      rw [hLen] at hDec
      rw [ite_bool_true] at hDec; rotate_left; rfl
      cases hDec
    | true =>
      rw [hLen] at hDec
      rw [ite_bool_false] at hDec; rotate_left; rfl
      dsimp only [dsf_cons, dsf_nil, lv2_int, lv2_array, lv2_struct, layoutOfTy,
        intLayout] at hDec
      rw [take_drop_take _ 4 1 8 (by decide), List.drop_drop, getElem_drop_take_1 hGet,
        decodeValV2_u8_uninit] at hDec
      generalize decodeValV2 profileV2TargetEndian (MirTy.int IntWidth.i32 false)
        (List.take 4 (List.drop 0 (List.take 8 (List.drop off bs)))) = r at hDec
      cases r with
      | error _ => cases hDec
      | ok r' => cases r' <;> cases hDec

private theorem pair_tag_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q ∧
    match q.args with
    | [.ptr pv] =>
      match pv.allocId with
      | none => False
      | some aid =>
        ∃ v : Val,
          loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
            ⟨aid, pv.offsetBytes.toNat + 4⟩ = .ok (some v) ∧
          BehaviorV2 (entryProgForBody Captured.program 1) q
            (TerminalOut.returned ⟨v, q.callerMem⟩)
    | _ => False := by
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  let hArgsOrig := hArgs
  let hRefsOrig := hRefs
  cases hList : q.args with
  | nil => rw [hList] at hArgs; cases hArgs
  | cons v0 rest =>
    cases rest with
    | cons _ _ =>
      rw [hList] at hArgs
      dsimp only [Captured.body_1, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.ref .shared pairTy) <;> rw [hV0] at hArgs <;> cases hArgs
    | nil =>
      rw [hList] at hArgs hRefs
      dsimp only [Captured.body_1, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.ref .shared pairTy) with
      | false => rw [hV0] at hArgs; cases hArgs
      | true =>
        let ⟨pv, hvp, _⟩ := checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV0
        subst hvp
        dsimp only [Captured.body_1, refsValidInMemList, refsValidInMem, List.drop,
          List.take] at hRefs
        cases hRP : refValidInMem (entryMemoryWithCaller q.callerMem) .shared pairTy
            (.ptr pv) with
        | error _ => rw [hRP] at hRefs; cases hRefs
        | ok _ =>
          rcases refValidInMem_pair_inv hRP with
            ⟨aid, a, hPId, hFind, hLive, hInB, hAl, w, hDec⟩
          have hLe8 : pv.offsetBytes.toNat + 8 ≤ a.bytes.length := le_of_ble_true hInB
          have hInB4 : isInBounds a (pv.offsetBytes.toNat + 4) 1 = true := by
            unfold isInBounds
            rw [Nat.add_assoc]
            exact Nat.ble_eq.mpr (Nat.le_trans
              (Nat.add_le_add_left (by decide : 4 + 1 ≤ 8) _) hLe8)
          have hLt4 : pv.offsetBytes.toNat + 4 < a.bytes.length :=
            Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 8) _) hLe8
          have hOffLt : Nat.blt (pv.offsetBytes.toNat + 4) (Nat.pow 2 64) = true :=
            entry_offset_blt_pow64 hCM hFind (Nat.le_of_lt hLt4)
          rcases getElem?_some_of_lt hLt4 with ⟨x, hGet⟩
          rcases pair_tag_byte_init hGet hDec with ⟨b, prov, hx⟩
          subst hx
          let v : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩
          have hLoad : loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
              ⟨aid, pv.offsetBytes.toNat + 4⟩ = .ok (some v) := by
            rw [loadIndirectV2_u8 hFind hLive hInB4 hGet, decodeValV2_u8_init]
          have hChk : checkValV2 v (.int .i8 false) = true :=
            checkValV2_u8_ofNat_lt b.toBitVec.isLt
          let expectedOut : TerminalOut := .returned ⟨v, q.callerMem⟩
          have hInit : initStateV2 (entryProgForBody Captured.program 1) q =
              .ok ⟨[⟨1, 0, 0, initLocalsLoop Captured.body_1 q.args 0
                  Captured.body_1.locals, none, none, none⟩],
                q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
            apply initStateV2_ok_of (p := entryProgForBody Captured.program 1) (q := q)
              (body := Captured.body_1) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
              (by decide) (by decide) (by decide) (by decide) (by decide)
            · exact hArgsOrig
            · exact hRefsOrig
            · exact hDisj
          have hLocs : initLocalsLoop Captured.body_1 q.args 0 Captured.body_1.locals =
              [.immediate none, .immediate (some (.ptr pv))] := by
            rw [hList]; rfl
          have hExec : execProgV2 (entryProgForBody Captured.program 1) 3 q
              (fun o => o = expectedOut) := by
            unfold execProgV2
            rw [hInit, hLocs]
            -- bb0 stmt 0: _0 = copy (*_1).0
            apply execOutcomeStateV2_step (by
              dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                  List.nil_append, entryProgForBody, Captured.program, Captured.body_1,
                List.append, Trusted.MirSemantics.getElem?, evalStatementV2,
                resolvePlaceDestV2, resolveIndexProjsV2, consResolvedProjV2,
                placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2]
              rw [ite_bool_false]; rotate_left; rfl
              rw [ite_bool_true]; rotate_left; rfl
              dsimp only [readDerefProjectedV2]
              rw [ite_bool_false]; rotate_left; rfl
              rw [layoutOfTyV2_pair]
              dsimp only
              rw [projectMemoryLayoutV2_pair_tag]
              dsimp only
              rw [show layoutOfTyV2 (MirTy.int IntWidth.i8 false) = some ⟨1, 0⟩ from rfl]
              dsimp only
              rw [hPId]
              dsimp only
              rw [hFind]
              dsimp only
              rw [ite_bool_false]; rotate_left; (rw [hLive, hInB, hAl, hOffLt]; rfl)
              rw [hLoad]
              dsimp only
              rw [ite_bool_false]; rotate_left; decide
              dsimp only
              rw [writePlaceDestV2_immediate_ok hChk (by rfl) (by rfl)]; rfl)
            -- bb0: return
            apply execOutcomeStateV2_done (by
              dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                  List.nil_append, entryProgForBody, Captured.program, Captured.body_1,
                List.append, Trusted.MirSemantics.getElem?]
              rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
                (by rfl) (by rfl) (by rfl) (by rfl)]
              rw [extractCallerMemory_entry q.callerMem hCM]
              rfl)
            rfl
          have hRes := spec_and_behaviorV2_of_exec_eq hExec
          refine ⟨hRes.1, ?_⟩
          dsimp only
          rw [hPId]
          exact ⟨v, hLoad, hRes.2.1⟩

/-! ## Body 2: `digest_byte` -/

local notation "u8x4" => MirTy.array (MirTy.int IntWidth.i8 false) 4

local notation "digestTy" => MirTy.struct_ (StructLayout.mk 1530084049 4 0 [0]) [u8x4]

private theorem layoutOfTyV2_digest : layoutOfTyV2 digestTy = some ⟨4, 0⟩ := by rfl

private theorem land_three_lo : ∀ n : Nat, n < 128 → Nat.land n 3 = n % 4 := by decide

private theorem land_three_hi :
    ∀ n : Nat, n < 128 → Nat.land (128 + n) 3 = (128 + n) % 4 := by decide

private theorem land_three_eq_mod_four (n : Nat) (h : n < 256) : Nat.land n 3 = n % 4 := by
  cases Nat.lt_or_ge n 128 with
  | inl hLo => exact land_three_lo n hLo
  | inr hHi =>
    let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hHi
    subst hk
    exact land_three_hi k (Nat.lt_of_add_lt_add_left (h : 128 + k < 128 + 128))

private theorem lt_four_cases {k : Nat} (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  cases k with
  | zero => exact .inl rfl
  | succ k =>
    cases k with
    | zero => exact .inr (.inl rfl)
    | succ k =>
      cases k with
      | zero => exact .inr (.inr (.inl rfl))
      | succ k =>
        cases k with
        | zero => exact .inr (.inr (.inr rfl))
        | succ k =>
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)))) (Nat.not_lt_zero k)

private theorem toNat_ofNat_lt {k : Nat} (hk : k < 256) : (BitVec.ofNat 128 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans hk (by decide))

private theorem evalBinOp_bitAnd_three {bits : BitVec 128} (hLt : bits.toNat < 256) :
    evalBinOp .bitAnd (.scalar ⟨.i8, false, bits⟩) (.scalar ⟨.i8, false, BitVec.ofNat 128 3⟩) =
      .ok (.scalar ⟨.i8, false, BitVec.ofNat 128 (bits.toNat % 4)⟩) := by
  have hMod4 : bits.toNat % 4 < 256 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hEq : truncateBits .i8 (bvAnd (truncateBits .i8 bits)
      (truncateBits .i8 (BitVec.ofNat 128 3))) = BitVec.ofNat 128 (bits.toNat % 4) := by
    apply bitVec_eq_of_toNat_eq
    have h3 : (truncateBits .i8 (BitVec.ofNat 128 3)).toNat = 3 := by rfl
    unfold bvAnd
    rw [toNat_truncateBits, BitVec.toNat_ofNat, h3, toNat_truncateBits]
    change ((bits.toNat % 256).land 3 % Nat.pow 2 128) % 256 = _
    rw [Nat.mod_eq_of_lt hLt, land_three_eq_mod_four _ hLt, toNat_ofNat_lt hMod4,
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide) :
        bits.toNat % 4 < Nat.pow 2 128),
      Nat.mod_eq_of_lt hMod4]
  unfold evalBinOp
  dsimp only
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  rw [hEq]

private theorem evalIntToIntCast_u8_usize {k : Nat} (hk : k < 256) :
    evalIntToIntCast (.scalar ⟨.i8, false, BitVec.ofNat 128 k⟩) (.int .isize false) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 k⟩) := by
  have hTk := toNat_ofNat_lt hk
  unfold evalIntToIntCast intLikeBits
  dsimp only
  rw [ite_bool_false]; rotate_left; rfl
  dsimp only
  rw [truncateBits_of_toNat_lt (w := .i8) (x := BitVec.ofNat 128 k)
      (by rw [hTk]; exact hk), hTk,
    truncateBits_of_toNat_lt (w := .isize) (x := BitVec.ofNat 128 k)
      (by rw [hTk]; exact Nat.lt_trans hk (by decide))]

private theorem evalBinOp_lt_four {k : Nat} (hk : k < 4) :
    evalBinOp .lt (.scalar ⟨.isize, false, BitVec.ofNat 128 k⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 4⟩) = .ok (.bool true) := by
  rcases lt_four_cases hk with rfl | rfl | rfl | rfl <;> rfl

private theorem projectMemoryLayoutV2_digest_index {k : Nat} (hk : k < 4) :
    projectMemoryLayoutV2 digestTy [.field 0 u8x4, .constantIndex k (k + 1) false] =
      .ok (.int .i8 false, k) := by
  dsimp only [projectMemoryLayoutV2, Trusted.MirSemantics.getElem?]
  rw [ite_bool_false]; rotate_left; decide
  dsimp only [lv2_int, lv2_array, lv2_struct, layoutOfTy, intLayout]
  unfold constantIndexOffset
  have hBle : Nat.ble (k + 1) 4 = true := Nat.ble_eq.mpr hk
  have hBlt : Nat.blt k 4 = true := Nat.ble_eq.mpr hk
  rw [hBle]
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  rw [hBlt]
  rw [ite_bool_false]; rotate_left; rfl
  dsimp only
  rw [Nat.mul_one, Nat.add_zero, Nat.zero_add]

private theorem refValidInMem_digest_inv {m : MemoryState} {p : PtrVal}
    (hRef : refValidInMem m .shared digestTy (.ptr p) = .ok ()) :
    ∃ (aid : AllocId) (a : Allocation),
      p.allocId = some aid ∧
      findAllocation aid m.allocations = some a ∧
      a.live = true ∧
      isInBounds a p.offsetBytes.toNat 4 = true ∧
      ∃ w, decodeValV2 profileV2TargetEndian digestTy
        ((a.bytes.drop p.offsetBytes.toNat).take 4) = .ok (some w) := by
  unfold refValidInMem at hRef
  rw [layoutOfTyV2_digest] at hRef
  dsimp only at hRef
  cases hAid : p.allocId with
  | none =>
    rw [hAid] at hRef
    dsimp only at hRef
    have hZ : (Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 4) = true := by
      cases Nat.beq p.offsetBytes.toNat 0 <;> rfl
    rw [hZ] at hRef
    cases hRef
  | some aid =>
    rw [hAid] at hRef
    dsimp only at hRef
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at hRef; cases hRef
    | some a =>
      rw [hFind] at hRef
      dsimp only at hRef
      cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat 4 ||
          !isAligned a p.offsetBytes.toNat 0) with
      | true => rw [hBad] at hRef; cases hRef
      | false =>
        rw [hBad] at hRef
        rw [ite_bool_false] at hRef; rotate_left; rfl
        have hLive : a.live = true := by
          cases hL : a.live with
          | true => rfl
          | false => rw [hL] at hBad; cases hBad
        have hInB : isInBounds a p.offsetBytes.toNat 4 = true := by
          cases hI : isInBounds a p.offsetBytes.toNat 4 with
          | true => rfl
          | false => rw [hI] at hBad; cases hL : a.live <;> rw [hL] at hBad <;> cases hBad
        cases hDec : decodeValV2 profileV2TargetEndian digestTy
            ((a.bytes.drop p.offsetBytes.toNat).take 4) with
        | error _ => rw [hDec] at hRef; cases hRef
        | ok r =>
          cases r with
          | none => rw [hDec] at hRef; cases hRef
          | some w => exact ⟨aid, a, rfl, hFind, hLive, hInB, w, hDec⟩

private theorem decodeFixedChunks_get {f : List AllocByte → Except FaultKind (Option Val)} :
    ∀ (n : Nat) (bs : List AllocByte) (vs : List Val) (j : Nat),
      decodeFixedChunks 1 f n bs = .ok (some vs) → j < n →
      ∃ v, f ((bs.drop j).take 1) = .ok (some v)
  | 0, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, bs, vs, j, h, hj => by
    unfold decodeFixedChunks at h
    cases h1 : f (bs.take 1) with
    | error _ => rw [h1] at h; cases h
    | ok r1 =>
      cases h2 : decodeFixedChunks 1 f n (bs.drop 1) with
      | error _ => rw [h1, h2] at h; cases r1 <;> cases h
      | ok r2 =>
        rw [h1, h2] at h
        cases r1 with
        | none => cases h
        | some v1 =>
          cases r2 with
          | none => cases h
          | some vs2 =>
            cases j with
            | zero => exact ⟨v1, h1⟩
            | succ j' =>
              let ⟨v, hv⟩ := decodeFixedChunks_get n (bs.drop 1) vs2 j' h2
                (Nat.lt_of_succ_lt_succ hj)
              rw [List.drop_drop, Nat.add_comm] at hv
              exact ⟨v, hv⟩

/-- A successfully decoded `Digest` has an initialized byte at every index
`k < 4`. -/
private theorem digest_byte_init {bs : List AllocByte} {off k : Nat} {x : AllocByte}
    {w : Val} (hk : k < 4)
    (hGet : Trusted.MirSemantics.getElem? bs (off + k) = some x)
    (hDec : decodeValV2 profileV2TargetEndian digestTy ((bs.drop off).take 4) =
      .ok (some w)) :
    ∃ (b : UInt8) (prov : Option AllocId), x = .init b prov := by
  cases x with
  | init b prov => exact ⟨b, prov, rfl⟩
  | uninit =>
    exfalso
    rw [dv2_struct] at hDec
    rw [layoutOfTyV2_digest] at hDec
    dsimp only at hDec
    cases hLen : Nat.beq ((bs.drop off).take 4).length 4 with
    | false =>
      rw [hLen] at hDec
      rw [ite_bool_true] at hDec; rotate_left; rfl
      cases hDec
    | true =>
      rw [hLen] at hDec
      rw [ite_bool_false] at hDec; rotate_left; rfl
      dsimp only [dsf_cons, dsf_nil, lv2_int, lv2_array, lv2_struct, layoutOfTy,
        layoutOfArrayV2, intLayout] at hDec
      cases hA : decodeValV2 profileV2TargetEndian u8x4
          (List.take (4 * 1) (List.drop 0 (List.take 4 (List.drop off bs)))) with
      | error _ => rw [hA] at hDec; cases hDec
      | ok r =>
        cases r with
        | none => rw [hA] at hDec; cases hDec
        | some _ =>
          rw [dv2_array] at hA
          dsimp only [lv2_int, lv2_array, lv2_struct, layoutOfTy, layoutOfArrayV2, intLayout] at hA
          cases hL2 : Nat.beq
              (List.take (4 * 1) (List.drop 0 (List.take 4 (List.drop off bs)))).length
              (4 * 1) with
          | false =>
            rw [hL2] at hA
            rw [ite_bool_true] at hA; rotate_left; rfl
            cases hA
          | true =>
            rw [hL2] at hA
            rw [ite_bool_false] at hA; rotate_left; rfl
            cases hC : decodeFixedChunks 1
                (decodeValV2 profileV2TargetEndian (MirTy.int IntWidth.i8 false)) 4
                (List.take (4 * 1) (List.drop 0 (List.take 4 (List.drop off bs)))) with
            | error _ => rw [hC] at hA; cases hA
            | ok r =>
              cases r with
              | none => rw [hC] at hA; cases hA
              | some vs =>
                let ⟨_, hv⟩ := decodeFixedChunks_get 4 _ vs k hC hk
                rw [Nat.mul_one, List.drop_zero, take_drop_take _ k 1 4 hk,
                  take_drop_take _ k 1 4 hk, List.drop_drop, getElem_drop_take_1 hGet,
                  decodeValV2_u8_uninit] at hv
                cases hv

private theorem checkValV2_usize_ofNat_lt {n : Nat} (hLt : n < 256) :
    checkValV2 (.scalar ⟨.isize, false, BitVec.ofNat 128 n⟩) (.int .isize false) = true := by
  have hT : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [toNat_ofNat_lt hLt]; exact Nat.lt_trans hLt (by decide))
  unfold checkValV2
  exact checkVal_int_iff.mpr ⟨_, rfl, hT⟩

private theorem evalConstLit_u8_three :
    evalConstLit (.int .i8 false) (.scalar (BitVec.ofNat 128 3)) =
      .ok (.scalar ⟨.i8, false, BitVec.ofNat 128 3⟩) := by
  rfl

private theorem evalConstLit_usize_four :
    evalConstLit (.int .isize false) (.scalar (BitVec.ofNat 128 4)) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 4⟩) := by
  rfl

private theorem digest_byte_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q) :
    WellFormedV2 (entryProgForBody Captured.program 2) q ∧
    match q.args with
    | [.ptr pv, .scalar i] =>
      match pv.allocId with
      | none => False
      | some aid =>
        ∃ v : Val,
          loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
            ⟨aid, pv.offsetBytes.toNat + i.bits.toNat % 4⟩ = .ok (some v) ∧
          BehaviorV2 (entryProgForBody Captured.program 2) q
            (TerminalOut.returned ⟨v, q.callerMem⟩)
    | _ => False := by
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  let hArgsOrig := hArgs
  let hRefsOrig := hRefs
  cases hList : q.args with
  | nil => rw [hList] at hArgs; cases hArgs
  | cons v0 rest =>
    cases rest with
    | nil =>
      rw [hList] at hArgs
      dsimp only [Captured.body_2, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.ref .shared digestTy) <;> rw [hV0] at hArgs <;> cases hArgs
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hList] at hArgs
        dsimp only [Captured.body_2, checkArgsMatchV2, List.drop, List.take] at hArgs
        cases hV0 : checkValV2 v0 (.ref .shared digestTy) <;>
          cases hV1 : checkValV2 v1 (.int .i8 false) <;>
          rw [hV0, hV1] at hArgs <;> cases hArgs
      | nil =>
        rw [hList] at hArgs hRefs
        dsimp only [Captured.body_2, checkArgsMatchV2, List.drop, List.take] at hArgs
        cases hV0 : checkValV2 v0 (.ref .shared digestTy) with
        | false => rw [hV0] at hArgs; cases hArgs
        | true =>
          cases hV1 : checkValV2 v1 (.int .i8 false) with
          | false => rw [hV0, hV1] at hArgs; cases hArgs
          | true =>
            let ⟨pv, hvp, _⟩ :=
              checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV0
            let ⟨bits, hv1, hWf⟩ := checkValV2_scalar_inv hV1
            subst hvp
            subst hv1
            have hLt : bits.toNat < 256 := by
              unfold ScalarVal.wf at hWf
              have hEq : truncateBits .i8 bits = bits := eq_of_beq hWf
              rw [← hEq, toNat_truncateBits]
              exact Nat.mod_lt _ (by decide)
            have hk : bits.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
            have hk256 : bits.toNat % 4 < 256 := Nat.lt_trans hk (by decide)
            dsimp only [Captured.body_2, refsValidInMemList, refsValidInMem, List.drop,
              List.take] at hRefs
            cases hRP : refValidInMem (entryMemoryWithCaller q.callerMem) .shared digestTy
                (.ptr pv) with
            | error _ => rw [hRP] at hRefs; cases hRefs
            | ok _ =>
              rcases refValidInMem_digest_inv hRP with
                ⟨aid, a, hPId, hFind, hLive, hInB, w, hDec⟩
              have hLe4 : pv.offsetBytes.toNat + 4 ≤ a.bytes.length := le_of_ble_true hInB
              have hInBk : isInBounds a (pv.offsetBytes.toNat + bits.toNat % 4) 1 = true := by
                unfold isInBounds
                rw [Nat.add_assoc]
                exact Nat.ble_eq.mpr (Nat.le_trans (Nat.add_le_add_left hk _) hLe4)
              have hLtk : pv.offsetBytes.toNat + bits.toNat % 4 < a.bytes.length :=
                Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hLe4
              have hOffLtk :
                  Nat.blt (pv.offsetBytes.toNat + bits.toNat % 4) (Nat.pow 2 64) = true :=
                entry_offset_blt_pow64 hCM hFind (Nat.le_of_lt hLtk)
              rcases getElem?_some_of_lt hLtk with ⟨x, hGet⟩
              rcases digest_byte_init hk hGet hDec with ⟨b, prov, hx⟩
              subst hx
              let v : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩
              have hLoad : loadIndirectV2 (entryMemoryWithCaller q.callerMem)
                  (.int .i8 false) ⟨aid, pv.offsetBytes.toNat + bits.toNat % 4⟩ =
                    .ok (some v) := by
                rw [loadIndirectV2_u8 hFind hLive hInBk hGet, decodeValV2_u8_init]
              have hChk : checkValV2 v (.int .i8 false) = true :=
                checkValV2_u8_ofNat_lt b.toBitVec.isLt
              let expectedOut : TerminalOut := .returned ⟨v, q.callerMem⟩
              have hInit : initStateV2 (entryProgForBody Captured.program 2) q =
                  .ok ⟨[⟨2, 0, 0, initLocalsLoop Captured.body_2 q.args 0
                      Captured.body_2.locals, none, none, none⟩],
                    q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
                apply initStateV2_ok_of (p := entryProgForBody Captured.program 2) (q := q)
                  (body := Captured.body_2) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
                  (by decide) (by decide) (by decide) (by decide) (by decide)
                · exact hArgsOrig
                · exact hRefsOrig
                · exact hDisj
              have hLocs : initLocalsLoop Captured.body_2 q.args 0 Captured.body_2.locals =
                  [.immediate none, .immediate (some (.ptr pv)),
                   .immediate (some (.scalar ⟨.i8, false, bits⟩)),
                   .dead, .dead, .dead, .immediate none] := by
                rw [hList]; rfl
              have hExec : execProgV2 (entryProgForBody Captured.program 2) 20 q
                  (fun o => o = expectedOut) := by
                unfold execProgV2
                rw [hInit, hLocs]
                -- bb0 stmt 0..2: storageLive 3, 4, 5
                apply execOutcomeStateV2_step (by rfl)
                apply execOutcomeStateV2_step (by rfl)
                apply execOutcomeStateV2_step (by rfl)
                -- bb0 stmt 3: _5 = copy _2
                apply execOutcomeStateV2_step (by
                  dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                      List.nil_append, entryProgForBody, Captured.program,
                    Captured.body_2, List.append, Trusted.MirSemantics.getElem?,
                    evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                    placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2]
                  rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; decide
                  dsimp only
                  rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)
                -- bb0 stmt 4: _4 = BitAnd(move _5, const 3_u8)
                apply execOutcomeStateV2_step (by
                  dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                      List.nil_append, entryProgForBody, Captured.program,
                    Captured.body_2, List.append, Trusted.MirSemantics.getElem?,
                    evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                    placeStaticTyV2, evalRvalueV2, evalPrimitiveOperandV2,
                    evalOperandToSlotV2]
                  rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; decide
                  dsimp only
                  rw [evalConstLit_u8_three]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; decide
                  dsimp only
                  rw [evalBinOp_bitAnd_three hLt]
                  dsimp only
                  rw [writePlaceDestV2_immediate_ok (checkValV2_u8_ofNat_lt hk256) (by rfl)
                    (by rfl)]; rfl)
                -- bb0 stmt 5: storageDead 5
                apply execOutcomeStateV2_step (by rfl)
                -- bb0 stmt 6: _3 = move _4 as usize
                apply execOutcomeStateV2_step (by
                  dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                      List.nil_append, entryProgForBody, Captured.program,
                    Captured.body_2, List.append, Trusted.MirSemantics.getElem?,
                    evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                    placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2]
                  rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; decide
                  rw [evalIntToIntCast_u8_usize hk256]
                  dsimp only
                  rw [writePlaceDestV2_immediate_ok (checkValV2_usize_ofNat_lt hk256) (by rfl)
                    (by rfl)]; rfl)
                -- bb0 stmt 7: storageDead 4
                apply execOutcomeStateV2_step (by rfl)
                -- bb0 stmt 8: _6 = Lt(copy _3, const 4_usize)
                apply execOutcomeStateV2_step (by
                  dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                      List.nil_append, entryProgForBody, Captured.program,
                    Captured.body_2, List.append, Trusted.MirSemantics.getElem?,
                    evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                    placeStaticTyV2, evalRvalueV2, evalPrimitiveOperandV2,
                    evalOperandToSlotV2]
                  rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; decide
                  dsimp only
                  rw [evalConstLit_usize_four]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; decide
                  dsimp only
                  rw [evalBinOp_lt_four hk]
                  dsimp only
                  rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]; rfl)
                -- bb0 terminator: assert(move _6, true) -> bb1
                apply execOutcomeStateV2_step (by rfl)
                -- bb1 stmt 0: _0 = copy (*_1).0[_3]
                apply execOutcomeStateV2_step (by
                  dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                      List.nil_append, entryProgForBody, Captured.program,
                    Captured.body_2, List.append, Trusted.MirSemantics.getElem?,
                    evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                    consResolvedProjV2, readIndexLocalV2, placeStaticTyV2, evalRvalueV2,
                    evalOperandToSlotV2, readPlaceV2]
                  rw [ite_bool_false]; rotate_left; rfl
                  rw [ite_bool_true]; rotate_left; rfl
                  rw [ite_bool_true]; rotate_left; rfl
                  rw [toNat_ofNat_lt hk256]
                  dsimp only [readDerefProjectedV2]
                  rw [ite_bool_false]; rotate_left; rfl
                  rw [layoutOfTyV2_digest]
                  dsimp only
                  rw [projectMemoryLayoutV2_digest_index hk]
                  dsimp only
                  rw [show layoutOfTyV2 (MirTy.int IntWidth.i8 false) = some ⟨1, 0⟩ from rfl]
                  dsimp only
                  rw [hPId]
                  dsimp only
                  rw [hFind]
                  dsimp only
                  rw [ite_bool_false]; rotate_left
                  · rw [hLive, hInB, isAligned_zero, hOffLtk]; rfl
                  rw [hLoad]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; decide
                  dsimp only
                  rw [writePlaceDestV2_immediate_ok hChk (by rfl) (by rfl)]; rfl)
                -- bb1 stmt 1: storageDead 3
                apply execOutcomeStateV2_step (by rfl)
                -- bb1: return
                apply execOutcomeStateV2_done (by
                  dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                      List.nil_append, entryProgForBody, Captured.program,
                    Captured.body_2, List.append, Trusted.MirSemantics.getElem?]
                  rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
                    (by rfl) (by rfl) (by rfl) (by rfl)]
                  rw [extractCallerMemory_entry q.callerMem hCM]
                  rfl)
                rfl
              have hRes := spec_and_behaviorV2_of_exec_eq hExec
              refine ⟨hRes.1, ?_⟩
              dsimp only
              rw [hPId]
              exact ⟨v, hLoad, hRes.2.1⟩

/-! ## Bodies 3-4: `digests_differ` and the derived `eq` -/

/-! ## Array and Reference Helpers (adapted from `profile_v2_arrays/Proof.lean`) -/

private theorem pb_checkValV2_ref_ptr_inv {reqMut : Mutability} {pt : MirTy}
    {hNonSlice : ∀ elem, pt ≠ .slice elem} {v : Val}
    (h : checkValV2 v (.ref reqMut pt) = true)
    (hNonStr : pt ≠ .str := by intro h; cases h) :
    ∃ p : PtrVal, v = .ptr p ∧ p.width = .isize := by
  cases pt with
  | slice elem => exact absurd rfl (hNonSlice elem)
  | str => exact absurd rfl hNonStr
  | _ =>
    cases v with
    | ptr p =>
      cases p with
      | mk aid off pw =>
        unfold checkValV2 at h
        dsimp only at h
        cases hW : IntWidth.beq pw .isize with
        | false =>
          rw [hW] at h
          cases h
        | true =>
          have hEqW : pw = .isize := by cases pw <;> first | rfl | cases hW
          exact ⟨⟨aid, off, pw⟩, rfl, hEqW⟩
    | bool _ | scalar _ | unit | char _ | ordering _ | tuple _ | enumVal _ _
    | vec _ _ _ | range _ _ | slicePtr _ _ | array _ | rangeTo _ | rangeFrom _ | bytes _ => cases h
    | optionVal o => cases o <;> cases h
    | boxPtr _ o => cases o <;> cases h

private theorem pb_decodeValV2_u8_uninit :
    decodeValV2 profileV2TargetEndian (.int .i8 false) [.uninit] = .ok none := by
  rw [dv2_int]
  unfold decodeVal layoutOfTy
  dsimp only [intLayout]
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  rfl

private theorem pb_decodeValV2_u8_init (b : UInt8) (prov : Option AllocId) :
    decodeValV2 profileV2TargetEndian (.int .i8 false) [.init b prov] =
      .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)) := by
  have hBLt : b.toNat < 256 := b.toBitVec.isLt
  have hTrunc : truncateBits .i8 (BitVec.ofNat 128 b.toNat) = BitVec.ofNat 128 b.toNat := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits, BitVec.toNat_ofNat]
    change (b.toNat % Nat.pow 2 128) % 256 = b.toNat % Nat.pow 2 128
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hBLt (by decide)), Nat.mod_eq_of_lt hBLt]
  rw [dv2_int]
  unfold decodeVal layoutOfTy
  dsimp only [intLayout, initBytes?, decodeUInt]
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  have hDecB : natOfLeBytes [b] = b.toNat := by
    dsimp only [natOfLeBytes]; rw [Nat.mul_zero, Nat.add_zero]
  change (match evalConstLit (.int .i8 false) (.scalar (BitVec.ofNat 128 (natOfLeBytes [b]))) with
    | Except.ok v => Except.ok (some v)
    | Except.error k => Except.error k) = _
  rw [hDecB]
  dsimp only [evalConstLit]
  rw [hTrunc]
  rw [ite_bool_false (bne_self_eq_false _)]

private theorem pb_decodeValV2_u8x4_init (b0 b1 b2 b3 : UInt8)
    (p0 p1 p2 p3 : Option AllocId) :
    decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4)
      [.init b0 p0, .init b1 p1, .init b2 p2, .init b3 p3] =
      .ok (some (.array [
        .scalar ⟨.i8, false, BitVec.ofNat 128 b0.toNat⟩,
        .scalar ⟨.i8, false, BitVec.ofNat 128 b1.toNat⟩,
        .scalar ⟨.i8, false, BitVec.ofNat 128 b2.toNat⟩,
        .scalar ⟨.i8, false, BitVec.ofNat 128 b3.toNat⟩])) := by
  rw [dv2_array]
  dsimp only [lv2_int, lv2_array, lv2_struct, layoutOfArrayV2, layoutOfTy, intLayout]
  rw [ite_bool_false]; rotate_left; rfl
  dsimp only [decodeFixedChunks, List.take, List.drop]
  rw [pb_decodeValV2_u8_init b0 p0, pb_decodeValV2_u8_init b1 p1,
      pb_decodeValV2_u8_init b2 p2, pb_decodeValV2_u8_init b3 p3]
  rfl
private theorem pb_drop_take_four_of_getElem {off : Nat} {bs : List AllocByte}
    {x0 x1 x2 x3 : AllocByte}
    (h0 : Trusted.MirSemantics.getElem? bs off = some x0)
    (h1 : Trusted.MirSemantics.getElem? bs (off + 1) = some x1)
    (h2 : Trusted.MirSemantics.getElem? bs (off + 2) = some x2)
    (h3 : Trusted.MirSemantics.getElem? bs (off + 3) = some x3) :
    (bs.drop off).take 4 = [x0, x1, x2, x3] := by
  induction off generalizing bs with
  | zero =>
    cases bs with
    | nil => cases h0
    | cons a0 r0 =>
      cases h0
      cases r0 with
      | nil => cases h1
      | cons a1 r1 =>
        cases h1
        cases r1 with
        | nil => cases h2
        | cons a2 r2 =>
          cases h2
          cases r2 with
          | nil => cases h3
          | cons a3 _ => cases h3; rfl
  | succ k ih =>
    cases bs with
    | nil => cases h0
    | cons _ tl =>
      exact ih h0 h1 h2 h3

private theorem pb_getElem_four_of_drop_take_four {off : Nat} {bs : List AllocByte}
    {x0 x1 x2 x3 : AllocByte} (hLen : off + 4 ≤ bs.length)
    (hSlice : (bs.drop off).take 4 = [x0, x1, x2, x3]) :
    Trusted.MirSemantics.getElem? bs off = some x0 ∧
    Trusted.MirSemantics.getElem? bs (off + 1) = some x1 ∧
    Trusted.MirSemantics.getElem? bs (off + 2) = some x2 ∧
    Trusted.MirSemantics.getElem? bs (off + 3) = some x3 := by
  induction off generalizing bs with
  | zero =>
    cases bs with
    | nil => cases hLen
    | cons a0 r0 =>
      cases r0 with
      | nil =>
        dsimp only [List.length] at hLen
        exact absurd hLen (by decide)
      | cons a1 r1 =>
        cases r1 with
        | nil =>
          dsimp only [List.length] at hLen
          exact absurd hLen (by decide)
        | cons a2 r2 =>
          cases r2 with
          | nil =>
            dsimp only [List.length] at hLen
            exact absurd hLen (by decide)
          | cons a3 _ =>
            cases hSlice
            exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    cases bs with
    | nil => cases hLen
    | cons _ tl =>
      have hLen' : k + 4 ≤ tl.length :=
        Nat.le_of_succ_le_succ (by rw [Nat.succ_add] at hLen; exact hLen)
      exact ih hLen' hSlice

private theorem pb_decodeValV2_u8x4_init_inv {x0 x1 x2 x3 : AllocByte} {v : Val}
    (h : decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4) [x0, x1, x2, x3] = .ok (some v)) :
    ∃ b0 b1 b2 b3 p0 p1 p2 p3,
      x0 = .init b0 p0 ∧ x1 = .init b1 p1 ∧ x2 = .init b2 p2 ∧ x3 = .init b3 p3 := by
  rw [dv2_array] at h
  dsimp only [lv2_int, lv2_array, lv2_struct, layoutOfArrayV2, layoutOfTy, intLayout] at h
  rw [ite_bool_false] at h; rotate_left; rfl
  dsimp only [decodeFixedChunks, List.take, List.drop] at h
  rw [ite_bool_true] at h; rotate_left; rfl
  cases x0 with
  | uninit =>
    cases x1 <;> cases x2 <;> cases x3 <;>
      simp only [pb_decodeValV2_u8_uninit, pb_decodeValV2_u8_init] at h <;> cases h
  | init b0 p0 =>
    cases x1 with
    | uninit =>
      cases x2 <;> cases x3 <;>
        simp only [pb_decodeValV2_u8_uninit, pb_decodeValV2_u8_init] at h <;> cases h
    | init b1 p1 =>
      cases x2 with
      | uninit =>
        cases x3 <;>
          simp only [pb_decodeValV2_u8_uninit, pb_decodeValV2_u8_init] at h <;> cases h
      | init b2 p2 =>
        cases x3 with
        | uninit =>
          simp only [pb_decodeValV2_u8_uninit, pb_decodeValV2_u8_init] at h; cases h
        | init b3 p3 => exact ⟨b0, b1, b2, b3, p0, p1, p2, p3, rfl, rfl, rfl, rfl⟩

private theorem pb_refValidInMem_u8x4_inv {m : MemoryState} {p : PtrVal}
    (hRef : refValidInMem m .shared (.array (.int .i8 false) 4) (.ptr p) = .ok ()) :
    ∃ (aid : AllocId) (a : Allocation) (b0 b1 b2 b3 : UInt8)
      (p0 p1 p2 p3 : Option AllocId),
      p.allocId = some aid ∧
      findAllocation aid m.allocations = some a ∧
      a.live = true ∧
      isInBounds a p.offsetBytes.toNat 4 = true ∧
      Trusted.MirSemantics.getElem? a.bytes p.offsetBytes.toNat = some (.init b0 p0) ∧
      Trusted.MirSemantics.getElem? a.bytes (p.offsetBytes.toNat + 1) = some (.init b1 p1) ∧
      Trusted.MirSemantics.getElem? a.bytes (p.offsetBytes.toNat + 2) = some (.init b2 p2) ∧
      Trusted.MirSemantics.getElem? a.bytes (p.offsetBytes.toNat + 3) = some (.init b3 p3) := by
  unfold refValidInMem at hRef
  dsimp only at hRef
  rw [ite_bool_false (b := !isSupportedV2PointeeTy (.array (.int .i8 false) 4) &&
      !isHeapHandleTyV2 (.array (.int .i8 false) 4))
    (by decide), (show layoutOfTyV2 (.array (.int .i8 false) 4) = some ⟨4, 0⟩
      from rfl)] at hRef
  dsimp only at hRef
  cases hAid : p.allocId with
  | none =>
    rw [hAid] at hRef
    dsimp only at hRef
    split at hRef
    · cases hRef
    · split at hRef
      · cases hRef
      · cases hRef
  | some aid =>
    rw [hAid] at hRef
    dsimp only at hRef
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at hRef; cases hRef
    | some a =>
      rw [hFind] at hRef
      dsimp only at hRef
      cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat 4 ||
          !isAligned a p.offsetBytes.toNat 0) with
      | true => rw [hBad] at hRef; cases hRef
      | false =>
        rw [hBad] at hRef
        rw [ite_bool_false] at hRef; rotate_left; rfl
        have hLive : a.live = true := by
          cases hL : a.live with
          | true => rfl
          | false => rw [hL] at hBad; cases hBad
        have hInB : isInBounds a p.offsetBytes.toNat 4 = true := by
          cases hI : isInBounds a p.offsetBytes.toNat 4 with
          | true => rfl
          | false => rw [hI] at hBad; cases hL : a.live <;> rw [hL] at hBad <;> cases hBad
        have hLe : p.offsetBytes.toNat + 4 ≤ a.bytes.length := le_of_ble_true hInB
        have hDropLen : ((a.bytes.drop p.offsetBytes.toNat).take 4).length = 4 := by
          have : ∀ (off : Nat) (bs : List AllocByte), off + 4 ≤ bs.length →
              ((bs.drop off).take 4).length = 4 := by
            intro off bs h
            induction off generalizing bs with
            | zero =>
              cases bs with | nil => cases h | cons _ r0 =>
              cases r0 with | nil => dsimp only [List.length] at h; exact absurd h (by decide) | cons _ r1 =>
              cases r1 with | nil => dsimp only [List.length] at h; exact absurd h (by decide) | cons _ r2 =>
              cases r2 with | nil => dsimp only [List.length] at h; exact absurd h (by decide) | cons _ _ => rfl
            | succ k ih =>
              cases bs with | nil => cases h | cons _ tl =>
              exact ih tl (Nat.le_of_succ_le_succ (by rw [Nat.succ_add] at h; exact h))
          exact this p.offsetBytes.toNat a.bytes hLe
        cases hS : (a.bytes.drop p.offsetBytes.toNat).take 4 with
        | nil => rw [hS] at hDropLen; cases hDropLen
        | cons x0 r0 => cases r0 with | nil => rw [hS] at hDropLen; cases hDropLen | cons x1 r1 =>
          cases r1 with | nil => rw [hS] at hDropLen; cases hDropLen | cons x2 r2 =>
          cases r2 with | nil => rw [hS] at hDropLen; cases hDropLen | cons x3 r3 =>
          cases r3 with
          | cons _ _ => rw [hS] at hDropLen; cases hDropLen
          | nil =>
            rw [hS] at hRef
            rcases pb_getElem_four_of_drop_take_four hLe hS with ⟨hg0, hg1, hg2, hg3⟩
            rw [ite_bool_false] at hRef; rotate_left; rfl
            cases hD : decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4) [x0, x1, x2, x3] with
            | error k => rw [hD] at hRef; cases hRef
            | ok ov =>
              cases ov with
              | none => rw [hD] at hRef; cases hRef
              | some v =>
                rcases pb_decodeValV2_u8x4_init_inv hD with ⟨b0, b1, b2, b3, p0, p1, p2, p3, rfl, rfl, rfl, rfl⟩
                exact ⟨aid, a, b0, b1, b2, b3, p0, p1, p2, p3,
                  rfl, hFind, hLive, hInB, hg0, hg1, hg2, hg3⟩

private theorem pb_arrayValEq_u8_byte (x y : UInt8) :
    arrayValEqV2 (.int .i8 false)
      (.scalar ⟨.i8, false, BitVec.ofNat 128 x.toNat⟩)
      (.scalar ⟨.i8, false, BitVec.ofNat 128 y.toNat⟩) = .ok (Nat.beq x.toNat y.toNat) := by
  have hxLt : x.toNat < 256 := x.toBitVec.isLt
  have hyLt : y.toNat < 256 := y.toBitVec.isLt
  have h1 : (truncateBits .i8 (BitVec.ofNat 128 x.toNat)).toNat = x.toNat := by
    rw [toNat_truncateBits, BitVec.toNat_ofNat]
    change (x.toNat % Nat.pow 2 128) % 256 = x.toNat
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hxLt (by decide)), Nat.mod_eq_of_lt hxLt]
  have h2 : (truncateBits .i8 (BitVec.ofNat 128 y.toNat)).toNat = y.toNat := by
    rw [toNat_truncateBits, BitVec.toNat_ofNat]
    change (y.toNat % Nat.pow 2 128) % 256 = y.toNat
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hyLt (by decide)), Nat.mod_eq_of_lt hyLt]
  unfold arrayValEqV2 evalBinOp
  dsimp only [decodeScalar]
  rw [ite_bool_false]; rotate_left; decide
  rw [ite_bool_false]; rotate_left; decide
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  rw [h1, h2]
  have hBool : (Int.ofNat x.toNat == Int.ofNat y.toNat) = Nat.beq x.toNat y.toNat := by
    change (@decide (Int.ofNat x.toNat = Int.ofNat y.toNat) (Int.decEq _ _)) = Nat.beq x.toNat y.toNat
    cases h : Int.decEq (Int.ofNat x.toNat) (Int.ofNat y.toNat) with
    | isTrue hEq =>
      have hNat : x.toNat = y.toNat := Int.ofNat.inj hEq
      change true = Nat.beq x.toNat y.toNat
      rw [hNat, Nat.beq_refl]
    | isFalse hNe =>
      cases h2 : Nat.beq x.toNat y.toNat with
      | false => rfl
      | true => exact False.elim (hNe (congrArg Int.ofNat (Nat.eq_of_beq_eq_true h2)))
  rw [hBool]

/-! ## `Digest` Helpers for Bodies 3 and 4 -/

private abbrev pb_digestTy : MirTy :=
  .struct_ (StructLayout.mk 1530084049 4 0 [0]) [.array (.int .i8 false) 4]

private theorem pb_layoutOfTyV2_digest : layoutOfTyV2 pb_digestTy = some ⟨4, 0⟩ := by rfl

private theorem pb_bodyCallAdmitted_4 : bodyCallAdmittedV2 Captured.body_4 = true := by decide

private theorem pb_decodeValV2_digest (x0 x1 x2 x3 : AllocByte) :
    decodeValV2 profileV2TargetEndian pb_digestTy [x0, x1, x2, x3] =
      (match decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4) [x0, x1, x2, x3] with
       | .ok (some v) => .ok (some (.tuple [v]))
       | .ok none => .ok none
       | .error k => .error k) := by
  generalize hD : decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4) [x0, x1, x2, x3] = d
  rw [dv2_struct]
  rw [pb_layoutOfTyV2_digest]
  dsimp only
  rw [ite_bool_false]; rotate_left; rfl
  dsimp only [dsf_cons, dsf_nil, List.drop]
  rw [show layoutOfTyV2 (.array (.int .i8 false) 4) = some ⟨4, 0⟩ from rfl]
  dsimp only [List.take]
  rw [hD]
  cases d with
  | error k => rfl
  | ok o => cases o <;> rfl

private theorem pb_refValidInMem_digest_inv {m : MemoryState} {p : PtrVal}
    (hRef : refValidInMem m .shared pb_digestTy (.ptr p) = .ok ()) :
    ∃ (aid : AllocId) (a : Allocation) (b0 b1 b2 b3 : UInt8)
      (p0 p1 p2 p3 : Option AllocId),
      p.allocId = some aid ∧
      findAllocation aid m.allocations = some a ∧
      a.live = true ∧
      isInBounds a p.offsetBytes.toNat 4 = true ∧
      Trusted.MirSemantics.getElem? a.bytes p.offsetBytes.toNat = some (.init b0 p0) ∧
      Trusted.MirSemantics.getElem? a.bytes (p.offsetBytes.toNat + 1) = some (.init b1 p1) ∧
      Trusted.MirSemantics.getElem? a.bytes (p.offsetBytes.toNat + 2) = some (.init b2 p2) ∧
      Trusted.MirSemantics.getElem? a.bytes (p.offsetBytes.toNat + 3) = some (.init b3 p3) := by
  unfold refValidInMem at hRef
  dsimp only at hRef
  rw [ite_bool_false (b := !isSupportedV2PointeeTy pb_digestTy &&
      !isHeapHandleTyV2 pb_digestTy) (by decide)] at hRef
  rw [pb_layoutOfTyV2_digest] at hRef
  dsimp only at hRef
  cases hAid : p.allocId with
  | none =>
    rw [hAid] at hRef
    dsimp only at hRef
    split at hRef
    · cases hRef
    · split at hRef
      · cases hRef
      · cases hRef
  | some aid =>
    rw [hAid] at hRef
    dsimp only at hRef
    cases hFind : findAllocation aid m.allocations with
    | none => rw [hFind] at hRef; cases hRef
    | some a =>
      rw [hFind] at hRef
      dsimp only at hRef
      cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat 4 ||
          !isAligned a p.offsetBytes.toNat 0) with
      | true => rw [hBad] at hRef; cases hRef
      | false =>
        rw [hBad] at hRef
        rw [ite_bool_false] at hRef; rotate_left; rfl
        have hLive : a.live = true := by
          cases hL : a.live with
          | true => rfl
          | false => rw [hL] at hBad; cases hBad
        have hInB : isInBounds a p.offsetBytes.toNat 4 = true := by
          cases hI : isInBounds a p.offsetBytes.toNat 4 with
          | true => rfl
          | false => rw [hI] at hBad; cases hL : a.live <;> rw [hL] at hBad <;> cases hBad
        have hLe : p.offsetBytes.toNat + 4 ≤ a.bytes.length := le_of_ble_true hInB
        have hDropLen : ((a.bytes.drop p.offsetBytes.toNat).take 4).length = 4 := by
          have : ∀ (off : Nat) (bs : List AllocByte), off + 4 ≤ bs.length →
              ((bs.drop off).take 4).length = 4 := by
            intro off bs h
            induction off generalizing bs with
            | zero =>
              cases bs with | nil => cases h | cons _ r0 =>
              cases r0 with | nil => dsimp only [List.length] at h; exact absurd h (by decide) | cons _ r1 =>
              cases r1 with | nil => dsimp only [List.length] at h; exact absurd h (by decide) | cons _ r2 =>
              cases r2 with | nil => dsimp only [List.length] at h; exact absurd h (by decide) | cons _ _ => rfl
            | succ k ih =>
              cases bs with | nil => cases h | cons _ tl =>
              exact ih tl (Nat.le_of_succ_le_succ (by rw [Nat.succ_add] at h; exact h))
          exact this p.offsetBytes.toNat a.bytes hLe
        cases hS : (a.bytes.drop p.offsetBytes.toNat).take 4 with
        | nil => rw [hS] at hDropLen; cases hDropLen
        | cons x0 r0 => cases r0 with | nil => rw [hS] at hDropLen; cases hDropLen | cons x1 r1 =>
          cases r1 with | nil => rw [hS] at hDropLen; cases hDropLen | cons x2 r2 =>
          cases r2 with | nil => rw [hS] at hDropLen; cases hDropLen | cons x3 r3 =>
          cases r3 with
          | cons _ _ => rw [hS] at hDropLen; cases hDropLen
          | nil =>
            rw [hS] at hRef
            rcases pb_getElem_four_of_drop_take_four hLe hS with ⟨hg0, hg1, hg2, hg3⟩
            rw [ite_bool_false] at hRef; rotate_left; rfl
            rw [pb_decodeValV2_digest] at hRef
            cases hD : decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4) [x0, x1, x2, x3] with
            | error k => rw [hD] at hRef; cases hRef
            | ok ov =>
              cases ov with
              | none => rw [hD] at hRef; cases hRef
              | some v =>
                rcases pb_decodeValV2_u8x4_init_inv hD with ⟨b0, b1, b2, b3, p0, p1, p2, p3, rfl, rfl, rfl, rfl⟩
                exact ⟨aid, a, b0, b1, b2, b3, p0, p1, p2, p3,
                  rfl, hFind, hLive, hInB, hg0, hg1, hg2, hg3⟩

private abbrev pb_arr (b0 b1 b2 b3 : UInt8) : List Val :=
  [.scalar ⟨.i8, false, BitVec.ofNat 128 b0.toNat⟩,
   .scalar ⟨.i8, false, BitVec.ofNat 128 b1.toNat⟩,
   .scalar ⟨.i8, false, BitVec.ofNat 128 b2.toNat⟩,
   .scalar ⟨.i8, false, BitVec.ofNat 128 b3.toNat⟩]

private theorem pb_isAligned_zero (a : Allocation) (off : Nat) : isAligned a off 0 = true := by
  unfold isAligned
  change (Nat.ble 0 a.alignLog2 && Nat.beq (off % 1) 0) = true
  rw [Nat.mod_one, Nat.beq_refl, Nat.ble_eq.mpr (Nat.zero_le _)]
  rfl

private theorem pb_refValid_arr_of {m : MemoryState} {p : PtrVal} {aid : AllocId}
    {a : Allocation} {off : Nat} {b0 b1 b2 b3 : UInt8} {p0 p1 p2 p3 : Option AllocId}
    (hId : p.allocId = some aid) (hOff : p.offsetBytes.toNat = off)
    (hFind : findAllocation aid m.allocations = some a) (hLive : a.live = true)
    (hInB : isInBounds a off 4 = true)
    (hg0 : Trusted.MirSemantics.getElem? a.bytes off = some (.init b0 p0))
    (hg1 : Trusted.MirSemantics.getElem? a.bytes (off + 1) = some (.init b1 p1))
    (hg2 : Trusted.MirSemantics.getElem? a.bytes (off + 2) = some (.init b2 p2))
    (hg3 : Trusted.MirSemantics.getElem? a.bytes (off + 3) = some (.init b3 p3)) :
    refValidInMem m .shared (.array (.int .i8 false) 4) (.ptr p) = .ok () := by
  unfold refValidInMem
  dsimp only
  rw [ite_bool_false (b := !isSupportedV2PointeeTy (.array (.int .i8 false) 4) &&
      !isHeapHandleTyV2 (.array (.int .i8 false) 4))
    (by decide), (show layoutOfTyV2 (.array (.int .i8 false) 4) = some ⟨4, 0⟩
      from rfl)]
  dsimp only
  rw [hId]; dsimp only
  rw [hFind]; dsimp only
  rw [hOff]
  rw [ite_bool_false]; rotate_left; (rw [hLive, hInB, pb_isAligned_zero]; rfl)
  rw [ite_bool_false]; rotate_left; rfl
  rw [pb_drop_take_four_of_getElem hg0 hg1 hg2 hg3]
  rw [pb_decodeValV2_u8x4_init b0 b1 b2 b3 p0 p1 p2 p3]

private theorem pb_loadIndirect_arr_of {m : MemoryState} {aid : AllocId}
    {a : Allocation} {off : Nat} {b0 b1 b2 b3 : UInt8} {p0 p1 p2 p3 : Option AllocId}
    (hFind : findAllocation aid m.allocations = some a) (hLive : a.live = true)
    (hInB : isInBounds a off 4 = true)
    (hg0 : Trusted.MirSemantics.getElem? a.bytes off = some (.init b0 p0))
    (hg1 : Trusted.MirSemantics.getElem? a.bytes (off + 1) = some (.init b1 p1))
    (hg2 : Trusted.MirSemantics.getElem? a.bytes (off + 2) = some (.init b2 p2))
    (hg3 : Trusted.MirSemantics.getElem? a.bytes (off + 3) = some (.init b3 p3)) :
    loadIndirectV2 m (.array (.int .i8 false) 4) ⟨aid, off⟩ =
      .ok (some (.array (pb_arr b0 b1 b2 b3))) := by
  unfold loadIndirectV2
  dsimp only [lv2_int, lv2_array, lv2_struct, layoutOfArrayV2, layoutOfTy, intLayout]
  unfold readBytes
  rw [hFind]; dsimp only
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; (rw [hLive, hInB, pb_isAligned_zero]; rfl)
  rw [pb_drop_take_four_of_getElem hg0 hg1 hg2 hg3]
  exact pb_decodeValV2_u8x4_init b0 b1 b2 b3 p0 p1 p2 p3

private theorem pb_valEq_ok (b0 b1 b2 b3 c0 c1 c2 c3 : UInt8) :
    ∃ r : Bool, valEqListWith (arrayValEqV2 (.int .i8 false))
      (pb_arr b0 b1 b2 b3) (pb_arr c0 c1 c2 c3) = .ok r := by
  dsimp only [pb_arr, valEqListWith]
  rw [pb_arrayValEq_u8_byte b0 c0, pb_arrayValEq_u8_byte b1 c1,
    pb_arrayValEq_u8_byte b2 c2, pb_arrayValEq_u8_byte b3 c3]
  cases Nat.beq b0.toNat c0.toNat <;> cases Nat.beq b1.toNat c1.toNat <;>
    cases Nat.beq b2.toNat c2.toNat <;> cases Nat.beq b3.toNat c3.toNat <;> exact ⟨_, rfl⟩

private theorem pb_ofNat_toNat_add_zero (o : UInt64) :
    (UInt64.ofNat (o.toNat + 0)).toNat = o.toNat := by
  rw [Nat.add_zero]
  cases o with
  | ofBitVec bv =>
    change (BitVec.ofNat 64 bv.toNat).toNat = bv.toNat
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt bv.isLt

private abbrev pb_refDigestTy : MirTy := .ref .shared pb_digestTy

private theorem pb_digest_args_inv {body : Body} {q : Query}
    (hParams : (body.locals.drop 1).take body.argumentCount = [pb_refDigestTy, pb_refDigestTy])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ (pa pb : PtrVal) (aa ab : AllocId) (allocA allocB : Allocation)
      (b0 b1 b2 b3 c0 c1 c2 c3 : UInt8) (p0 p1 p2 p3 r0 r1 r2 r3 : Option AllocId),
      q.args = [.ptr pa, .ptr pb] ∧
      checkValV2 (.ptr pa) pb_refDigestTy = true ∧
      checkValV2 (.ptr pb) pb_refDigestTy = true ∧
      refValidInMem (entryMemoryWithCaller q.callerMem) .shared pb_digestTy (.ptr pa) = .ok () ∧
      refValidInMem (entryMemoryWithCaller q.callerMem) .shared pb_digestTy (.ptr pb) = .ok () ∧
      pa.allocId = some aa ∧
      findAllocation aa (entryMemoryWithCaller q.callerMem).allocations = some allocA ∧
      allocA.live = true ∧
      isInBounds allocA pa.offsetBytes.toNat 4 = true ∧
      Trusted.MirSemantics.getElem? allocA.bytes pa.offsetBytes.toNat = some (.init b0 p0) ∧
      Trusted.MirSemantics.getElem? allocA.bytes (pa.offsetBytes.toNat + 1) = some (.init b1 p1) ∧
      Trusted.MirSemantics.getElem? allocA.bytes (pa.offsetBytes.toNat + 2) = some (.init b2 p2) ∧
      Trusted.MirSemantics.getElem? allocA.bytes (pa.offsetBytes.toNat + 3) = some (.init b3 p3) ∧
      pb.allocId = some ab ∧
      findAllocation ab (entryMemoryWithCaller q.callerMem).allocations = some allocB ∧
      allocB.live = true ∧
      isInBounds allocB pb.offsetBytes.toNat 4 = true ∧
      Trusted.MirSemantics.getElem? allocB.bytes pb.offsetBytes.toNat = some (.init c0 r0) ∧
      Trusted.MirSemantics.getElem? allocB.bytes (pb.offsetBytes.toNat + 1) = some (.init c1 r1) ∧
      Trusted.MirSemantics.getElem? allocB.bytes (pb.offsetBytes.toNat + 2) = some (.init c2 r2) ∧
      Trusted.MirSemantics.getElem? allocB.bytes (pb.offsetBytes.toNat + 3) = some (.init c3 r3) := by
  let ⟨_, hArgs, hRefs, _⟩ := hValid
  change checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true at hArgs
  change refsValidInMemList (entryMemoryWithCaller q.callerMem)
    ((body.locals.drop 1).take body.argumentCount) q.args = true at hRefs
  rw [hParams] at hArgs hRefs
  cases hList : q.args with
  | nil => rw [hList] at hArgs; cases hArgs
  | cons v0 rest =>
    cases rest with
    | nil =>
      rw [hList] at hArgs
      dsimp only [checkArgsMatchV2] at hArgs
      cases hV0 : checkValV2 v0 pb_refDigestTy <;> rw [hV0] at hArgs <;> cases hArgs
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hList] at hArgs
        dsimp only [checkArgsMatchV2] at hArgs
        cases hV0 : checkValV2 v0 pb_refDigestTy <;> rw [hV0] at hArgs
        · cases hArgs
        · cases hV1 : checkValV2 v1 pb_refDigestTy <;> rw [hV1] at hArgs <;> cases hArgs
      | nil =>
        rw [hList] at hArgs hRefs
        dsimp only [checkArgsMatchV2] at hArgs
        cases hV0 : checkValV2 v0 pb_refDigestTy with
        | false => rw [hV0] at hArgs; cases hArgs
        | true =>
          rw [hV0] at hArgs
          cases hV1 : checkValV2 v1 pb_refDigestTy with
          | false => rw [hV1] at hArgs; cases hArgs
          | true =>
            let ⟨pa, hva, _⟩ := pb_checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV0
            let ⟨pb, hvb, _⟩ := pb_checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV1
            subst hva; subst hvb
            dsimp only [refsValidInMemList, refsValidInMem] at hRefs
            cases hRA : refValidInMem (entryMemoryWithCaller q.callerMem) .shared pb_digestTy (.ptr pa) with
            | error _ => rw [hRA] at hRefs; cases hRefs
            | ok _ =>
              rw [hRA] at hRefs
              cases hRB : refValidInMem (entryMemoryWithCaller q.callerMem) .shared pb_digestTy (.ptr pb) with
              | error _ => rw [hRB] at hRefs; cases hRefs
              | ok _ =>
                rcases pb_refValidInMem_digest_inv hRA with
                  ⟨aa, allocA, b0, b1, b2, b3, p0, p1, p2, p3, hPaId, hFindA, hLiveA, hInBA,
                    hga0, hga1, hga2, hga3⟩
                rcases pb_refValidInMem_digest_inv hRB with
                  ⟨ab, allocB, c0, c1, c2, c3, r0, r1, r2, r3, hPbId, hFindB, hLiveB, hInBB,
                    hgb0, hgb1, hgb2, hgb3⟩
                exact ⟨pa, pb, aa, ab, allocA, allocB, b0, b1, b2, b3, c0, c1, c2, c3,
                  p0, p1, p2, p3, r0, r1, r2, r3, rfl, hV0, hV1, hRA, hRB,
                  hPaId, hFindA, hLiveA, hInBA, hga0, hga1, hga2, hga3,
                  hPbId, hFindB, hLiveB, hInBB, hgb0, hgb1, hgb2, hgb3⟩

private theorem pb_evalCallV2_ok {p : Program} {body calleeBody : Body} {frame : FrameState}
    {callers : List FrameState} {mem mem1 : MemoryState} {cm : CallerMemory}
    {callee : DefId} {args : List Operand} {dst : Place} {t : BasicBlockId}
    {dstTy retTy : MirTy} {typedArgs : List (MirTy × Val)} {vals : List Val}
    {locals1 calleeLocals : List LocalSlot}
    (hDst : Trusted.MirSemantics.getElem? body.locals dst.localId = some dstTy)
    (hCallee : Trusted.MirSemantics.getElem? p.bodies callee = some calleeBody)
    (hAdm : bodyCallAdmittedV2 calleeBody = true)
    (hRet : Trusted.MirSemantics.getElem? calleeBody.locals 0 = some retTy)
    (hBeq : MirTy.beq retTy dstTy = true)
    (hEval : evalArgOperandsV2 body.locals frame.locals mem args = .ok (typedArgs, locals1, mem1))
    (hVals : argValues typedArgs = vals)
    (hTyped : typedArgsMatchV2 typedArgs
      ((calleeBody.locals.drop 1).take calleeBody.argumentCount) = true)
    (hChk : checkArgsMatchV2 vals ((calleeBody.locals.drop 1).take calleeBody.argumentCount) = true)
    (hRefs : refsValidInMemList mem1
      ((calleeBody.locals.drop 1).take calleeBody.argumentCount) vals = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((calleeBody.locals.drop 1).take calleeBody.argumentCount) vals) = true)
    (hLocs : initLocalsLoop calleeBody vals 0 calleeBody.locals = calleeLocals)
    {u : UnwindAction} {v : Option Val}
    (hU : (match u with | .cleanup _ => false | _ => true) = true)
    (hMv : moveDefinitelyDisjoint args dst = true)
    (hLive : Trusted.MirSemantics.getElem? locals1 dst.localId = some (.immediate v)) :
    evalCallV2 p body frame callers mem cm callee args dst (some t) u =
      .step {
        frames := { defId := callee, blockIdx := 0, stmtIdx := 0, locals := calleeLocals,
                    retDst? := some dst, retTarget? := some t } ::
          { frame with locals := locals1 } :: callers
        callerMem := cm
        mem := mem1 } := by
  unfold evalCallV2
  cases u
  case cleanup b => exact absurd hU Bool.false_ne_true
  all_goals
    dsimp only
    rw [ite_bool_false (by rw [hMv]; rfl)]
    rw [hDst, hCallee]
    dsimp only
    rw [ite_bool_false (by rw [hAdm]; rfl), hRet]
    dsimp only
    rw [ite_bool_false (by rw [hBeq]; rfl), hEval]
    dsimp only
    rw [hLive]
    dsimp only
    rw [hVals, ite_bool_false (by rw [hTyped, hChk]; rfl),
      ite_bool_false (by rw [hRefs, hDisj]; rfl), hLocs]

/-! ## Body 4: `<Digest as PartialEq>::eq` -/

private theorem digest_eq_correct (q : Query) (hValid : ValidEntryArgsV2 Captured.body_4 q) :
    WellFormedV2 (entryProgForBody Captured.program 4) q ∧
    match q.args with
    | [.ptr pa, .ptr pb] =>
      match pa.allocId, pb.allocId with
      | some aa, some ab =>
        ∃ a b : List Val,
          loadIndirectV2 (entryMemoryWithCaller q.callerMem)
            (.array (.int .i8 false) 4) ⟨aa, pa.offsetBytes.toNat⟩ =
              .ok (some (.array a)) ∧
          loadIndirectV2 (entryMemoryWithCaller q.callerMem)
            (.array (.int .i8 false) 4) ⟨ab, pb.offsetBytes.toNat⟩ =
              .ok (some (.array b)) ∧
          BehaviorV2 (entryProgForBody Captured.program 4) q
            (TerminalOut.returned ⟨.bool (Spec.arrayBytesEq a b), q.callerMem⟩)
      | _, _ => False
    | _ => False := by
  rcases pb_digest_args_inv (body := Captured.body_4) rfl hValid with
    ⟨pa, pb, aa, ab, allocA, allocB, b0, b1, b2, b3, c0, c1, c2, c3,
      p0, p1, p2, p3, r0, r1, r2, r3, hList, hV0, hV1, hRA, hRB,
      hPaId, hFindA, hLiveA, hInBA, hga0, hga1, hga2, hga3,
      hPbId, hFindB, hLiveB, hInBB, hgb0, hgb1, hgb2, hgb3⟩
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  have hLoadA := pb_loadIndirect_arr_of hFindA hLiveA hInBA hga0 hga1 hga2 hga3
  have hLoadB := pb_loadIndirect_arr_of hFindB hLiveB hInBB hgb0 hgb1 hgb2 hgb3
  rcases pb_valEq_ok b0 b1 b2 b3 c0 c1 c2 c3 with ⟨res, hRes⟩
  have hEqSpec : Spec.arrayBytesEq (pb_arr b0 b1 b2 b3) (pb_arr c0 c1 c2 c3) = res := by
    unfold Spec.arrayBytesEq
    rw [hRes]
  let expectedOut : TerminalOut := .returned ⟨.bool res, q.callerMem⟩
  have hInit : initStateV2 (entryProgForBody Captured.program 4) q =
      .ok ⟨[⟨4, 0, 0, initLocalsLoop Captured.body_4 q.args 0 Captured.body_4.locals, none, none, none⟩],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    apply initStateV2_ok_of (p := entryProgForBody Captured.program 4) (q := q)
      (body := Captured.body_4) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hArgs
    · exact hRefs
    · exact hDisj
  have hLocs : initLocalsLoop Captured.body_4 q.args 0 Captured.body_4.locals =
      [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)), .dead, .dead] := by
    rw [hList]; rfl
  have hExec : execProgV2 (entryProgForBody Captured.program 4) 20 q (fun o => o = expectedOut) := by
    unfold execProgV2
    rw [hInit, hLocs]
    -- bb0 stmt 0: storageLive 3
    apply execOutcomeStateV2_step (by rfl)
    -- bb0 stmt 1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2,
        placeAddrV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [pb_layoutOfTyV2_digest]
      rw [show projectMemoryLayoutV2 pb_digestTy [.field 0 (.array (.int .i8 false) 4)] =
        .ok (.array (.int .i8 false) 4, 0) from rfl]
      dsimp only
      rw [hPaId]; dsimp only
      rw [hFindA]; dsimp only
      rw [ite_bool_false]; rotate_left; (rw [hLiveA, hInBA, pb_isAligned_zero]; rfl)
      dsimp only
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [pb_refValid_arr_of
        (p := { allocId := some aa, offsetBytes := UInt64.ofNat (pa.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindA hLiveA hInBA hga0 hga1 hga2 hga3]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]; rfl)
    -- bb0 stmt 2: storageLive 4
    apply execOutcomeStateV2_step (by rfl)
    -- bb0 stmt 3
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2,
        placeAddrV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [pb_layoutOfTyV2_digest]
      rw [show projectMemoryLayoutV2 pb_digestTy [.field 0 (.array (.int .i8 false) 4)] =
        .ok (.array (.int .i8 false) 4, 0) from rfl]
      dsimp only
      rw [hPbId]; dsimp only
      rw [hFindB]; dsimp only
      rw [ite_bool_false]; rotate_left; (rw [hLiveB, hInBB, pb_isAligned_zero]; rfl)
      dsimp only
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [pb_refValid_arr_of
        (p := { allocId := some ab, offsetBytes := UInt64.ofNat (pb.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindB hLiveB hInBB hgb0 hgb1 hgb2 hgb3]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]; rfl)
    -- bb0 terminator: coreCall arrayEq
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        List.append, Trusted.MirSemantics.getElem?]
      rw [ite_bool_true]; rotate_left; decide
      dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
      dsimp only [argValues, execCoreCallOpWithMem, execAllocCoreCall, execCoreCallWithMem,
        execCoreCallOp]
      rw [ite_bool_false]; rotate_left; decide
      rw [pb_refValid_arr_of
        (p := { allocId := some aa, offsetBytes := UInt64.ofNat (pa.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindA hLiveA hInBA hga0 hga1 hga2 hga3]
      rw [pb_refValid_arr_of
        (p := { allocId := some ab, offsetBytes := UInt64.ofNat (pb.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindB hLiveB hInBB hgb0 hgb1 hgb2 hgb3]
      dsimp only
      rw [pb_ofNat_toNat_add_zero, pb_ofNat_toNat_add_zero, hLoadA, hLoadB]
      dsimp only
      rw [hRes]
      dsimp only
      rw [writePlaceV2_immediate_ok (by rfl) (by rfl) (by rfl)]
      rfl)
    -- bb1: storageDead 4, storageDead 3
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    -- bb1: return
    apply execOutcomeStateV2_done (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        List.append, Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rw [ite_bool_true]; rotate_left; rfl)
    rfl
  have hRes4 := spec_and_behaviorV2_of_exec_eq hExec
  refine ⟨hRes4.1, ?_⟩
  rw [hList]
  dsimp only
  rw [hPaId, hPbId]
  dsimp only
  refine ⟨pb_arr b0 b1 b2 b3, pb_arr c0 c1 c2 c3, hLoadA, hLoadB, ?_⟩
  rw [hEqSpec]
  exact hRes4.2.1

/-! ## Body 3: `digests_differ` (`*a != *b`, a `callNe` into body 4) -/

private theorem digests_differ_correct (q : Query) (hValid : ValidEntryArgsV2 Captured.body_3 q) :
    WellFormedV2 (entryProgForBody Captured.program 3) q ∧
    match q.args with
    | [.ptr pa, .ptr pb] =>
      match pa.allocId, pb.allocId with
      | some aa, some ab =>
        ∃ a b : List Val,
          loadIndirectV2 (entryMemoryWithCaller q.callerMem)
            (.array (.int .i8 false) 4) ⟨aa, pa.offsetBytes.toNat⟩ =
              .ok (some (.array a)) ∧
          loadIndirectV2 (entryMemoryWithCaller q.callerMem)
            (.array (.int .i8 false) 4) ⟨ab, pb.offsetBytes.toNat⟩ =
              .ok (some (.array b)) ∧
          BehaviorV2 (entryProgForBody Captured.program 3) q
            (TerminalOut.returned ⟨.bool (!(Spec.arrayBytesEq a b)), q.callerMem⟩)
      | _, _ => False
    | _ => False := by
  rcases pb_digest_args_inv (body := Captured.body_3) rfl hValid with
    ⟨pa, pb, aa, ab, allocA, allocB, b0, b1, b2, b3, c0, c1, c2, c3,
      p0, p1, p2, p3, r0, r1, r2, r3, hList, hV0, hV1, hRA, hRB,
      hPaId, hFindA, hLiveA, hInBA, hga0, hga1, hga2, hga3,
      hPbId, hFindB, hLiveB, hInBB, hgb0, hgb1, hgb2, hgb3⟩
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  have hLoadA := pb_loadIndirect_arr_of hFindA hLiveA hInBA hga0 hga1 hga2 hga3
  have hLoadB := pb_loadIndirect_arr_of hFindB hLiveB hInBB hgb0 hgb1 hgb2 hgb3
  rcases pb_valEq_ok b0 b1 b2 b3 c0 c1 c2 c3 with ⟨res, hRes⟩
  have hEqSpec : Spec.arrayBytesEq (pb_arr b0 b1 b2 b3) (pb_arr c0 c1 c2 c3) = res := by
    unfold Spec.arrayBytesEq
    rw [hRes]
  let expectedOut : TerminalOut := .returned ⟨.bool (!res), q.callerMem⟩
  have hInit : initStateV2 (entryProgForBody Captured.program 3) q =
      .ok ⟨[⟨3, 0, 0, initLocalsLoop Captured.body_3 q.args 0 Captured.body_3.locals, none, none, none⟩],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    apply initStateV2_ok_of (p := entryProgForBody Captured.program 3) (q := q)
      (body := Captured.body_3) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hArgs
    · exact hRefs
    · exact hDisj
  have hLocs : initLocalsLoop Captured.body_3 q.args 0 Captured.body_3.locals =
      [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)), .dead, .dead] := by
    rw [hList]; rfl
  have hLocs4 : initLocalsLoop Captured.body_4 [.ptr pa, .ptr pb] 0 Captured.body_4.locals =
      [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)), .dead, .dead] := by
    rfl
  have hChk : checkArgsMatchV2 [.ptr pa, .ptr pb]
      (List.take Captured.body_4.argumentCount (List.drop 1 Captured.body_4.locals)) = true := by
    rw [hList] at hArgs; exact hArgs
  have hRefsC : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      (List.take Captured.body_4.argumentCount (List.drop 1 Captured.body_4.locals))
      [.ptr pa, .ptr pb] = true := by
    rw [hList] at hRefs; exact hRefs
  have hDisjC : spansPairwiseDisjoint (refAccessSpansList
      (List.take Captured.body_4.argumentCount (List.drop 1 Captured.body_4.locals))
      [.ptr pa, .ptr pb]) = true := by
    rw [hList] at hDisj; exact hDisj
  have hTyped : typedArgsMatchV2 [(pb_refDigestTy, .ptr pa), (pb_refDigestTy, .ptr pb)]
      (List.take Captured.body_4.argumentCount (List.drop 1 Captured.body_4.locals)) = true := by
    rfl
  have hEvalArgs : evalArgOperandsV2 Captured.body_3.locals
      [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)),
        .immediate (some (.ptr pa)), .immediate (some (.ptr pb))]
      (entryMemoryWithCaller q.callerMem)
      [.move ⟨3, []⟩, .move ⟨4, []⟩] =
      .ok ([(pb_refDigestTy, .ptr pa), (pb_refDigestTy, .ptr pb)],
        [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)),
          liveUninitSlot pb_refDigestTy, liveUninitSlot pb_refDigestTy],
        entryMemoryWithCaller q.callerMem) := by
    dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
    dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
  have hExec : execProgV2 (entryProgForBody Captured.program 3) 30 q (fun o => o = expectedOut) := by
    unfold execProgV2
    rw [hInit, hLocs]
    -- bb0 stmt 0: storageLive 3
    apply execOutcomeStateV2_step (by rfl)
    -- bb0 stmt 1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_3,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [hRA]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
    -- bb0 stmt 2: storageLive 4
    apply execOutcomeStateV2_step (by rfl)
    -- bb0 stmt 3
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_3,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [hRB]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)
    -- bb0 terminator: callNe 4 [move _3, move _4] -> _0, bb1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_3,
        List.append, Trusted.MirSemantics.getElem?]
      rw [ite_bool_true]; rotate_left; decide
      rw [pb_evalCallV2_ok (calleeBody := Captured.body_4) rfl rfl pb_bodyCallAdmitted_4 rfl
        rfl hEvalArgs rfl hTyped hChk hRefsC hDisjC hLocs4 rfl rfl rfl])
    -- callee bb0 stmt 0: storageLive 3
    apply execOutcomeStateV2_step (by rfl)
    -- callee bb0 stmt 1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2,
        placeAddrV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [pb_layoutOfTyV2_digest]
      rw [show projectMemoryLayoutV2 pb_digestTy [.field 0 (.array (.int .i8 false) 4)] =
        .ok (.array (.int .i8 false) 4, 0) from rfl]
      dsimp only
      rw [hPaId]; dsimp only
      rw [hFindA]; dsimp only
      rw [ite_bool_false]; rotate_left; (rw [hLiveA, hInBA, pb_isAligned_zero]; rfl)
      dsimp only
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [pb_refValid_arr_of
        (p := { allocId := some aa, offsetBytes := UInt64.ofNat (pa.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindA hLiveA hInBA hga0 hga1 hga2 hga3]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]; rfl)
    -- callee bb0 stmt 2: storageLive 4
    apply execOutcomeStateV2_step (by rfl)
    -- callee bb0 stmt 3
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2,
        placeAddrV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [pb_layoutOfTyV2_digest]
      rw [show projectMemoryLayoutV2 pb_digestTy [.field 0 (.array (.int .i8 false) 4)] =
        .ok (.array (.int .i8 false) 4, 0) from rfl]
      dsimp only
      rw [hPbId]; dsimp only
      rw [hFindB]; dsimp only
      rw [ite_bool_false]; rotate_left; (rw [hLiveB, hInBB, pb_isAligned_zero]; rfl)
      dsimp only
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [pb_refValid_arr_of
        (p := { allocId := some ab, offsetBytes := UInt64.ofNat (pb.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindB hLiveB hInBB hgb0 hgb1 hgb2 hgb3]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]; rfl)
    -- callee bb0 terminator: coreCall arrayEq
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        List.append, Trusted.MirSemantics.getElem?]
      rw [ite_bool_true]; rotate_left; decide
      dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
      dsimp only [argValues, execCoreCallOpWithMem, execAllocCoreCall, execCoreCallWithMem,
        execCoreCallOp]
      rw [ite_bool_false]; rotate_left; decide
      rw [pb_refValid_arr_of
        (p := { allocId := some aa, offsetBytes := UInt64.ofNat (pa.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindA hLiveA hInBA hga0 hga1 hga2 hga3]
      rw [pb_refValid_arr_of
        (p := { allocId := some ab, offsetBytes := UInt64.ofNat (pb.offsetBytes.toNat + 0) })
        rfl (pb_ofNat_toNat_add_zero _) hFindB hLiveB hInBB hgb0 hgb1 hgb2 hgb3]
      dsimp only
      rw [pb_ofNat_toNat_add_zero, pb_ofNat_toNat_add_zero, hLoadA, hLoadB]
      dsimp only
      rw [hRes]
      dsimp only
      rw [writePlaceV2_immediate_ok (by rfl) (by rfl) (by rfl)]
      rfl)
    -- callee bb1: storageDead 4, storageDead 3
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    -- callee bb1: return to caller (writes `!res` into the caller's `_0`)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_4,
        Captured.body_3, List.append, Trusted.MirSemantics.getElem?, evalReturnToCallerV2,
        deallocateFrameLocalsV2, deallocateLocal]
      rfl)
    -- bb1: storageDead 4, storageDead 3
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    -- bb1: return
    apply execOutcomeStateV2_done (by
      dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
          List.nil_append, entryProgForBody, Captured.program, Captured.body_3,
        List.append, Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rw [ite_bool_true]; rotate_left; rfl)
    rfl
  have hRes3 := spec_and_behaviorV2_of_exec_eq hExec
  refine ⟨hRes3.1, ?_⟩
  rw [hList]
  dsimp only
  rw [hPaId, hPbId]
  dsimp only
  refine ⟨pb_arr b0 b1 b2 b3, pb_arr c0 c1 c2 c3, hLoadA, hLoadB, ?_⟩
  rw [hEqSpec]
  exact hRes3.2.1

/-! ## Top-Level Crate Verification Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, ?_⟩
      intro q hValid _
      exact (make_pair_correct q hValid).1
    | succ d1 =>
      cases d1 with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        refine ⟨rfl, by decide, ?_⟩
        intro q hValid _
        exact (pair_tag_correct q hValid).1
      | succ d2 =>
        cases d2 with
        | zero =>
          change some Captured.body_2 = some body at hBody
          cases hBody
          refine ⟨rfl, by decide, ?_⟩
          intro q hValid _
          exact (digest_byte_correct q hValid).1
        | succ d3 =>
          cases d3 with
          | zero =>
            change some Captured.body_3 = some body at hBody
            cases hBody
            refine ⟨rfl, by decide, ?_⟩
            intro q hValid _
            exact (digests_differ_correct q hValid).1
          | succ d4 =>
            cases d4 with
            | zero =>
              change some Captured.body_4 = some body at hBody
              cases hBody
              refine ⟨rfl, by decide, ?_⟩
              intro q hValid _
              exact (digest_eq_correct q hValid).1
            | succ _ =>
              change none = some body at hBody
              cases hBody
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hValid
      exact (make_pair_correct q hValid).2
    · intro q hValid
      exact (pair_tag_correct q hValid).2
    · intro q hValid
      exact (digest_byte_correct q hValid).2
    · intro q hValid
      exact (digests_differ_correct q hValid).2
    · intro q hValid
      exact (digest_eq_correct q hValid).2

end Proof
