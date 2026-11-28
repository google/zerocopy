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

/-! ## Body 0: `first::<u8>` -/

private theorem first_u8_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q ∧
    match q.args with
    | [x, _] =>
      BehaviorV2 (entryProgForBody Captured.program 0) q
        (TerminalOut.returned ⟨x, q.callerMem⟩)
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
          cases hV1 : checkValV2 v1 (.int .i8 false) <;>
          rw [hV0, hV1] at hArgs <;> cases hArgs
      | nil =>
        rw [hList] at hArgs
        dsimp only [Captured.body_0, checkArgsMatchV2, List.drop, List.take] at hArgs
        cases hV0 : checkValV2 v0 (.int .i8 false) with
        | false => rw [hV0] at hArgs; cases hArgs
        | true =>
          cases hV1 : checkValV2 v1 (.int .i8 false) with
          | false => rw [hV0, hV1] at hArgs; cases hArgs
          | true =>
            let ⟨bits0, hv0, _⟩ := checkValV2_scalar_inv hV0
            let ⟨bits1, hv1, _⟩ := checkValV2_scalar_inv hV1
            subst hv0
            subst hv1
            let expectedOut : TerminalOut :=
              .returned ⟨.scalar ⟨.i8, false, bits0⟩, q.callerMem⟩
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
                   .immediate (some (.scalar ⟨.i8, false, bits1⟩))] := by
              rw [hList]; rfl
            have hExec : execProgV2 (entryProgForBody Captured.program 0) 4 q
                (fun o => o = expectedOut) := by
              unfold execProgV2
              rw [hInit, hLocs]
              -- bb0: _0 = move _1
              apply execOutcomeStateV2_step (by
                dsimp only [evalStepV2, activeFrameBody, attachCallers, List.cons_append,
                    List.nil_append, entryProgForBody, Captured.program,
                  Captured.body_0, List.append, Trusted.MirSemantics.getElem?,
                  evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
                  placeStaticTyV2, evalRvalueV2, evalOperandToSlotV2]
                rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
                dsimp only
                rw [ite_bool_false]; rotate_left; decide
                dsimp only
                rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
              -- bb0 terminator: drop(_2) -> bb1
              apply execOutcomeStateV2_step (by rfl)
              -- bb1: return
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

/-! ## Top-Level Unit Verification Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, ?_⟩
      intro q hValid _
      exact (first_u8_correct q hValid).1
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · intro q hValid
    exact (first_u8_correct q hValid).2

end Proof
