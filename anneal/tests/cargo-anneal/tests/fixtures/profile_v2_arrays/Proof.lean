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
import Anneal.MirWp.V2Memory

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
    (hLocs : body.locals.all isSupportedV2LocalTy = true)
    (hArgs : checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true)
    (hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpansList
      ((body.locals.drop 1).take body.argumentCount) q.args) = true)
    (hAct : assertConditionTypesValid body = true := by decide)
    (hNoRaw : tyListHasRawPtrV2
      ((body.locals.drop 1).take body.argumentCount) = false := by rfl) :
    initStateV2 p q = .ok ⟨[⟨p.entryDefId, 0, 0,
      initLocalsLoop body q.args 0 body.locals, none, none, none⟩],
      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  have h := Anneal.MirWp.initStateV2_ok_of hPW hPV hCM hEntry hNonEmpty hArgLt
    hSto hDiscr hCast hAct hLocs hArgs hRefs hDisj
  unfold entryMemoryForArgsV2 at h
  rw [hNoRaw] at h
  exact h

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
    {ps : PanicStrategy} {hLocal : Bool}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 = some (.immediate (some retVal)))
    (hNoRodata : hasEscapingRodataPtr callerMem mem retTy retVal = false)
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true) :
    evalTerminatorV2 body bb frame mem callerMem ps hLocal =
      .done (.returned
        ⟨retVal, extractReturnMemoryV2 callerMem mem frame.locals⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false hNoRodata, ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]

private theorem layoutOfTyV2_u8x4 :
    layoutOfTyV2 (.array (.int .i8 false) 4) = some ⟨4, 0⟩ := rfl

private theorem layoutOfTyV2_u8x3 :
    layoutOfTyV2 (.array (.int .i8 false) 3) = some ⟨3, 0⟩ := rfl

private theorem layoutOfTyV2_u8x2 :
    layoutOfTyV2 (.array (.int .i8 false) 2) = some ⟨2, 0⟩ := rfl

private theorem layoutOfTyV2_u8 :
    layoutOfTyV2 (.int .i8 false) = some ⟨1, 0⟩ := rfl

private theorem layoutOfTyV2_u16 :
    layoutOfTyV2 (.int .i16 false) = some ⟨2, 1⟩ := rfl

private theorem decodeValV2_u8_array (n : Nat) (bytes : List AllocByte) :
    decodeValV2 profileV2TargetEndian (.array (.int .i8 false) n) bytes =
      (if !Nat.beq bytes.length (n * 1) then .error .unsupported
       else
         match decodeFixedChunks 1 (decodeValV2 profileV2TargetEndian (.int .i8 false))
             n bytes with
         | .error k => .error k
         | .ok none => .ok none
         | .ok (some vs) => .ok (some (.array vs))) := rfl

private theorem encodeValV2_u8_array (n : Nat) (vs : List Val) :
    encodeValV2 profileV2TargetEndian (.array (.int .i8 false) n) (.array vs) =
      (if !checkValV2 (.array vs) (.array (.int .i8 false) n) then .error .unsupported
       else if !Nat.beq vs.length n then .error .unsupported
       else encodeValListWith (encodeValV2 profileV2TargetEndian (.int .i8 false)) vs) :=
  rfl

/-! ## Inversion Helpers for Scalar, Enum, and Array Entry Values -/

private theorem checkValV2_scalar_inv {v : Val} {w : IntWidth} {s : Bool}
    (h : checkValV2 v (.int w s) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ ScalarVal.wf ⟨w, s, bits⟩ = true := by
  have h1 : checkVal v (.int w s) = true := by
    cases v with
    | scalar sv => unfold checkValV2 at h; exact h
    | bool _ | unit | char _ | ordering _ | tuple _ | enumVal _ _
    | ptr _ | slicePtr _ _ | array _ | rangeTo _ | rangeFrom _ | range _ _
    | bytes _ | vec _ _ _ => cases h
    | optionVal o => cases o <;> cases h
    | boxPtr _ o => cases o <;> cases h
  exact let ⟨bits, hv, hTrunc⟩ := checkVal_int_iff.mp h1; ⟨bits, hv, beq_iff_eq.mpr hTrunc⟩

private theorem scalarVal_wf_i16 {bits : BitVec 128}
    (hWf : ScalarVal.wf ⟨.i16, false, bits⟩ = true) :
    bits.toNat < 65536 := by
  unfold ScalarVal.wf at hWf
  have hEq : truncateBits .i16 bits = bits := eq_of_beq hWf
  rw [← hEq, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

private theorem scalarVal_wf_i8 {bits : BitVec 128}
    (hWf : ScalarVal.wf ⟨.i8, false, bits⟩ = true) :
    bits.toNat < 256 := by
  unfold ScalarVal.wf at hWf
  have hEq : truncateBits .i8 bits = bits := eq_of_beq hWf
  rw [← hEq, toNat_truncateBits]
  exact Nat.mod_lt _ (by decide)

private theorem checkValV2_ref_ptr_inv {reqMut : Mutability} {pt : MirTy}
    {hNonSlice : ∀ elem, pt ≠ .slice elem} {v : Val}
    (h : checkValV2 v (.ref reqMut pt) = true)
    (hNonStr : pt ≠ .str := by intro hC; cases hC) :
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
    | slicePtr _ _ | array _ | rangeTo _ | rangeFrom _ | range _ _
    | bytes _ | vec _ _ _ => cases h
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

private theorem decodeValV2_u8_uninit :
    decodeValV2 profileV2TargetEndian (.int .i8 false) [.uninit] = .ok none := by
  delta decodeValV2
  dsimp only
  try (delta decodeValV2._f; dsimp only)
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
  delta decodeValV2
  dsimp only
  try (delta decodeValV2._f; dsimp only)
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

private theorem decodeValV2_u8x4_init (b0 b1 b2 b3 : UInt8)
    (p0 p1 p2 p3 : Option AllocId) :
    decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4)
      [.init b0 p0, .init b1 p1, .init b2 p2, .init b3 p3] =
      .ok (some (.array [
        .scalar ⟨.i8, false, BitVec.ofNat 128 b0.toNat⟩,
        .scalar ⟨.i8, false, BitVec.ofNat 128 b1.toNat⟩,
        .scalar ⟨.i8, false, BitVec.ofNat 128 b2.toNat⟩,
        .scalar ⟨.i8, false, BitVec.ofNat 128 b3.toNat⟩])) := by
  rw [decodeValV2_u8_array]
  try dsimp only [layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout]
  rw [ite_bool_false]; rotate_left; rfl
  dsimp only [decodeFixedChunks, List.take, List.drop]
  rw [decodeValV2_u8_init b0 p0, decodeValV2_u8_init b1 p1,
      decodeValV2_u8_init b2 p2, decodeValV2_u8_init b3 p3]
  rfl

/-! ## Body 0: `pack_le_rev` -/

private theorem pack_le_rev_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q ∧
    match q.args with
    | [.scalar x] =>
      let lo := BitVec.ofNat 128 (x.bits.toNat % 256)
      let hi := BitVec.ofNat 128 ((x.bits.toNat / 256) % 256)
      ∃ out : TerminalOut,
        BehaviorV2 (entryProgForBody Captured.program 0) q out ∧
        out = TerminalOut.returned
          ⟨.array [.scalar ⟨.i8, false, hi⟩, .scalar ⟨.i8, false, lo⟩], q.callerMem⟩
    | _ => False := by
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  cases hList : q.args with
  | nil => rw [hList] at hArgs; cases hArgs
  | cons v0 rest =>
    cases rest with
    | cons _ _ =>
      rw [hList] at hArgs
      dsimp only [Captured.body_0, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.int .i16 false) <;> rw [hV0] at hArgs <;> cases hArgs
    | nil =>
      rw [hList] at hArgs
      dsimp only [Captured.body_0, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.int .i16 false) with
      | false => rw [hV0] at hArgs; cases hArgs
      | true =>
        let ⟨bits, hv0, hWf⟩ := checkValV2_scalar_inv hV0
        subst hv0
        have hLoLt : bits.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
        have hHiLt : (bits.toNat / 256) % 256 < 256 := Nat.mod_lt _ (by decide)
        have hLoWf : ScalarVal.wf ⟨.i8, false, BitVec.ofNat 128 (bits.toNat % 256)⟩ = true :=
          scalarWf_i8_ofNat_lt hLoLt
        have hHiWf : ScalarVal.wf ⟨.i8, false, BitVec.ofNat 128 ((bits.toNat / 256) % 256)⟩ = true :=
          scalarWf_i8_ofNat_lt hHiLt
        have hCheckLo : checkValV2 (.scalar ⟨.i8, false, BitVec.ofNat 128 (bits.toNat % 256)⟩) (.int .i8 false) = true := by
          dsimp only [checkValV2, checkVal, Val.ty?, IntWidth.bitWidth]; rw [ite_bool_true hLoWf]; rfl
        have hCheckHi : checkValV2 (.scalar ⟨.i8, false, BitVec.ofNat 128 ((bits.toNat / 256) % 256)⟩) (.int .i8 false) = true := by
          dsimp only [checkValV2, checkVal, Val.ty?, IntWidth.bitWidth]; rw [ite_bool_true hHiWf]; rfl
        have hLoByte : (UInt8.ofNat (bits.toNat % 256)).toNat = bits.toNat % 256 :=
          Nat.mod_eq_of_lt hLoLt
        have hHiByte : (UInt8.ofNat ((bits.toNat / 256) % 256)).toNat = (bits.toNat / 256) % 256 :=
          Nat.mod_eq_of_lt hHiLt
        have hLoByteNat : (UInt8.ofNat (Nat.mod bits.toNat 256)).toNat = bits.toNat % 256 :=
          Nat.mod_eq_of_lt hLoLt
        have hHiByteNat : (UInt8.ofNat (Nat.mod (Nat.div bits.toNat 256) 256)).toNat = (bits.toNat / 256) % 256 :=
          Nat.mod_eq_of_lt hHiLt
        let svLo : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 (bits.toNat % 256)⟩
        let svHi : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 ((bits.toNat / 256) % 256)⟩
        let expectedOut : TerminalOut :=
          .returned ⟨.array [svHi, svLo], q.callerMem⟩
        have hInit : initStateV2 (entryProgForBody Captured.program 0) q =
            .ok ⟨[⟨0, 0, 0, initLocalsLoop Captured.body_0 q.args 0 Captured.body_0.locals,
              none, none, none⟩],
              q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
          apply initStateV2_ok_of (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
            (by decide) (by decide) (by decide) (by decide)
          · rw [hList]; exact hArgs
          · exact hRefs
          · exact hDisj
        have hLocs : initLocalsLoop Captured.body_0 q.args 0 Captured.body_0.locals =
            [.immediate none, .immediate (some (.scalar ⟨.i16, false, bits⟩)),
             .dead, .dead, .dead, .dead, .dead, .dead] := by
          rw [hList]; rfl
        have hExec : execProgV2 (entryProgForBody Captured.program 0) 30 q (fun o => o = expectedOut) := by
          unfold execProgV2
          rw [hInit, hLocs]
          -- bb0: storageLive 4, storageLive 5
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- bb0: assign 5 (use (copy 1))
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
            rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
            dsimp only
            rw [ite_bool_false]; rotate_left; decide
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
          -- bb0 terminator: coreCall intToLeBytes .i16 false [move 5] -> 4 goto
          -- 1
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?]
            rw [ite_bool_true]; rotate_left; decide
            dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
            rw [ite_bool_false]; rotate_left; decide
            dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
            rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
            dsimp only [evalArgOperandsV2, argValues,
              execCoreCallOpWithMemOutcome, execAllocCoreCallOutcome,
              execAllocCoreCallInfallible, execCoreCallWithMemOutcome,
              execCoreCallOp, leBytesOfNat]
            rw [ite_bool_false]; rotate_left; (dsimp only [IntWidth.byteSize]; rw [hWf]; decide)
            dsimp only [IntWidth.byteSize, List.map]
            have hLe2 : List.map (fun b : UInt8 => Val.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)
                (leBytesOfNat 2 bits.toNat) = [svLo, svHi] := by
              dsimp only [svLo, svHi]
              change [Val.scalar ⟨.i8, false, BitVec.ofNat 128 (UInt8.ofNat (Nat.mod bits.toNat 256)).toNat⟩,
                      Val.scalar ⟨.i8, false, BitVec.ofNat 128 (UInt8.ofNat (Nat.mod (Nat.div bits.toNat 256) 256)).toNat⟩] = _
              rw [hLoByteNat, hHiByteNat]
            rw [hLe2]
            have hCheckArr : checkValV2 (.array [svLo, svHi]) (.array (.int .i8 false) 2) = true := by
              dsimp only [svLo, svHi, checkValV2, checkValUniformV2, checkVal, Val.ty?, IntWidth.bitWidth]
              rw [ite_bool_true hLoWf, ite_bool_true hHiWf]
              rfl
            rw [writePlaceV2_immediate_ok hCheckArr (by rfl) (by rfl)]
            rfl)
          -- bb1: storageDead 5, nop, storageLive 2
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- assign 2 (copy 4.[0])
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2,
              projectValFieldV2, projectOneElemV2, constantIndexOffset]
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            dsimp only [Trusted.MirSemantics.getElem?]
            rw [ite_bool_false]; rotate_left; decide
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok hCheckLo (by rfl) (by rfl)]; rfl)
          -- storageLive 3
          apply execOutcomeStateV2_step (by rfl)
          -- assign 3 (copy 4.[1])
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2,
              projectValFieldV2, projectOneElemV2, constantIndexOffset]
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            dsimp only [Trusted.MirSemantics.getElem?]
            rw [ite_bool_false]; rotate_left; decide
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok hCheckHi (by rfl) (by rfl)]; rfl)
          -- storageDead 4, storageLive 6
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- assign 6 (copy 3)
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
            rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
            dsimp only
            rw [ite_bool_false]; rotate_left; decide
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok hCheckHi (by rfl) (by rfl)]; rfl)
          -- storageLive 7
          apply execOutcomeStateV2_step (by rfl)
          -- assign 7 (copy 2)
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
            rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
            dsimp only
            rw [ite_bool_false]; rotate_left; decide
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok hCheckLo (by rfl) (by rfl)]; rfl)
          -- assign 0 (aggregateArray .i8 [move 6, move 7])
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalArgOperandsV2, evalOperandToSlotV2]
            rw [ite_bool_false]; rotate_left; decide
            rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
            dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
            rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
            dsimp only [argValues]
            have hCheck2 : checkValUniformV2 (fun v => checkValV2 v (.int .i8 false))
                [.scalar ⟨.i8, false, BitVec.ofNat 128 ((bits.toNat / 256) % 256)⟩,
                 .scalar ⟨.i8, false, BitVec.ofNat 128 (bits.toNat % 256)⟩] = true := by
              dsimp only [checkValUniformV2, checkValV2, checkVal, Val.ty?, IntWidth.bitWidth]
              rw [ite_bool_true hHiWf, ite_bool_true hLoWf]
              rfl
            have hChkOut : checkValV2 (.array
                [.scalar ⟨.i8, false, BitVec.ofNat 128 ((bits.toNat / 256) % 256)⟩,
                 .scalar ⟨.i8, false, BitVec.ofNat 128 (bits.toNat % 256)⟩])
                (.array (.int .i8 false) 2) = true := by
              dsimp only [checkValV2, checkValUniformV2, checkVal, Val.ty?, IntWidth.bitWidth]
              rw [ite_bool_true hHiWf, ite_bool_true hLoWf]
              rfl
            simp only [hCheck2]
            rw [ite_bool_false]; rotate_left; rfl
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok hChkOut (by rfl) (by rfl)]; rfl)
          -- storageDead 7, 6, 3, 2
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- return_
          apply execOutcomeStateV2_done (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
              List.append, Trusted.MirSemantics.getElem?]
            rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
              (by rfl) (by rfl) (by rfl) (by rfl)]
            rw [rm2_extractReturnMemoryV2_entry]
            rw [extractCallerMemory_entry q.callerMem hCM]
            rfl)
          rfl
        have hRes := spec_and_behaviorV2_of_exec_eq hExec
        exact ⟨hRes.1, expectedOut, hRes.2.1, rfl⟩

/-! ## Body 1: `repeat_unsize_len` -/

private theorem repeat_unsize_len_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q ∧
    ∃ out : TerminalOut,
      BehaviorV2 (entryProgForBody Captured.program 1) q out ∧
      out = TerminalOut.returned ⟨.scalar ⟨.isize, false, BitVec.ofNat 128 3⟩, q.callerMem⟩ := by
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  cases hList : q.args with
  | nil => rw [hList] at hArgs; cases hArgs
  | cons v0 rest =>
    cases rest with
    | cons _ _ =>
      rw [hList] at hArgs
      dsimp only [Captured.body_1, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.int .i8 false) <;> rw [hV0] at hArgs <;> cases hArgs
    | nil =>
      rw [hList] at hArgs
      dsimp only [Captured.body_1, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.int .i8 false) with
      | false => rw [hV0] at hArgs; cases hArgs
      | true =>
        let ⟨bits, hv0, hWf⟩ := checkValV2_scalar_inv hV0
        subst hv0
        let expectedOut : TerminalOut :=
          .returned ⟨.scalar ⟨.isize, false, BitVec.ofNat 128 3⟩, q.callerMem⟩
        let stackAid := (entryMemoryWithCaller q.callerMem).nextAllocId
        have hAidFresh : ∀ a, a ∈ q.callerMem.allocations → a.allocId ≠ stackAid := by
          intro a ha hEq
          have hLe : a.allocId ≤ maxAllocId q.callerMem.allocations := allocId_le_maxAllocId ha
          have hLtAid : maxAllocId q.callerMem.allocations < stackAid := by
            change maxAllocId q.callerMem.allocations <
              Nat.max entryMemory.nextAllocId (maxAllocAndProvId q.callerMem.allocations + 1)
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_left _ _))
              (Nat.le_max_right _ _)
          exact absurd (hEq ▸ hLe) (Nat.not_le_of_lt hLtAid)
        let stackAlloc : Allocation := {
          allocId := stackAid
          alignLog2 := 0
          mutability := .mut
          bytes := [.init (UInt8.ofNat bits.toNat) none,
                    .init (UInt8.ofNat bits.toNat) none,
                    .init (UInt8.ofNat bits.toNat) none]
          live := true
        }
        have hFindStack :
            findAllocation stackAid (q.callerMem.allocations ++ [stackAlloc]) = some stackAlloc :=
          findAllocation_append_single_fresh (x := stackAlloc) hAidFresh
        have hRefStackPtr :
            refValidInMem
              { nextAllocId := stackAid + 1, allocations := q.callerMem.allocations ++ [stackAlloc] }
              .shared (.array (.int .i8 false) 3) (.ptr ⟨some stackAid, UInt64.ofNat 0, .isize⟩) =
            .ok () := by
          unfold refValidInMem
          dsimp only [layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout]
          rw [hFindStack]
          dsimp only
          rw [ite_bool_false]; rotate_left; rfl
          rw [ite_bool_false]; rotate_left; rfl
          rw [show (UInt64.ofNat 0).toNat = 0 from rfl]
          rw [decodeValV2_u8_array]
          try dsimp only [layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout]
          rw [ite_bool_false]; rotate_left; rfl
          try rw [show 3 * 1 = 3 from rfl]
          dsimp only [stackAlloc, decodeFixedChunks, List.take, List.drop]
          rw [decodeValV2_u8_init]
          rfl
        have hRefStackSlice :
            refValidInMem
              { nextAllocId := stackAid + 1, allocations := q.callerMem.allocations ++ [stackAlloc] }
              .shared (.slice (.int .i8 false))
              (.slicePtr ⟨some stackAid, UInt64.ofNat 0, .isize⟩ (UInt64.ofNat 3)) =
            .ok () := by
          unfold refValidInMem sliceFromRawPartsCheck sliceRefRawCheck
          dsimp only [intLayout, layoutOfTyV2_u8]
          rw [ite_bool_false]; rotate_left; rfl
          rw [hFindStack]
          dsimp only
          rw [ite_bool_false]; rotate_left; rfl
          rw [ite_bool_false]; rotate_left; rfl
          rw [ite_bool_false]; rotate_left; rfl
          dsimp only
          rw [ite_bool_false]; rotate_left; rfl
        have hInit : initStateV2 (entryProgForBody Captured.program 1) q =
            .ok ⟨[⟨1, 0, 0, initLocalsLoop Captured.body_1 q.args 0 Captured.body_1.locals,
              none, none, none⟩],
              q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
          apply initStateV2_ok_of (p := entryProgForBody Captured.program 1) (q := q)
            (body := Captured.body_1) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
            (by decide) (by decide) (by decide) (by decide)
          · rw [hList]; exact hArgs
          · exact hRefs
          · exact hDisj
        have hLocs : initLocalsLoop Captured.body_1 q.args 0 Captured.body_1.locals =
            [.immediate none, .immediate (some (.scalar ⟨.i8, false, bits⟩)),
             .dead, .dead, .dead, .dead, .dead, .dead] := by
          rw [hList]; rfl
        have hExec : execProgV2 (entryProgForBody Captured.program 1) 30 q (fun o => o = expectedOut) := by
          unfold execProgV2
          rw [hInit, hLocs]
          -- bb0: storageLive 2, storageLive 3
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- assign 3 (use (copy 1))
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
            rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
            dsimp only
            rw [ite_bool_false]; rotate_left; decide
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
          -- assign 2 (repeat_ (move 3) .i8 3)
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
            rw [ite_bool_false]; rotate_left; decide
            rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
            dsimp only
            rw [ite_bool_false]; rotate_left; decide
            rw [ite_bool_false]; rotate_left; (rw [hV0]; rfl)
            dsimp only [List.replicate]
            have hChkArr : checkValV2 (.array [.scalar ⟨.i8, false, bits⟩,
                .scalar ⟨.i8, false, bits⟩, .scalar ⟨.i8, false, bits⟩])
                (.array (.int .i8 false) 3) = true := by
              dsimp only [checkValV2, checkValUniformV2, checkVal, Val.ty?, IntWidth.bitWidth]
              rw [ite_bool_true hWf]
              rfl
            rw [writePlaceDestV2_immediate_ok hChkArr (by rfl) (by rfl)]; rfl)
          -- storageDead 3, storageLive 4, storageLive 5, storageLive 6
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- assign 6 (ref .shared 2): promotes local 2 to stackAlloc in memory!
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalRefRvalueV2,
              promoteLocalToMemory, layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
              layoutOfArrayV2, layoutOfTy, intLayout, allocateStack,
              MemoryState.reserveAllocId, storeIndirectV2]
            have hChkArr : checkValV2 (.array [.scalar ⟨.i8, false, bits⟩,
                .scalar ⟨.i8, false, bits⟩, .scalar ⟨.i8, false, bits⟩])
                (.array (.int .i8 false) 3) = true := by
              dsimp only [checkValV2, checkValUniformV2, checkVal, Val.ty?, IntWidth.bitWidth]
              rw [ite_bool_true hWf]
              rfl
            have hEncArr : encodeValV2 profileV2TargetEndian (.array (.int .i8 false) 3)
                (.array [.scalar ⟨.i8, false, bits⟩, .scalar ⟨.i8, false, bits⟩, .scalar ⟨.i8, false, bits⟩]) =
                .ok [AllocByte.init (UInt8.ofNat bits.toNat) none,
                     AllocByte.init (UInt8.ofNat bits.toNat) none,
                     AllocByte.init (UInt8.ofNat bits.toNat) none] := by
              have hCE : checkVal (.scalar ⟨.i8, false, bits⟩) (.int .i8 false) = true := by
                dsimp only [checkVal, Val.ty?, IntWidth.bitWidth]; rw [ite_bool_true hWf]; rfl
              have hCE2 : checkValV2 (.scalar ⟨.i8, false, bits⟩) (.int .i8 false) = true := by
                dsimp only [checkValV2]; exact hCE
              have hEncElem : encodeValV2 profileV2TargetEndian (.int .i8 false) (.scalar ⟨.i8, false, bits⟩) =
                  .ok [AllocByte.init (UInt8.ofNat bits.toNat) none] := by
                delta encodeValV2
                dsimp only
                try (delta encodeValV2._f; dsimp only)
                unfold encodeVal
                rw [ite_bool_false (by rw [hCE2]; rfl)]
                dsimp only
                rw [ite_bool_false (by rw [hCE]; rfl)]
                dsimp only [encodeUInt, IntWidth.byteSize]
                change Except.ok (List.map (fun b => AllocByte.init b none) [UInt8.ofNat (Nat.mod bits.toNat 256)]) = _
                have hByteEq : UInt8.ofNat (Nat.mod bits.toNat 256) = UInt8.ofNat bits.toNat :=
                  congrArg UInt8.ofBitVec (BitVec.eq_of_toNat_eq
                    (by change (bits.toNat % 256) % 256 = bits.toNat % 256
                        rw [Nat.mod_mod_of_dvd _ (by decide)]))
                rw [hByteEq]
                rfl
              rw [encodeValV2_u8_array]
              rw [ite_bool_false (by rw [hChkArr]; rfl)]
              try dsimp only
              rw [ite_bool_false]; rotate_left; rfl
              dsimp only [encodeValListWith]
              rw [hEncElem]
              rfl
            rw [hEncArr]
            dsimp only [List.replicate]
            let uninitAlloc : Allocation :=
              { allocId := stackAid, alignLog2 := 0, mutability := .mut,
                bytes := [.uninit, .uninit, .uninit], live := true }
            have hFindRaw :
                findAllocation stackAid ((entryMemoryWithCaller q.callerMem).allocations ++ [uninitAlloc]) =
                some uninitAlloc :=
              findAllocation_append_single_fresh (x := uninitAlloc) hAidFresh
            have hReplRaw :
                replaceAllocation stackAlloc
                  ((entryMemoryWithCaller q.callerMem).allocations ++ [uninitAlloc]) =
                q.callerMem.allocations ++ [stackAlloc] := by
              change replaceAllocation stackAlloc (q.callerMem.allocations ++ [uninitAlloc]) =
                q.callerMem.allocations ++ [stackAlloc]
              have hAux : ∀ (xs : List Allocation), (∀ a, a ∈ xs → a.allocId ≠ stackAid) →
                  replaceAllocation stackAlloc (xs ++ [uninitAlloc]) = xs ++ [stackAlloc] := by
                intro xs hXs
                induction xs with
                | nil =>
                  change (if Nat.beq stackAid stackAid then stackAlloc :: [] else _) = [stackAlloc]
                  rw [Nat.beq_refl]; rfl
                | cons hd tl ih =>
                  have hNe : hd.allocId ≠ stackAid := hXs hd (.head _)
                  have hBeq : Nat.beq hd.allocId stackAid = false := by
                    cases hEq : Nat.beq hd.allocId stackAid with
                    | false => rfl
                    | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe
                  change (if Nat.beq hd.allocId stackAid then stackAlloc :: _ else hd :: replaceAllocation stackAlloc _) = _
                  rw [hBeq]
                  exact congrArg (hd :: ·) (ih (fun a ha => hXs a (.tail _ ha)))
              exact hAux q.callerMem.allocations hAidFresh
            have hWB :
                writeBytes
                  { nextAllocId := stackAid + 1,
                    allocations := (entryMemoryWithCaller q.callerMem).allocations ++ [uninitAlloc] }
                  ⟨stackAid, 0⟩ 0
                  [.init (UInt8.ofNat bits.toNat) none,
                   .init (UInt8.ofNat bits.toNat) none,
                   .init (UInt8.ofNat bits.toNat) none] =
                .ok { nextAllocId := stackAid + 1,
                      allocations := q.callerMem.allocations ++ [stackAlloc] } := by
              unfold writeBytes
              rw [hFindRaw]
              dsimp only
              rw [ite_bool_false]; rotate_left; rfl
              dsimp only [uninitAlloc, isInBounds, isAligned]
              change (if false = true then (Except.error FaultKind.undefined : Except FaultKind MemoryState) else
                (Except.ok (MemoryState.mk (stackAid + 1)
                  (replaceAllocation
                    (Allocation.mk stackAid 0 .mut
                      (List.take 0 [.uninit, .uninit, .uninit] ++
                        [.init (UInt8.ofNat bits.toNat) none,
                         .init (UInt8.ofNat bits.toNat) none,
                         .init (UInt8.ofNat bits.toNat) none] ++
                        List.drop 3 [.uninit, .uninit, .uninit])
                      true)
                    ((entryMemoryWithCaller q.callerMem).allocations ++ [uninitAlloc]))) : Except FaultKind MemoryState)) = _
              rw [ite_bool_false rfl]
              dsimp only [List.take, List.drop]
              rw [List.nil_append, List.append_nil, hReplRaw]
            rw [hWB]
            dsimp only [Trusted.MirSemantics.setElem?]
            rw [ite_bool_false]; rotate_left; decide
            rw [hRefStackPtr]
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]
            try rfl)
          -- assign 5 (ref .shared (*6))
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalRefRvalueV2]
            rw [ite_bool_false]; rotate_left; decide
            rw [ite_bool_false]; rotate_left; decide
            rw [hRefStackPtr]
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]
            try rfl)
          -- assign 4 (cast .unsize (move 5))
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
            rw [ite_bool_false]; rotate_left; decide
            rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
            dsimp only
            rw [ite_bool_false]; rotate_left; decide
            rw [ite_bool_false]; rotate_left; decide
            rw [hRefStackPtr]
            dsimp only
            rw [hRefStackSlice]
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]
            try rfl)
          -- storageDead 5, storageDead 6, storageLive 7
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- assign 7 (ref .shared (*4))
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
              stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalRefRvalueV2]
            rw [ite_bool_false]; rotate_left; decide
            rw [ite_bool_false]; rotate_left; decide
            rw [hRefStackSlice]
            dsimp only
            repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
            try dsimp only
            rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]
            try rfl)
          -- coreCall .sliceLen [move 7] -> 0 goto 1
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?]
            rw [ite_bool_true]; rotate_left; decide
            dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
            rw [ite_bool_false]; rotate_left; decide
            dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
            rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
            dsimp only [evalArgOperandsV2, argValues,
              execCoreCallOpWithMemOutcome, execAllocCoreCallOutcome,
              execAllocCoreCallInfallible, execCoreCallWithMemOutcome,
              execCoreCallOp]
            rw [ite_bool_false]; rotate_left; decide
            rw [hRefStackSlice]
            dsimp only
            rw [writePlaceV2_immediate_ok (by decide) (by rfl) (by rfl)]
            try rfl)
          -- bb1: storageDead 7, storageDead 4
          apply execOutcomeStateV2_step (by rfl)
          apply execOutcomeStateV2_step (by rfl)
          -- bb1: storageDead 2 (deallocates stackAlloc)
          apply execOutcomeStateV2_step (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?, evalStatementV2, deallocateLocal,
              deallocateStack]
            rw [hFindStack]
            rfl)
          -- bb1: return_
          apply execOutcomeStateV2_done (by
            dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_1,
              List.append, Trusted.MirSemantics.getElem?]
            rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
              (by rfl) (by rfl) (by rfl) (by rfl)]
            have hReplDead :
                replaceAllocation { stackAlloc with live := false }
                  (q.callerMem.allocations ++ [stackAlloc]) =
                q.callerMem.allocations ++ [{ stackAlloc with live := false }] := by
              have hAux : ∀ (xs : List Allocation), (∀ a, a ∈ xs → a.allocId ≠ stackAid) →
                  replaceAllocation { stackAlloc with live := false } (xs ++ [stackAlloc]) =
                  xs ++ [{ stackAlloc with live := false }] := by
                intro xs hXs
                induction xs with
                | nil =>
                  change (if Nat.beq stackAid stackAid then _ :: [] else _) = _
                  rw [Nat.beq_refl]; rfl
                | cons hd tl ih =>
                  have hNe : hd.allocId ≠ stackAid := hXs hd (.head _)
                  have hBeq : Nat.beq hd.allocId stackAid = false := by
                    cases hEq : Nat.beq hd.allocId stackAid with
                    | false => rfl
                    | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe
                  change (if Nat.beq hd.allocId stackAid then _ else hd :: replaceAllocation _ _) = _
                  rw [hBeq]
                  exact congrArg (hd :: ·) (ih (fun a ha => hXs a (.tail _ ha)))
              exact hAux q.callerMem.allocations hAidFresh
            have hCallerUnchanged :
                extractCallerMemory q.callerMem {
                  nextAllocId := stackAid + 1
                  allocations := replaceAllocation { stackAlloc with live := false }
                    (q.callerMem.allocations ++ [stackAlloc])
                } = q.callerMem := by
              rw [hReplDead]
              exact extractCallerMemory_append_single hCM
            have hIdsM : ∀ a, a ∈ replaceAllocation { stackAlloc with live := false }
                  (q.callerMem.allocations ++ [stackAlloc]) →
                a.allocId ∈ allocIdsOf q.callerMem.allocations ∨ a.live = false := by
              intro a ha
              rw [hReplDead] at ha
              rcases List.mem_append.mp ha with h | h
              · exact .inl (rm2_mem_allocIdsOf h)
              · cases h with
                | head _ => exact .inr rfl
                | tail _ h' => cases h'
            rw [rm2_extractReturnMemoryV2_eq_dead (mem := ⟨stackAid + 1,
              replaceAllocation { stackAlloc with live := false }
                (q.callerMem.allocations ++ [stackAlloc])⟩) _ hIdsM]
            rw [hCallerUnchanged]
            rfl)
          rfl
        have hRes := spec_and_behaviorV2_of_exec_eq hExec
        exact ⟨hRes.1, expectedOut, hRes.2.1, rfl⟩

/-! ## Body 2: `tag_eq` -/

private abbrev tagEnumTy : EnumTy :=
  { id := 933338508
    discrWidth := .i8
    discrSigned := false
    tagRepr := .scalar .i8 false
    discriminants := [0, 1] }

private theorem refValidInMem_tag_inv {m : MemoryState} {p : PtrVal}
    (hRef : refValidInMem m .shared (.enum tagEnumTy) (.ptr p) = .ok ()) :
    ∃ (aid : AllocId) (a : Allocation) (b : UInt8) (prov : Option AllocId),
      p.allocId = some aid ∧
      findAllocation aid m.allocations = some a ∧
      a.live = true ∧
      isInBounds a p.offsetBytes.toNat 1 = true ∧
      Trusted.MirSemantics.getElem? a.bytes p.offsetBytes.toNat = some (.init b prov) ∧
      (b = 0 ∨ b = 1) := by
  have hLay : layoutOfTyV2 (.enum tagEnumTy) = some (intLayout .i8) := by
    have hAdm : enumAdmitted tagEnumTy = true := by decide
    rfl
  unfold refValidInMem at hRef
  rw [hLay] at hRef
  dsimp only [intLayout] at hRef
  cases hAid : p.allocId with
  | none =>
    rw [hAid] at hRef
    dsimp only at hRef
    have hZ : (Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 1) = true := by
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
      cases hBad : (!a.live || !isInBounds a p.offsetBytes.toNat 1 ||
          !isAligned a p.offsetBytes.toNat 0) with
      | true => rw [hBad] at hRef; cases hRef
      | false =>
        rw [hBad] at hRef
        rw [ite_bool_false] at hRef; rotate_left; rfl
        dsimp only [Mutability.beq] at hRef
        have hLive : a.live = true := by
          cases hL : a.live with
          | true => rfl
          | false => rw [hL] at hBad; cases hBad
        have hInB : isInBounds a p.offsetBytes.toNat 1 = true := by
          cases hI : isInBounds a p.offsetBytes.toNat 1 with
          | true => rfl
          | false => rw [hI] at hBad; cases hL : a.live <;> rw [hL] at hBad <;> cases hBad
        have hLeLen : p.offsetBytes.toNat + 1 ≤ a.bytes.length := le_of_ble_true hInB
        have hLtLen : p.offsetBytes.toNat < a.bytes.length :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hLeLen
        have hGetDrop : ∀ (off : Nat) (bs : List AllocByte), off < bs.length →
            ∃ x, Trusted.MirSemantics.getElem? bs off = some x ∧ (bs.drop off).take 1 = [x] := by
          intro off bs hOff
          induction off generalizing bs with
          | zero =>
            cases bs with
            | nil => cases hOff
            | cons x _ => exact ⟨x, rfl, rfl⟩
          | succ k ih =>
            cases bs with
            | nil => cases hOff
            | cons _ tl =>
              exact ih tl (Nat.lt_of_succ_lt_succ hOff)
        rcases hGetDrop p.offsetBytes.toNat a.bytes hLtLen with ⟨byte0, hGet0, hSlice0⟩
        rw [hSlice0] at hRef
        cases byte0 with
        | uninit => cases hRef
        | init b prov =>
          have hAdm : enumAdmitted tagEnumTy = true := by decide
          cases hb0 : Nat.beq b.toNat 0 with
          | true =>
            cases b with | ofBitVec bv =>
            have hBv : bv = 0 := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb0)
            subst hBv
            exact ⟨aid, a, 0, prov, rfl, hFind, hLive, hInB, hGet0, .inl rfl⟩
          | false =>
            cases hb1 : Nat.beq b.toNat 1 with
            | true =>
              cases b with | ofBitVec bv =>
              have hBv : bv = 1 := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb1)
              subst hBv
              exact ⟨aid, a, 1, prov, rfl, hFind, hLive, hInB, hGet0, .inr rfl⟩
            | false =>
              have hB0 : b.toNat ≠ 0 := fun h => by rw [h] at hb0; cases hb0
              have hB1 : b.toNat ≠ 1 := fun h => by rw [h] at hb1; cases hb1
              have hBLt : b.toNat < 256 := b.toBitVec.isLt
              have hNe0 : (BitVec.ofNat 128 0 == BitVec.ofNat 128 b.toNat) = false := by
                cases hEq : (BitVec.ofNat 128 0 == BitVec.ofNat 128 b.toNat) with
                | false => rfl
                | true =>
                  have hBv := congrArg BitVec.toNat (beq_iff_eq.mp hEq)
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hBv
                  rw [Nat.mod_eq_of_lt (by decide),
                      Nat.mod_eq_of_lt (Nat.lt_trans hBLt (by decide))] at hBv
                  exact absurd hBv.symm hB0
              have hNe1 : (BitVec.ofNat 128 1 == BitVec.ofNat 128 b.toNat) = false := by
                cases hEq : (BitVec.ofNat 128 1 == BitVec.ofNat 128 b.toNat) with
                | false => rfl
                | true =>
                  have hBv := congrArg BitVec.toNat (beq_iff_eq.mp hEq)
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hBv
                  rw [Nat.mod_eq_of_lt (by decide),
                      Nat.mod_eq_of_lt (Nat.lt_trans hBLt (by decide))] at hBv
                  exact absurd hBv.symm hB1
              have hTrunc : truncateBits .i8 (BitVec.ofNat 128 b.toNat) = BitVec.ofNat 128 b.toNat := by
                apply bitVec_eq_of_toNat_eq
                rw [toNat_truncateBits, BitVec.toNat_ofNat]
                change (b.toNat % Nat.pow 2 128) % 256 = b.toNat % Nat.pow 2 128
                rw [Nat.mod_eq_of_lt (Nat.lt_trans hBLt (by decide)), Nat.mod_eq_of_lt hBLt]
              have hLay1 : layoutOfTy (.enum tagEnumTy) = some (intLayout .i8) := by
                dsimp only [layoutOfTy]; rw [hAdm]; rfl
              delta decodeValV2 at hRef
              dsimp only at hRef
              try (delta decodeValV2._f at hRef; dsimp only at hRef)
              change (match decodeVal profileV2TargetEndian (.enum tagEnumTy) [AllocByte.init b prov] with
                | Except.ok (some _) => Except.ok ()
                | Except.ok none => Except.error FaultKind.undefined
                | Except.error k => Except.error k) = Except.ok () at hRef
              unfold decodeVal at hRef
              rw [hLay1] at hRef
              dsimp only [profileV2TargetEndian, intLayout, initBytes?, decodeUInt] at hRef
              rw [ite_bool_false] at hRef; rotate_left; rfl
              rw [ite_bool_false] at hRef; rotate_left; rfl
              dsimp only [evalConstLit, tagBitsToDiscrBits, findDiscrVariant?,
                findDiscrVariantAux, tagEnumTy] at hRef
              rw [hAdm] at hRef
              have hDecB : natOfLeBytes [b] = b.toNat := by
                dsimp only [natOfLeBytes]
                rw [Nat.mul_zero, Nat.add_zero]
              rw [hDecB] at hRef
              have hWfB : (!true || (truncateBits .i8 (BitVec.ofNat 128 b.toNat) != BitVec.ofNat 128 b.toNat)) = false := by
                rw [hTrunc]; exact bne_self_eq_false _
              rw [ite_bool_false hWfB] at hRef
              rw [hTrunc] at hRef
              rw [show (if false = true then bvOfInt 128 (signExtendBits .i8 (BitVec.ofNat 128 b.toNat))
                  else BitVec.ofNat 128 b.toNat) = BitVec.ofNat 128 b.toNat from rfl] at hRef
              rw [hTrunc, hNe0] at hRef
              rw [ite_bool_false] at hRef; rotate_left; rfl
              rw [hNe1] at hRef
              rw [ite_bool_false] at hRef; rotate_left; rfl
              cases hRef

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

private theorem tag_eq_tail_ba0
    {q : Query} {pa pb : PtrVal} {ida idb : AllocId} {bb : UInt8}
    (hCM : validCallerMemory q.callerMem = true)
    (hV1 : checkValV2 (.ptr pb) (.ref .shared (.enum tagEnumTy)) = true)
    (hPaId : pa.allocId = some ida) (hPbId : pb.allocId = some idb)
    (hLay : layoutOfTyV2 (.enum tagEnumTy) = some (intLayout .i8))
    (hLoadA : loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.enum tagEnumTy)
      ⟨ida, pa.offsetBytes.toNat⟩ = .ok (some (.enumVal tagEnumTy 0)))
    (hLoadB : loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.enum tagEnumTy)
      ⟨idb, pb.offsetBytes.toNat⟩ =
        .ok (some (.enumVal tagEnumTy (if bb = 0 then 0 else 1))))
    (hBbCase : bb = 0 ∨ bb = 1) :
    execOutcomeStateV2 (entryProgForBody Captured.program 2)
      (fun o => o = .returned ⟨.bool (Nat.beq (0 : UInt8).toNat bb.toNat), q.callerMem⟩)
      (fun _ => False) 20
      ⟨[⟨2, 0, 10,
        [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)),
         .immediate (some (.tuple [.ptr pa, .ptr pb])), .dead, .dead,
         .immediate none, .immediate none, .immediate none,
         .immediate (some (.ptr pa)), .immediate none, .immediate none],
        none, none, none⟩],
       q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  rcases hBbCase with rfl | rfl
  · -- ba = 0, bb = 0
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPaId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadA]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl) -- bb0 term -> bb2
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2,
        projectValFieldV2, projectOneElemV2]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]
      try rfl) -- bb2 stmt 0: 10 = copy 3.1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPbId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadB]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)]
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl) -- bb2 term -> bb4
    apply execOutcomeStateV2_step (by rfl) -- bb4 stmt 0: 0 = true
    apply execOutcomeStateV2_step (by rfl) -- bb4 term -> bb5
    apply execOutcomeStateV2_step (by rfl) -- bb5 stmt 0: storageDead 3
    apply execOutcomeStateV2_done (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [rm2_extractReturnMemoryV2_entry]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rfl)
    rfl
  · -- ba = 0, bb = 1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPaId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadA]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2,
        projectValFieldV2, projectOneElemV2]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]
      try rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPbId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadB]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)]
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_done (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [rm2_extractReturnMemoryV2_entry]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rfl)
    rfl

private theorem tag_eq_tail_ba1
    {q : Query} {pa pb : PtrVal} {ida idb : AllocId} {bb : UInt8}
    (hCM : validCallerMemory q.callerMem = true)
    (hV1 : checkValV2 (.ptr pb) (.ref .shared (.enum tagEnumTy)) = true)
    (hPaId : pa.allocId = some ida) (hPbId : pb.allocId = some idb)
    (hLay : layoutOfTyV2 (.enum tagEnumTy) = some (intLayout .i8))
    (hLoadA : loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.enum tagEnumTy)
      ⟨ida, pa.offsetBytes.toNat⟩ = .ok (some (.enumVal tagEnumTy 1)))
    (hLoadB : loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.enum tagEnumTy)
      ⟨idb, pb.offsetBytes.toNat⟩ =
        .ok (some (.enumVal tagEnumTy (if bb = 0 then 0 else 1))))
    (hBbCase : bb = 0 ∨ bb = 1) :
    execOutcomeStateV2 (entryProgForBody Captured.program 2)
      (fun o => o = .returned ⟨.bool (Nat.beq (1 : UInt8).toNat bb.toNat), q.callerMem⟩)
      (fun _ => False) 20
      ⟨[⟨2, 0, 10,
        [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)),
         .immediate (some (.tuple [.ptr pa, .ptr pb])), .dead, .dead,
         .immediate none, .immediate none, .immediate none,
         .immediate (some (.ptr pa)), .immediate none, .immediate none],
        none, none, none⟩],
       q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  rcases hBbCase with rfl | rfl
  · -- ba = 1, bb = 0
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPaId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadA]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2,
        projectValFieldV2, projectOneElemV2]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]
      try rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPbId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadB]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)]
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_done (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [rm2_extractReturnMemoryV2_entry]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rfl)
    rfl
  · -- ba = 1, bb = 1
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPaId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadA]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2,
        projectValFieldV2, projectOneElemV2]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]
      try rfl)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, readPlaceV2]
      rw [ite_bool_true]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_false]; rotate_left; decide
      rw [hLay]
      dsimp only
      rw [hPbId]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      rw [hLoadB]; dsimp only
      rw [ite_bool_false]; rotate_left; decide
      dsimp only [evalDiscriminantOfVal]
      rw [ite_bool_false]; rotate_left; decide
      rw [ite_bool_true]; rotate_left; decide
      first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)]
      dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; try rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_step (by rfl)
    apply execOutcomeStateV2_done (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
        List.append, Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [rm2_extractReturnMemoryV2_entry]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rfl)
    rfl

private theorem tag_eq_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q) :
    WellFormedV2 (entryProgForBody Captured.program 2) q ∧
    match q.args with
    | [.ptr pa, .ptr pb] =>
      ∃ ba bb : UInt8,
        Spec.readCallerInitByte q.callerMem pa = some ba ∧
        Spec.readCallerInitByte q.callerMem pb = some bb ∧
        ∃ out : TerminalOut,
          BehaviorV2 (entryProgForBody Captured.program 2) q out ∧
          out = TerminalOut.returned ⟨.bool (Nat.beq ba.toNat bb.toNat), q.callerMem⟩
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
      cases hV0 : checkValV2 v0 (.ref .shared (.enum tagEnumTy)) <;> rw [hV0] at hArgs <;> cases hArgs
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hList] at hArgs
        dsimp only [Captured.body_2, checkArgsMatchV2, List.drop, List.take] at hArgs
        cases hV0 : checkValV2 v0 (.ref .shared (.enum tagEnumTy)) <;> rw [hV0] at hArgs
        · cases hArgs
        · cases hV1 : checkValV2 v1 (.ref .shared (.enum tagEnumTy)) <;> rw [hV1] at hArgs <;> cases hArgs
      | nil =>
        rw [hList] at hArgs hRefs
        dsimp only [Captured.body_2, checkArgsMatchV2, List.drop, List.take] at hArgs
        cases hV0 : checkValV2 v0 (.ref .shared (.enum tagEnumTy)) with
        | false => rw [hV0] at hArgs; cases hArgs
        | true =>
          rw [hV0] at hArgs
          cases hV1 : checkValV2 v1 (.ref .shared (.enum tagEnumTy)) with
          | false => rw [hV1] at hArgs; cases hArgs
          | true =>
            let ⟨pa, hva, _⟩ := checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV0
            let ⟨pb, hvb, _⟩ := checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV1
            subst hva; subst hvb
            dsimp only [Captured.body_2, refsValidInMemList, refsValidInMem, List.drop, List.take] at hRefs
            cases hRA : refValidInMem (entryMemoryWithCaller q.callerMem) .shared (.enum tagEnumTy) (.ptr pa) with
            | error _ => rw [hRA] at hRefs; cases hRefs
            | ok _ =>
              rw [hRA] at hRefs
              cases hRB : refValidInMem (entryMemoryWithCaller q.callerMem) .shared (.enum tagEnumTy) (.ptr pb) with
              | error _ => rw [hRB] at hRefs; cases hRefs
              | ok _ =>
                rcases refValidInMem_tag_inv hRA with
                  ⟨ida, allocA, ba, provA, hPaId, hFindA, hLiveA, hInBA, hGetA, hBaCase⟩
                rcases refValidInMem_tag_inv hRB with
                  ⟨idb, allocB, bb, provB, hPbId, hFindB, hLiveB, hInBB, hGetB, hBbCase⟩
                have hReadA : Spec.readCallerInitByte q.callerMem pa = some ba := by
                  unfold Spec.readCallerInitByte
                  rw [hPaId]
                  change (match findAllocation ida q.callerMem.allocations with
                    | none => none
                    | some alloc =>
                      match Trusted.MirSemantics.getElem? alloc.bytes pa.offsetBytes.toNat with
                      | some (.init b _) => some b
                      | _ => none) = some ba
                  change findAllocation ida q.callerMem.allocations = some allocA at hFindA
                  rw [hFindA]; dsimp only; rw [hGetA]
                have hReadB : Spec.readCallerInitByte q.callerMem pb = some bb := by
                  unfold Spec.readCallerInitByte
                  rw [hPbId]
                  change (match findAllocation idb q.callerMem.allocations with
                    | none => none
                    | some alloc =>
                      match Trusted.MirSemantics.getElem? alloc.bytes pb.offsetBytes.toNat with
                      | some (.init b _) => some b
                      | _ => none) = some bb
                  change findAllocation idb q.callerMem.allocations = some allocB at hFindB
                  rw [hFindB]; dsimp only; rw [hGetB]
                let expectedOut : TerminalOut :=
                  .returned ⟨.bool (Nat.beq ba.toNat bb.toNat), q.callerMem⟩
                have hInit : initStateV2 (entryProgForBody Captured.program 2) q =
                    .ok ⟨[⟨2, 0, 0, initLocalsLoop Captured.body_2 q.args 0 Captured.body_2.locals,
                      none, none, none⟩],
                      q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
                  apply initStateV2_ok_of (p := entryProgForBody Captured.program 2) (q := q)
                    (body := Captured.body_2) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
                    (by decide) (by decide) (by decide) (by decide)
                  · exact hArgsOrig
                  · exact hRefsOrig
                  · exact hDisj
                have hLocs : initLocalsLoop Captured.body_2 q.args 0 Captured.body_2.locals =
                    [.immediate none, .immediate (some (.ptr pa)), .immediate (some (.ptr pb)),
                     .dead, .dead, .dead, .immediate none, .immediate none, .immediate none,
                     .immediate none, .immediate none, .immediate none] := by
                  rw [hList]; rfl
                have hAdm : enumAdmitted tagEnumTy = true := by decide
                have hLay : layoutOfTyV2 (.enum tagEnumTy) = some (intLayout .i8) := by
                  rfl
                have hLoadA :
                    loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.enum tagEnumTy)
                      ⟨ida, pa.offsetBytes.toNat⟩ =
                    .ok (some (.enumVal tagEnumTy (if ba = 0 then 0 else 1))) := by
                  unfold loadIndirectV2
                  rw [hLay]
                  dsimp only [intLayout]
                  unfold readBytes
                  rw [hFindA]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; rfl
                  have hAlA : isAligned allocA pa.offsetBytes.toNat 0 = true := by
                    unfold isAligned
                    change (Nat.ble 0 allocA.alignLog2 && Nat.beq (pa.offsetBytes.toNat % 1) 0) = true
                    rw [Nat.mod_one, Nat.beq_refl, Nat.ble_eq.mpr (Nat.zero_le _)]
                    rfl
                  rw [ite_bool_false]; rotate_left; (rw [hLiveA, hInBA, hAlA]; rfl)
                  rw [getElem_drop_take_1 hGetA]
                  rcases hBaCase with rfl | rfl <;> rfl
                have hLoadB :
                    loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.enum tagEnumTy)
                      ⟨idb, pb.offsetBytes.toNat⟩ =
                    .ok (some (.enumVal tagEnumTy (if bb = 0 then 0 else 1))) := by
                  unfold loadIndirectV2
                  rw [hLay]
                  dsimp only [intLayout]
                  unfold readBytes
                  rw [hFindB]
                  dsimp only
                  rw [ite_bool_false]; rotate_left; rfl
                  have hAlB : isAligned allocB pb.offsetBytes.toNat 0 = true := by
                    unfold isAligned
                    change (Nat.ble 0 allocB.alignLog2 && Nat.beq (pb.offsetBytes.toNat % 1) 0) = true
                    rw [Nat.mod_one, Nat.beq_refl, Nat.ble_eq.mpr (Nat.zero_le _)]
                    rfl
                  rw [ite_bool_false]; rotate_left; (rw [hLiveB, hInBB, hAlB]; rfl)
                  rw [getElem_drop_take_1 hGetB]
                  rcases hBbCase with rfl | rfl <;> rfl
                have hExec : execProgV2 (entryProgForBody Captured.program 2) 30 q (fun o => o = expectedOut) := by
                  unfold execProgV2
                  rw [hInit, hLocs]
                  -- bb0 stmt 0..1: storageLive 3, storageLive 4
                  apply execOutcomeStateV2_step (by rfl)
                  apply execOutcomeStateV2_step (by rfl)
                  -- bb0 stmt 2: assign 4 (useRetag (copy 1))
                  apply execOutcomeStateV2_step (by
                    dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
                      List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
                      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
                    rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
                    dsimp only
                    rw [ite_bool_false]; rotate_left; decide
                    have hRV : refsValidInMem (entryMemoryWithCaller q.callerMem)
                        (.ref .shared (.enum tagEnumTy)) (.ptr pa) = true := by
                      dsimp only [refsValidInMem]; rw [hRA]
                    rw [ite_bool_false (by rw [hRV]; rfl)]
                    dsimp only
                    repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
                    try dsimp only
                    rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]
                    try rfl)
                  -- bb0 stmt 3: storageLive 5
                  apply execOutcomeStateV2_step (by rfl)
                  -- bb0 stmt 4: assign 5 (useRetag (copy 2))
                  apply execOutcomeStateV2_step (by
                    dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
                      List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
                      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2]
                    rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
                    dsimp only
                    rw [ite_bool_false]; rotate_left; decide
                    have hRV : refsValidInMem (entryMemoryWithCaller q.callerMem)
                        (.ref .shared (.enum tagEnumTy)) (.ptr pb) = true := by
                      dsimp only [refsValidInMem]; rw [hRB]
                    rw [ite_bool_false (by rw [hRV]; rfl)]
                    dsimp only
                    repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
                    try dsimp only
                    rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]
                    try rfl)
                  -- bb0 stmt 5: assign 3 (aggregateTuple [move 4, move 5])
                  apply execOutcomeStateV2_step (by
                    dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
                      List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
                      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalArgOperandsV2, evalOperandToSlotV2]
                    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
                    dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
                    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
                    dsimp only [argValues]
                    have hV0' : checkValV2 (.ptr pa) (.ref .shared (.enum { id := 933338508, discrWidth := .i8, discrSigned := false, tagRepr := .scalar .i8 false, discriminants := [0, 1] })) = true := hV0
                    have hV1' : checkValV2 (.ptr pb) (.ref .shared (.enum { id := 933338508, discrWidth := .i8, discrSigned := false, tagRepr := .scalar .i8 false, discriminants := [0, 1] })) = true := hV1
                    have hCL : checkValV2List [.ptr pa, .ptr pb] [.ref .shared (.enum { id := 933338508, discrWidth := .i8, discrSigned := false, tagRepr := .scalar .i8 false, discriminants := [0, 1] }), .ref .shared (.enum { id := 933338508, discrWidth := .i8, discrSigned := false, tagRepr := .scalar .i8 false, discriminants := [0, 1] })] = true := by
                      dsimp only [checkValV2List]; rw [hV0', hV1']; rfl
                    have hChkTuple : checkValV2 (.tuple [.ptr pa, .ptr pb])
                        (.tuple [.ref .shared (.enum { id := 933338508, discrWidth := .i8, discrSigned := false, tagRepr := .scalar .i8 false, discriminants := [0, 1] }), .ref .shared (.enum { id := 933338508, discrWidth := .i8, discrSigned := false, tagRepr := .scalar .i8 false, discriminants := [0, 1] })]) = true := by
                      unfold checkValV2; dsimp only [checkValV2List]; rw [hV0', hV1']; rfl
                    simp only [hCL]
                    rw [ite_bool_false]; rotate_left; rfl
                    dsimp only
                    repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
                    try dsimp only
                    rw [writePlaceDestV2_immediate_ok hChkTuple (by rfl) (by rfl)]; rfl)
                  -- bb0 stmt 6..8: storageDead 5, storageDead 4, nop
                  apply execOutcomeStateV2_step (by rfl)
                  apply execOutcomeStateV2_step (by rfl)
                  apply execOutcomeStateV2_step (by rfl)
                  -- bb0 stmt 9: assign 9 (copy 3.0)
                  apply execOutcomeStateV2_step (by
                    dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_2,
                      List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
                      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2, readPlaceV2,
                      projectValFieldV2, projectOneElemV2]
                    rw [ite_bool_false]; rotate_left; decide
                    rw [ite_bool_false]; rotate_left; decide
                    dsimp only
                    rw [ite_bool_false]; rotate_left; decide
                    dsimp only
                    repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
                    try dsimp only
                    rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
                  -- Split concretely on ba ∈ {0, 1} into dedicated tail lemmas
                  -- to stay comfortably under the default heartbeat budget.
                  rcases hBaCase with rfl | rfl
                  · exact tag_eq_tail_ba0 hCM hV1 hPaId hPbId hLay hLoadA hLoadB hBbCase
                  · exact tag_eq_tail_ba1 hCM hV1 hPaId hPbId hLay hLoadA hLoadB hBbCase
                have hRes := spec_and_behaviorV2_of_exec_eq hExec
                exact ⟨hRes.1, ba, bb, hReadA, hReadB, expectedOut, hRes.2.1, rfl⟩

/-! ## Body 3: `matches_pattern` -/

private theorem drop_take_four_of_getElem {off : Nat} {bs : List AllocByte}
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

private theorem getElem_four_of_drop_take_four {off : Nat} {bs : List AllocByte}
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

private theorem decodeValV2_u8x4_init_inv {x0 x1 x2 x3 : AllocByte} {v : Val}
    (h : decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4) [x0, x1, x2, x3] = .ok (some v)) :
    ∃ b0 b1 b2 b3 p0 p1 p2 p3,
      x0 = .init b0 p0 ∧ x1 = .init b1 p1 ∧ x2 = .init b2 p2 ∧ x3 = .init b3 p3 := by
  rw [decodeValV2_u8_array] at h
  try dsimp only [layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout] at h
  rw [ite_bool_false] at h; rotate_left; rfl
  dsimp only [decodeFixedChunks, List.take, List.drop] at h
  rw [ite_bool_true] at h; rotate_left; rfl
  cases x0 with
  | uninit =>
    cases x1 <;> cases x2 <;> cases x3 <;>
      simp only [decodeValV2_u8_uninit, decodeValV2_u8_init] at h <;> cases h
  | init b0 p0 =>
    cases x1 with
    | uninit =>
      cases x2 <;> cases x3 <;>
        simp only [decodeValV2_u8_uninit, decodeValV2_u8_init] at h <;> cases h
    | init b1 p1 =>
      cases x2 with
      | uninit =>
        cases x3 <;>
          simp only [decodeValV2_u8_uninit, decodeValV2_u8_init] at h <;> cases h
      | init b2 p2 =>
        cases x3 with
        | uninit =>
          simp only [decodeValV2_u8_uninit, decodeValV2_u8_init] at h; cases h
        | init b3 p3 => exact ⟨b0, b1, b2, b3, p0, p1, p2, p3, rfl, rfl, rfl, rfl⟩

private theorem refValidInMem_u8x4_inv {m : MemoryState} {p : PtrVal}
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
    (by decide), layoutOfTyV2_u8x4] at hRef
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
            rcases getElem_four_of_drop_take_four hLe hS with ⟨hg0, hg1, hg2, hg3⟩
            rw [ite_bool_false] at hRef; rotate_left; rfl
            cases hD : decodeValV2 profileV2TargetEndian (.array (.int .i8 false) 4) [x0, x1, x2, x3] with
            | error k => rw [hD] at hRef; cases hRef
            | ok ov =>
              cases ov with
              | none => rw [hD] at hRef; cases hRef
              | some v =>
                rcases decodeValV2_u8x4_init_inv hD with ⟨b0, b1, b2, b3, p0, p1, p2, p3, rfl, rfl, rfl, rfl⟩
                exact ⟨aid, a, b0, b1, b2, b3, p0, p1, p2, p3,
                  rfl, hFind, hLive, hInB, hg0, hg1, hg2, hg3⟩

private theorem arrayValEq_u8_byte (x y : UInt8) :
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

private theorem matches_pattern_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_3 q) :
    WellFormedV2 (entryProgForBody Captured.program 3) q ∧
    match q.args with
    | [.ptr pa] =>
      ∃ b0 b1 b2 b3 : UInt8,
        Spec.readCallerFourInitBytes q.callerMem pa = some (b0, b1, b2, b3) ∧
        ∃ out : TerminalOut,
          BehaviorV2 (entryProgForBody Captured.program 3) q out ∧
          out = TerminalOut.returned
            ⟨.bool (Nat.beq b0.toNat 1 && Nat.beq b1.toNat 2 &&
                    Nat.beq b2.toNat 3 && Nat.beq b3.toNat 4),
             q.callerMem⟩
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
      dsimp only [Captured.body_3, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.ref .shared (.array (.int .i8 false) 4)) <;>
        rw [hV0] at hArgs <;> cases hArgs
    | nil =>
      rw [hList] at hArgs hRefs
      dsimp only [Captured.body_3, checkArgsMatchV2, List.drop, List.take] at hArgs
      cases hV0 : checkValV2 v0 (.ref .shared (.array (.int .i8 false) 4)) with
      | false => rw [hV0] at hArgs; cases hArgs
      | true =>
        let ⟨pa, hva, _⟩ := checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV0
        subst hva
        dsimp only [Captured.body_3, refsValidInMemList, refsValidInMem, List.drop, List.take] at hRefs
        cases hRA : refValidInMem (entryMemoryWithCaller q.callerMem) .shared
            (.array (.int .i8 false) 4) (.ptr pa) with
        | error _ => rw [hRA] at hRefs; cases hRefs
        | ok _ =>
          rcases refValidInMem_u8x4_inv hRA with
            ⟨ida, allocA, b0, b1, b2, b3, p0, p1, p2, p3, hPaId, hFindA, hLiveA, hInBA,
              hg0, hg1, hg2, hg3⟩
          have hRead4 : Spec.readCallerFourInitBytes q.callerMem pa = some (b0, b1, b2, b3) := by
            unfold Spec.readCallerFourInitBytes
            rw [hPaId]
            change findAllocation ida q.callerMem.allocations = some allocA at hFindA
            dsimp only
            rw [hFindA]; dsimp only; rw [hg0, hg1, hg2, hg3]
          let roAid := (entryMemoryWithCaller q.callerMem).nextAllocId
          have hRoGt : maxAllocId q.callerMem.allocations < roAid := by
            change maxAllocId q.callerMem.allocations <
              Nat.max entryMemory.nextAllocId (maxAllocAndProvId q.callerMem.allocations + 1)
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_left _ _))
              (Nat.le_max_right _ _)
          have hIdaLe : ida ≤ maxAllocId q.callerMem.allocations := by
            have hMemA : allocA ∈ q.callerMem.allocations := findAllocation_mem hFindA
            have hEqId : allocA.allocId = ida := findAllocation_allocId_eq hFindA
            exact hEqId ▸ allocId_le_maxAllocId hMemA
          have hRoNeIda : roAid ≠ ida := Nat.ne_of_gt (Nat.lt_of_le_of_lt hIdaLe hRoGt)
          let roAlloc : Allocation := {
            allocId := roAid
            bytes := [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
            alignLog2 := 0
            mutability := .shared
            live := true
          }
          let resBool := Nat.beq b0.toNat 1 && Nat.beq b1.toNat 2 &&
              Nat.beq b2.toNat 3 && Nat.beq b3.toNat 4
          let expectedOut : TerminalOut := .returned ⟨.bool resBool, q.callerMem⟩
          have hInit : initStateV2 (entryProgForBody Captured.program 3) q =
              .ok ⟨[⟨3, 0, 0, initLocalsLoop Captured.body_3 q.args 0 Captured.body_3.locals,
                none, none, none⟩],
                q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
            apply initStateV2_ok_of (p := entryProgForBody Captured.program 3) (q := q)
              (body := Captured.body_3) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
              (by decide) (by decide) (by decide) (by decide)
            · exact hArgsOrig
            · exact hRefsOrig
            · exact hDisj
          have hLocs : initLocalsLoop Captured.body_3 q.args 0 Captured.body_3.locals =
              [.immediate none, .immediate (some (.ptr pa)), .dead, .dead, .immediate none,
               .immediate none] := by
            rw [hList]; rfl
          have hExec : execProgV2 (entryProgForBody Captured.program 3) 20 q (fun o => o = expectedOut) := by
            unfold execProgV2
            rw [hInit, hLocs]
            -- bb0 stmt 0: storageLive 2
            apply execOutcomeStateV2_step (by rfl)
            -- bb0 stmt 1: assign 2 (ref .shared (*1))
            apply execOutcomeStateV2_step (by
              dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_3,
                List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
                stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalRefRvalueV2]
              rw [hRA]
              dsimp only
              rw [ite_bool_false]; rotate_left; decide
              rw [ite_bool_false]; rotate_left; decide
              dsimp only
              repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
              try dsimp only
              rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
            -- bb0 stmt 2: storageLive 3
            apply execOutcomeStateV2_step (by rfl)
            -- bb0 stmt 3: assign 5 (useRetag (rodataRef [1,2,3,4] 0 0 none))
            apply execOutcomeStateV2_step (by
              dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_3,
                List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
                stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
                evalRodataRefConstV2, allocRodataMemory, MemoryState.reserveAllocId,
                rodataByteToAllocByte, List.map]
              rw [ite_bool_false]; rotate_left; decide
              rw [ite_bool_false]; rotate_left; decide
              rw [ite_bool_false]; rotate_left; decide
              rw [show (entryMemoryWithCaller q.callerMem).allocations = q.callerMem.allocations from rfl]
              have hFindRo : findAllocation roAid (roAlloc :: q.callerMem.allocations) = some roAlloc := by
                change (if Nat.beq roAid roAid then some roAlloc else _) = some roAlloc
                rw [Nat.beq_refl]; rfl
              have hRefRoMem : refValidInMem
                  { nextAllocId := roAid + 1, allocations := roAlloc :: q.callerMem.allocations }
                  .shared (.array (.int .i8 false) 4) (.ptr ⟨some roAid, UInt64.ofNat 0, .isize⟩) = .ok () := by
                dsimp only [refValidInMem, layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout]
                rw [hFindRo]
                rfl
              rw [hRefRoMem]
              dsimp only
              have hRoValid : refsValidInMem
                  { nextAllocId := roAid + 1, allocations := roAlloc :: q.callerMem.allocations }
                  (.ref .shared (.array (.int .i8 false) 4))
                  (.ptr ⟨some roAid, UInt64.ofNat 0, .isize⟩) = true := by
                dsimp only [refsValidInMem]; rw [hRefRoMem]
              rw [ite_bool_false]; rotate_left; decide
              rw [ite_bool_false (by rw [hRoValid]; rfl)]
              dsimp only
              repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
              try dsimp only
              rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]
              try rfl)
            -- bb0 stmt 4: assign 3 (ref .shared (*5))
            apply execOutcomeStateV2_step (by
              dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_3,
                List.append, Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
                stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalRefRvalueV2]
              have hFindRo : findAllocation roAid (roAlloc :: q.callerMem.allocations) = some roAlloc := by
                change (if Nat.beq roAid roAid then some roAlloc else _) = some roAlloc
                rw [Nat.beq_refl]; rfl
              have hRefRoMem : refValidInMem
                  { nextAllocId := roAid + 1, allocations := roAlloc :: q.callerMem.allocations }
                  .shared (.array (.int .i8 false) 4) (.ptr ⟨some roAid, UInt64.ofNat 0, .isize⟩) = .ok () := by
                dsimp only [refValidInMem, layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout]
                rw [hFindRo]
                rfl
              rw [ite_bool_false]; rotate_left; decide
              rw [ite_bool_false]; rotate_left; decide
              rw [hRefRoMem]
              dsimp only
              repeat (rw [ite_bool_false]; rotate_left; first | rfl | decide)
              try dsimp only
              rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]
              try rfl)
            -- bb0 terminator: coreCall .arrayEq (.int .i8 false) 4 [move 2,
            -- move 3] -> 0 goto 1
            apply execOutcomeStateV2_step (by
              dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_3,
                List.append, Trusted.MirSemantics.getElem?]
              rw [ite_bool_true]; rotate_left; decide
              dsimp only [evalTerminatorV2, Trusted.MirSemantics.getElem?]
              rw [ite_bool_false]; rotate_left; decide
              dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
              rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
              dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
              rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
              dsimp only [argValues, execCoreCallOpWithMemOutcome,
                execAllocCoreCallOutcome, execAllocCoreCallInfallible,
                execCoreCallWithMemOutcome, execCoreCallOp]
              rw [ite_bool_false]; rotate_left; decide
              have hFindRo : findAllocation roAid (roAlloc :: q.callerMem.allocations) = some roAlloc := by
                change (if Nat.beq roAid roAid then some roAlloc else _) = some roAlloc
                rw [Nat.beq_refl]; rfl
              have hFindACons : findAllocation ida (roAlloc :: q.callerMem.allocations) = some allocA := by
                rw [findAllocation_cons_ne hRoNeIda]; exact hFindA
              have hAlA : isAligned allocA pa.offsetBytes.toNat 0 = true := by
                unfold isAligned
                change (Nat.ble 0 allocA.alignLog2 && Nat.beq (pa.offsetBytes.toNat % 1) 0) = true
                rw [Nat.mod_one, Nat.beq_refl, Nat.ble_eq.mpr (Nat.zero_le _)]
                rfl
              have hRefPa : refValidInMem
                  { nextAllocId := roAid + 1, allocations := roAlloc :: q.callerMem.allocations }
                  .shared (.array (.int .i8 false) 4) (.ptr pa) = .ok () := by
                unfold refValidInMem
                dsimp only
                rw [ite_bool_false (b := !isSupportedV2PointeeTy (.array (.int .i8 false) 4) &&
      !isHeapHandleTyV2 (.array (.int .i8 false) 4))
                  (by decide), layoutOfTyV2_u8x4]
                dsimp only
                rw [hPaId]; dsimp only
                rw [hFindACons]; dsimp only
                rw [ite_bool_false]; rotate_left; ((try dsimp only [intLayout]); rw [hLiveA, hInBA, hAlA]; rfl)
                rw [ite_bool_false]; rotate_left; rfl
                try dsimp only [intLayout]
                rw [drop_take_four_of_getElem hg0 hg1 hg2 hg3]
                rw [decodeValV2_u8x4_init b0 b1 b2 b3 p0 p1 p2 p3]
              have hRefRo : refValidInMem
                  { nextAllocId := roAid + 1, allocations := roAlloc :: q.callerMem.allocations }
                  .shared (.array (.int .i8 false) 4) (.ptr ⟨some roAid, UInt64.ofNat 0, .isize⟩) = .ok () := by
                dsimp only [refValidInMem, layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout]
                rw [hFindRo]
                rfl
              have hLoadPa : loadIndirectV2
                  { nextAllocId := roAid + 1, allocations := roAlloc :: q.callerMem.allocations }
                  (.array (.int .i8 false) 4) ⟨ida, pa.offsetBytes.toNat⟩ =
                  .ok (some (.array [
                    .scalar ⟨.i8, false, BitVec.ofNat 128 b0.toNat⟩,
                    .scalar ⟨.i8, false, BitVec.ofNat 128 b1.toNat⟩,
                    .scalar ⟨.i8, false, BitVec.ofNat 128 b2.toNat⟩,
                    .scalar ⟨.i8, false, BitVec.ofNat 128 b3.toNat⟩])) := by
                unfold loadIndirectV2
                dsimp only [layoutOfTyV2_u8x4, layoutOfTyV2_u8x3, layoutOfTyV2_u8x2, layoutOfTyV2_u8, layoutOfTyV2_u16,
    layoutOfArrayV2, layoutOfTy, intLayout]
                unfold readBytes
                rw [hFindACons]; dsimp only
                rw [ite_bool_false]; rotate_left; rfl
                rw [ite_bool_false]; rotate_left; (rw [hLiveA, hInBA, hAlA]; rfl)
                rw [drop_take_four_of_getElem hg0 hg1 hg2 hg3]
                exact decodeValV2_u8x4_init b0 b1 b2 b3 p0 p1 p2 p3
              have hLoadRo : loadIndirectV2
                  { nextAllocId := roAid + 1, allocations := roAlloc :: q.callerMem.allocations }
                  (.array (.int .i8 false) 4) ⟨roAid, (UInt64.ofNat 0).toNat⟩ =
                  .ok (some (.array [
                    .scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
                    .scalar ⟨.i8, false, BitVec.ofNat 128 2⟩,
                    .scalar ⟨.i8, false, BitVec.ofNat 128 3⟩,
                    .scalar ⟨.i8, false, BitVec.ofNat 128 4⟩])) := by
                unfold loadIndirectV2 readBytes
                rw [hFindRo]
                rfl
              rw [hRefPa, hRefRo]
              dsimp only
              rw [hPaId]; dsimp only; rw [hLoadPa, hLoadRo]
              dsimp only
              have hEqList : valEqListWith (arrayValEqV2 (.int .i8 false))
                  [.scalar ⟨.i8, false, BitVec.ofNat 128 b0.toNat⟩,
                   .scalar ⟨.i8, false, BitVec.ofNat 128 b1.toNat⟩,
                   .scalar ⟨.i8, false, BitVec.ofNat 128 b2.toNat⟩,
                   .scalar ⟨.i8, false, BitVec.ofNat 128 b3.toNat⟩]
                  [.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
                   .scalar ⟨.i8, false, BitVec.ofNat 128 2⟩,
                   .scalar ⟨.i8, false, BitVec.ofNat 128 3⟩,
                   .scalar ⟨.i8, false, BitVec.ofNat 128 4⟩] =
                  .ok (Nat.beq b0.toNat 1 && Nat.beq b1.toNat 2 &&
                       Nat.beq b2.toNat 3 && Nat.beq b3.toNat 4) := by
                dsimp only [valEqListWith]
                rw [show BitVec.ofNat 128 1 = BitVec.ofNat 128 (1 : UInt8).toNat from rfl,
                    show BitVec.ofNat 128 2 = BitVec.ofNat 128 (2 : UInt8).toNat from rfl,
                    show BitVec.ofNat 128 3 = BitVec.ofNat 128 (3 : UInt8).toNat from rfl,
                    show BitVec.ofNat 128 4 = BitVec.ofNat 128 (4 : UInt8).toNat from rfl]
                rw [arrayValEq_u8_byte b0 1, arrayValEq_u8_byte b1 2,
                    arrayValEq_u8_byte b2 3, arrayValEq_u8_byte b3 4]
                rw [show (1 : UInt8).toNat = 1 from rfl, show (2 : UInt8).toNat = 2 from rfl,
                    show (3 : UInt8).toNat = 3 from rfl, show (4 : UInt8).toNat = 4 from rfl]
                cases Nat.beq b0.toNat 1 <;> cases Nat.beq b1.toNat 2 <;>
                  cases Nat.beq b2.toNat 3 <;> cases Nat.beq b3.toNat 4 <;> rfl
              rw [hEqList]
              dsimp only
              rw [writePlaceV2_immediate_ok (by rfl) (by rfl) (by rfl)]
              rfl)
            -- bb1: storageDead 3, storageDead 2
            apply execOutcomeStateV2_step (by rfl)
            apply execOutcomeStateV2_step (by rfl)
            -- bb1: return_
            apply execOutcomeStateV2_done (by
              dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_3,
                List.append, Trusted.MirSemantics.getElem?]
              rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
                (by rfl) (by rfl) (by rfl) (by rfl)]
              rw [rm2_extractReturnMemoryV2_cons_shared]; rotate_left; rfl
              rw [extractCallerMemory_cons_fresh hRoGt]
              rw [extractCallerMemory_entry q.callerMem hCM]
              rfl)
            rfl
          have hRes := spec_and_behaviorV2_of_exec_eq hExec
          exact ⟨hRes.1, b0, b1, b2, b3, hRead4, expectedOut, hRes.2.1, rfl⟩

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
      exact (pack_le_rev_correct q hValid).1
    | succ d1 =>
      cases d1 with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        refine ⟨rfl, by decide, ?_⟩
        intro q hValid _
        exact (repeat_unsize_len_correct q hValid).1
      | succ d2 =>
        cases d2 with
        | zero =>
          change some Captured.body_2 = some body at hBody
          cases hBody
          refine ⟨rfl, by decide, ?_⟩
          intro q hValid _
          exact (tag_eq_correct q hValid).1
        | succ d3 =>
          cases d3 with
          | zero =>
            change some Captured.body_3 = some body at hBody
            cases hBody
            refine ⟨rfl, by decide, ?_⟩
            intro q hValid _
            exact (matches_pattern_correct q hValid).1
          | succ _ =>
            change none = some body at hBody
            cases hBody
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hValid
      exact (pack_le_rev_correct q hValid).2
    · intro q hValid
      exact (repeat_unsize_len_correct q hValid).2
    · intro q hValid
      exact (tag_eq_correct q hValid).2
    · intro q hValid
      exact (matches_pattern_correct q hValid).2

end Proof
