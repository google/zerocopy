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

/-! `CrateTheoremV2` for a crate that capture shards and reorders. After the
reorder the bodies are: 0 `<Tag as AaaFake>::fake_eq`, 1
`<Tag as PartialEq>::eq`, 2-19 `fake_caller_00` .. `fake_caller_17` (one
lemma, `fake_caller_correct`), and 20 `tag_ne`. `eq_run` steps body 1 under
arbitrary caller frames, so it serves both `eq` as an entry point and the
callee of `tag_ne`'s `callNe`. That `callNe` must name body 1: the step that
pushes the callee frame (`pb_evalCallV2_ok` with `calleeBody := eqBody`) does
not elaborate against any other body. -/

/-! ## Profile v2 Return Memory -/

theorem rm2_natNotElem_false_of_mem {x : Nat} {xs : List Nat}
    (h : x ∈ xs) : natNotElem x xs = false := by
  induction h with
  | head _ =>
    unfold natNotElem
    rw [Nat.beq_refl]
    rfl
  | tail _ _ ih =>
    unfold natNotElem
    rw [ih, Bool.and_false]

theorem rm2_mem_allocIdsOf {a : Allocation} {l : List Allocation}
    (h : a ∈ l) : a.allocId ∈ allocIdsOf l := by
  induction h with
  | head _ => unfold allocIdsOf; exact .head _
  | tail _ _ ih => unfold allocIdsOf; exact .tail _ ih

theorem rm2_calleeLive_nil_of_sub {ids f : List AllocId} :
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
theorem rm2_extractReturnMemoryV2_eq {cm : CallerMemory}
    {mem : MemoryState} (locals : List LocalSlot)
    (h : ∀ a, a ∈ mem.allocations → a.allocId ∈ allocIdsOf cm.allocations) :
    extractReturnMemoryV2 cm mem locals = extractCallerMemory cm mem := by
  unfold extractReturnMemoryV2
  rw [rm2_calleeLive_nil_of_sub h, List.append_nil]

theorem rm2_extractReturnMemoryV2_entry (cm : CallerMemory)
    (locals : List LocalSlot) :
    extractReturnMemoryV2 cm (entryMemoryWithCaller cm) locals =
      extractCallerMemory cm (entryMemoryWithCaller cm) :=
  rm2_extractReturnMemoryV2_eq locals (fun _ ha => rm2_mem_allocIdsOf ha)

theorem rm2_calleeLive_nil_of_dead {ids f : List AllocId} :
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
theorem rm2_extractReturnMemoryV2_eq_dead {cm : CallerMemory}
    {mem : MemoryState} (locals : List LocalSlot)
    (h : ∀ a, a ∈ mem.allocations →
      a.allocId ∈ allocIdsOf cm.allocations ∨ a.live = false) :
    extractReturnMemoryV2 cm mem locals = extractCallerMemory cm mem := by
  unfold extractReturnMemoryV2
  rw [rm2_calleeLive_nil_of_dead h, List.append_nil]

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

theorem checkValV2_scalar_inv {v : Val} {w : IntWidth} {s : Bool}
    (h : checkValV2 v (.int w s) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ ScalarVal.wf ⟨w, s, bits⟩ = true := by
  have h1 : checkVal v (.int w s) = true := by
    cases v with
    | scalar sv => unfold checkValV2 at h; exact h
    | _ => first | cases h | (rename_i o; cases o <;> cases h)
  exact let ⟨bits, hv, hTrunc⟩ := checkVal_int_iff.mp h1; ⟨bits, hv, beq_iff_eq.mpr hTrunc⟩

/-! ## Reference, Byte, and List Helpers -/

theorem checkValV2_ref_ptr_inv {reqMut : Mutability} {pt : MirTy}
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
    | _ => first | cases h | (rename_i o; cases o <;> cases h)

/-! ## Call Helper -/

theorem pb_evalCallV2_ok {p : Program} {body calleeBody : Body} {frame : FrameState}
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

/-! ## Fuel-Free Stepping -/

/-- `post` holds on the outcome reached from `s` after finitely many steps,
none of which faults. -/
abbrev Runs (p : Program) (post : TerminalOut → Prop) (s : State) : Prop :=
  ∃ fuel, execOutcomeStateV2 p post (fun _ => False) fuel s

theorem runs_step {p : Program} {s s' : State} {post : TerminalOut → Prop}
    (hStep : evalStepV2 p s = .step s') (hRest : Runs p post s') :
    Runs p post s :=
  let ⟨fuel, h⟩ := hRest
  ⟨fuel + 1, execOutcomeStateV2_step hStep h⟩

theorem runs_done {p : Program} {s : State} {out : TerminalOut}
    {post : TerminalOut → Prop}
    (hDone : evalStepV2 p s = .done out) (hPost : post out) :
    Runs p post s :=
  ⟨_, execOutcomeStateV2_done (fuel := 0) hDone hPost⟩

theorem execProgV2_of_runs {p : Program} {q : Query} {s₀ : State}
    {post : TerminalOut → Prop} (hInit : initStateV2 p q = .ok s₀)
    (hRuns : Runs p post s₀) : ∃ fuel, execProgV2 p fuel q post :=
  let ⟨fuel, h⟩ := hRuns
  ⟨fuel, by unfold execProgV2; rw [hInit]; exact h⟩

/-! ## `Tag` -/

abbrev tagE : EnumTy :=
  { id := 933338508
    discrWidth := .isize
    discrSigned := true
    tagRepr := .scalar .i8 false
    discriminants := [0, 1] }

abbrev tagTy : MirTy := .enum tagE

abbrev refTagTy : MirTy := .ref .shared tagTy

abbrev im (v : Val) : LocalSlot := .immediate (some v)
abbrev N : LocalSlot := .immediate none
abbrev D : LocalSlot := .dead

/-! ## Entry Argument Inversion -/

theorem checkValV2_tag_inv {v : Val} (h : checkValV2 v tagTy = true) :
    ∃ x : Nat, v = .enumVal tagE x ∧ (x = 0 ∨ x = 1) := by
  have h1 : checkVal v tagTy = true := by
    cases v with
    | enumVal e x => unfold checkValV2 at h; exact h
    | _ => first | cases h | (rename_i o; cases o <;> cases h)
  let ⟨_, idx, hv⟩ := checkVal_enum_iff.mp h1
  refine ⟨idx.val, hv, ?_⟩
  match idx with
  | ⟨0, _⟩ => exact .inl rfl
  | ⟨1, _⟩ => exact .inr rfl
  | ⟨n + 2, hn⟩ => exact absurd hn (Nat.not_lt.mpr (Nat.le_add_left 2 n))

theorem tag_val_args_inv {body : Body} {q : Query}
    (hParams : (body.locals.drop 1).take body.argumentCount = [tagTy, tagTy])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ x y : Nat, q.args = [.enumVal tagE x, .enumVal tagE y] ∧
      (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1) := by
  let ⟨_, hArgs, _, _⟩ := hValid
  change checkArgsMatchV2 q.args ((body.locals.drop 1).take body.argumentCount) = true at hArgs
  rw [hParams] at hArgs
  cases hList : q.args with
  | nil => rw [hList] at hArgs; cases hArgs
  | cons v0 rest =>
    rw [hList] at hArgs
    cases rest with
    | nil =>
      dsimp only [checkArgsMatchV2] at hArgs
      cases hV0 : checkValV2 v0 tagTy <;> rw [hV0] at hArgs <;> cases hArgs
    | cons v1 rest2 =>
      dsimp only [checkArgsMatchV2] at hArgs
      cases hV0 : checkValV2 v0 tagTy with
      | false => rw [hV0] at hArgs; cases hArgs
      | true =>
        rw [hV0] at hArgs
        cases hV1 : checkValV2 v1 tagTy with
        | false => rw [hV1] at hArgs; cases hArgs
        | true =>
          rw [hV1] at hArgs
          cases rest2 with
          | cons _ _ => cases hArgs
          | nil =>
            let ⟨x, hx, hx01⟩ := checkValV2_tag_inv hV0
            let ⟨y, hy, hy01⟩ := checkValV2_tag_inv hV1
            subst hx; subst hy
            exact ⟨x, y, rfl, hx01, hy01⟩

theorem tag_ref_args_inv {body : Body} {q : Query}
    (hParams : (body.locals.drop 1).take body.argumentCount = [refTagTy, refTagTy])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ pa pb : PtrVal,
      q.args = [.ptr pa, .ptr pb] ∧
      checkValV2 (.ptr pa) refTagTy = true ∧
      checkValV2 (.ptr pb) refTagTy = true ∧
      refValidInMem (entryMemoryWithCaller q.callerMem) .shared tagTy (.ptr pa) = .ok () ∧
      refValidInMem (entryMemoryWithCaller q.callerMem) .shared tagTy (.ptr pb) = .ok () := by
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
      cases hV0 : checkValV2 v0 refTagTy <;> rw [hV0] at hArgs <;> cases hArgs
    | cons v1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hList] at hArgs
        dsimp only [checkArgsMatchV2] at hArgs
        cases hV0 : checkValV2 v0 refTagTy <;> rw [hV0] at hArgs
        · cases hArgs
        · cases hV1 : checkValV2 v1 refTagTy <;> rw [hV1] at hArgs <;> cases hArgs
      | nil =>
        rw [hList] at hArgs hRefs
        dsimp only [checkArgsMatchV2] at hArgs
        cases hV0 : checkValV2 v0 refTagTy with
        | false => rw [hV0] at hArgs; cases hArgs
        | true =>
          rw [hV0] at hArgs
          cases hV1 : checkValV2 v1 refTagTy with
          | false => rw [hV1] at hArgs; cases hArgs
          | true =>
            let ⟨pa, hva, _⟩ := checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV0
            let ⟨pb, hvb, _⟩ := checkValV2_ref_ptr_inv (hNonSlice := fun _ h => by cases h) hV1
            subst hva; subst hvb
            dsimp only [refsValidInMemList, refsValidInMem] at hRefs
            cases hRA : refValidInMem (entryMemoryWithCaller q.callerMem) .shared tagTy (.ptr pa) with
            | error _ => rw [hRA] at hRefs; cases hRefs
            | ok u =>
              rw [hRA] at hRefs
              cases hRB : refValidInMem (entryMemoryWithCaller q.callerMem) .shared tagTy (.ptr pb) with
              | error _ => rw [hRB] at hRefs; cases hRefs
              | ok u' => cases u; cases u'; exact ⟨pa, pb, rfl, hV0, hV1, hRA, hRB⟩

/-! ## `Tag` Pointee Reads -/

noncomputable def tagValB : Val → Bool
  | .enumVal e x => EnumTy.beq e tagE && (Nat.beq x 0 || Nat.beq x 1)
  | _ => false

theorem decode_tag_byte_all : ∀ n, n < 256 →
    (match decodeValV2 profileV2TargetEndian tagTy [.init (UInt8.ofNat n) none] with
     | .ok (some v) => tagValB v
     | _ => true) = true := by
  decide +kernel

theorem tagValB_true {v : Val} (h : tagValB v = true) :
    v = .enumVal tagE 0 ∨ v = .enumVal tagE 1 := by
  cases v
  case enumVal e x =>
    change (EnumTy.beq e tagE && (Nat.beq x 0 || Nat.beq x 1)) = true at h
    cases hE : EnumTy.beq e tagE with
    | false => rw [hE] at h; cases h
    | true =>
      rw [hE] at h
      have he := EnumTy.beq_iff.mp hE
      subst he
      cases h0 : Nat.beq x 0 with
      | true => exact .inl (by rw [Nat.eq_of_beq_eq_true h0])
      | false =>
        rw [h0] at h
        change Nat.beq x 1 = true at h
        exact .inr (by rw [Nat.eq_of_beq_eq_true h])
  all_goals cases h

theorem uint8_eq_ofNat_toNat (b : UInt8) : b = UInt8.ofNat b.toNat := by
  cases b with
  | ofBitVec bv =>
    change UInt8.ofBitVec bv = UInt8.ofBitVec (BitVec.ofNat 8 bv.toNat)
    apply congrArg UInt8.ofBitVec
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt bv.isLt).symm

theorem decode_tag_single {x : AllocByte} {v : Val}
    (h : decodeValV2 profileV2TargetEndian tagTy [x] = .ok (some v)) :
    v = .enumVal tagE 0 ∨ v = .enumVal tagE 1 := by
  cases x with
  | uninit => cases h
  | init b prov =>
    have hN := decode_tag_byte_all b.toNat b.toBitVec.isLt
    have h' : decodeValV2 profileV2TargetEndian tagTy
        [.init (UInt8.ofNat b.toNat) none] = .ok (some v) := by
      rw [← uint8_eq_ofNat_toNat b]
      exact h
    rw [h'] at hN
    exact tagValB_true hN

theorem layoutOfTyV2_tag : layoutOfTyV2 tagTy = some ⟨1, 0⟩ := rfl

theorem drop_take_one_of_lt {α : Type} :
    ∀ (off : Nat) (bs : List α), off < bs.length →
      ∃ x, (bs.drop off).take 1 = [x]
  | 0, [], h => absurd h (Nat.not_lt_zero _)
  | 0, x :: _, _ => ⟨x, rfl⟩
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | k + 1, _ :: tl, h => drop_take_one_of_lt k tl (Nat.lt_of_succ_lt_succ h)

/-- A valid shared `&Tag` points at a live byte that loads as one of the two
`Tag` variants. -/
theorem tag_load_of_refValid {m : MemoryState} {p : PtrVal}
    (hRef : refValidInMem m .shared tagTy (.ptr p) = .ok ()) :
    ∃ (aid : AllocId) (v : Val), p.allocId = some aid ∧
      loadIndirectV2 m tagTy ⟨aid, p.offsetBytes.toNat⟩ = .ok (some v) ∧
      (v = .enumVal tagE 0 ∨ v = .enumVal tagE 1) := by
  unfold refValidInMem at hRef
  rw [layoutOfTyV2_tag] at hRef
  dsimp only at hRef
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
        cases hDec : decodeValV2 profileV2TargetEndian tagTy
            ((a.bytes.drop p.offsetBytes.toNat).take 1) with
        | error k => rw [hDec] at hRef; cases hRef
        | ok ov =>
          cases ov with
          | none => rw [hDec] at hRef; cases hRef
          | some v =>
            refine ⟨aid, v, rfl, ?_, ?_⟩
            · unfold loadIndirectV2
              rw [layoutOfTyV2_tag]
              dsimp only
              unfold readBytes
              rw [hFind]
              dsimp only
              rw [ite_bool_false (rfl : Nat.beq 1 0 = false), ite_bool_false hBad]
              exact hDec
            · have hInB : isInBounds a p.offsetBytes.toNat 1 = true := by
                cases hI : isInBounds a p.offsetBytes.toNat 1 with
                | true => rfl
                | false =>
                  rw [hI, Bool.not_false, Bool.or_true, Bool.true_or] at hBad
                  cases hBad
              have hLt : p.offsetBytes.toNat < a.bytes.length :=
                Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_of_ble_true hInB)
              let ⟨x, hx⟩ := drop_take_one_of_lt _ _ hLt
              rw [hx] at hDec
              exact decode_tag_single hDec

/-! ## Frame-Local Steps Under Arbitrary Callers -/

theorem step_stmt {p : Program} {f f' : FrameState} {callers : List FrameState}
    {cm cm' : CallerMemory} {m m' : MemoryState} {body : Body} {bb : BasicBlock}
    {stmt : StatementKind}
    (hBody : activeFrameBody p f = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx = some stmt)
    (hEval : evalStatementV2 body f m cm stmt = .step ⟨[f'], cm', m'⟩) :
    evalStepV2 p ⟨f :: callers, cm, m⟩ = .step ⟨f' :: callers, cm', m'⟩ := by
  unfold evalStepV2
  dsimp only
  rw [hBody]; dsimp only; rw [hBB]; dsimp only; rw [hStmt]; dsimp only
  rw [hEval]
  cases callers <;> rfl

theorem step_term {p : Program} {f f' : FrameState} {callers : List FrameState}
    {cm cm' : CallerMemory} {m m' : MemoryState} {body : Body} {bb : BasicBlock}
    (hBody : activeFrameBody p f = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx = none)
    (hLen : Nat.beq f.stmtIdx bb.statements.length = true)
    (hT : (∃ t, bb.terminator = .goto t) ∨ (∃ o ts, bb.terminator = .switchInt o ts))
    (hEval : evalTerminatorV2 body bb f m cm p.panicStrategy p.hasLocalPanicHandler p.overflowChecks =
      .step ⟨[f'], cm', m'⟩) :
    evalStepV2 p ⟨f :: callers, cm, m⟩ = .step ⟨f' :: callers, cm', m'⟩ := by
  unfold evalStepV2
  dsimp only
  rw [hBody]; dsimp only; rw [hBB]; dsimp only; rw [hStmt]; dsimp only
  rw [ite_bool_true hLen]
  rcases hT with ⟨t, hT⟩ | ⟨o, ts, hT⟩ <;>
    (rw [hT]; dsimp only; rw [hEval]; cases callers <;> rfl)

/-! ## Body 1: `<Tag as PartialEq>::eq` -/

abbrev eqBody : Body := Captured.Shard_000.body_1

abbrev eqFr (b i : Nat) (l : List LocalSlot) (rd : Option Place)
    (rt : Option BasicBlockId) : FrameState :=
  ⟨1, b, i, l, none, rd, rt⟩

theorem eq_stmt {e b i : Nat} {l : List LocalSlot} {rd : Option Place}
    {rt : Option BasicBlockId} {f' : FrameState} {callers : List FrameState}
    {cm cm' : CallerMemory} {m m' : MemoryState} {bb : BasicBlock} {stmt : StatementKind}
    (hBB : Trusted.MirSemantics.getElem? eqBody.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = some stmt)
    (hEval : evalStatementV2 eqBody (eqFr b i l rd rt) m cm stmt = .step ⟨[f'], cm', m'⟩) :
    evalStepV2 (entryProgForBody Captured.program e) ⟨eqFr b i l rd rt :: callers, cm, m⟩ =
      .step ⟨f' :: callers, cm', m'⟩ :=
  step_stmt rfl hBB hStmt hEval

theorem eq_term {e b i : Nat} {l : List LocalSlot} {rd : Option Place}
    {rt : Option BasicBlockId} {f' : FrameState} {callers : List FrameState}
    {cm cm' : CallerMemory} {m m' : MemoryState} {bb : BasicBlock}
    (hBB : Trusted.MirSemantics.getElem? eqBody.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = none)
    (hLen : Nat.beq i bb.statements.length = true)
    (hT : (∃ t, bb.terminator = .goto t) ∨ (∃ o ts, bb.terminator = .switchInt o ts))
    (hEval : evalTerminatorV2 eqBody bb (eqFr b i l rd rt) m cm .unwind false false =
      .step ⟨[f'], cm', m'⟩) :
    evalStepV2 (entryProgForBody Captured.program e) ⟨eqFr b i l rd rt :: callers, cm, m⟩ =
      .step ⟨f' :: callers, cm', m'⟩ :=
  step_term rfl hBB hStmt hLen hT hEval

/-- Runs `<Tag as PartialEq>::eq` from its entry locals, in any caller context,
to its final `return` with `_0 = (va == vb)`. -/
theorem eq_run (e : Nat) {callers : List FrameState} {cm : CallerMemory} {mem : MemoryState}
    {rd : Option Place} {rt : Option BasicBlockId}
    {pa pb : PtrVal} {ida idb : AllocId} {va vb : Nat}
    (hV0 : checkValV2 (.ptr pa) refTagTy = true)
    (hV1 : checkValV2 (.ptr pb) refTagTy = true)
    (hRA : refValidInMem mem .shared tagTy (.ptr pa) = .ok ())
    (hRB : refValidInMem mem .shared tagTy (.ptr pb) = .ok ())
    (hPaId : pa.allocId = some ida) (hPbId : pb.allocId = some idb)
    (hLoadA : loadIndirectV2 mem tagTy ⟨ida, pa.offsetBytes.toNat⟩ = .ok (some (.enumVal tagE va)))
    (hLoadB : loadIndirectV2 mem tagTy ⟨idb, pb.offsetBytes.toNat⟩ = .ok (some (.enumVal tagE vb)))
    (hva : va = 0 ∨ va = 1) (hvb : vb = 0 ∨ vb = 1)
    {post : TerminalOut → Prop}
    (hK : ∀ l : List LocalSlot,
      Trusted.MirSemantics.getElem? l 0 = some (im (.bool (Nat.beq va vb))) →
      deallocateFrameLocalsV2 mem l = .ok mem →
      Runs (entryProgForBody Captured.program e) post
        ⟨eqFr 5 1 l rd rt :: callers, cm, mem⟩) :
    Runs (entryProgForBody Captured.program e) post
      ⟨eqFr 0 0 [N, im (.ptr pa), im (.ptr pb), D, D, D, N, N, N, N, N, N] rd rt :: callers,
        cm, mem⟩ := by
  -- bb0 stmt 0..1: storageLive 3, storageLive 4
  refine runs_step (eq_stmt rfl rfl rfl) ?_
  refine runs_step (eq_stmt rfl rfl rfl) ?_
  -- bb0 stmt 2: _4 = useRetag (copy _1)
  refine runs_step (eq_stmt rfl rfl (by
    dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?]
    rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
    try dsimp only
    have hRV : refsValidInMem mem refTagTy (.ptr pa) = true := by
      dsimp only [refsValidInMem]; rw [hRA]
    repeat (first
      | rw [ite_bool_false (by rw [hRV]; rfl)]
      | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
      | dsimp only)
    rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)) ?_
  -- bb0 stmt 3: storageLive 5
  refine runs_step (eq_stmt rfl rfl rfl) ?_
  -- bb0 stmt 4: _5 = useRetag (copy _2)
  refine runs_step (eq_stmt rfl rfl (by
    dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?]
    rw [readPlaceV2_copy_local (by rfl) (by rfl) (by decide)]
    try dsimp only
    have hRV : refsValidInMem mem refTagTy (.ptr pb) = true := by
      dsimp only [refsValidInMem]; rw [hRB]
    repeat (first
      | rw [ite_bool_false (by rw [hRV]; rfl)]
      | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
      | dsimp only)
    rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)) ?_
  -- bb0 stmt 5: _3 = (move _4, move _5)
  refine runs_step (eq_stmt rfl rfl (by
    dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, evalArgOperandsV2]
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
    dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
    dsimp only [argValues]
    have hCL : checkValV2List [.ptr pa, .ptr pb] [refTagTy, refTagTy] = true := by
      dsimp only [checkValV2List]; rw [hV0, hV1]; rfl
    have hChkTuple : checkValV2 (.tuple [.ptr pa, .ptr pb]) (.tuple [refTagTy, refTagTy]) = true := by
      unfold checkValV2; exact hCL
    simp only [hCL]
    repeat (first
      | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
      | dsimp only)
    rw [writePlaceDestV2_immediate_ok hChkTuple (by rfl) (by rfl)]; rfl)) ?_
  -- bb0 stmt 6..8: storageDead 5, storageDead 4, nop
  refine runs_step (eq_stmt rfl rfl rfl) ?_
  refine runs_step (eq_stmt rfl rfl rfl) ?_
  refine runs_step (eq_stmt rfl rfl rfl) ?_
  -- bb0 stmt 9: _9 = copy (_3.0)
  refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2, projectValFieldV2, projectOneElemV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | dsimp only)
      rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)) ?_
  rcases hva with rfl | rfl <;> rcases hvb with rfl | rfl
  · -- (A, A): bb0 -> bb2 -> bb4 -> bb5
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPaId]
        | rw [hLoadA]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2, projectValFieldV2, projectOneElemV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | dsimp only)
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPbId]
        | rw [hLoadB]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    refine runs_step (eq_term rfl rfl rfl (.inl ⟨_, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    exact hK _ rfl rfl
  · -- (A, B): bb0 -> bb2 -> bb1 -> bb5
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPaId]
        | rw [hLoadA]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2, projectValFieldV2, projectOneElemV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | dsimp only)
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPbId]
        | rw [hLoadB]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    refine runs_step (eq_term rfl rfl rfl (.inl ⟨_, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    exact hK _ rfl rfl
  · -- (B, A): bb0 -> bb3 -> bb1 -> bb5
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPaId]
        | rw [hLoadA]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2, projectValFieldV2, projectOneElemV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | dsimp only)
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPbId]
        | rw [hLoadB]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    refine runs_step (eq_term rfl rfl rfl (.inl ⟨_, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    exact hK _ rfl rfl
  · -- (B, B): bb0 -> bb3 -> bb4 -> bb5
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPaId]
        | rw [hLoadA]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2, projectValFieldV2, projectOneElemV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | dsimp only)
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2,
      resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2,
      stepProjectedTyV2, placeProjectedTyV2, evalRvalueV2, evalOperandToSlotV2,
      eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?, readPlaceV2]
      repeat (first
        | (rw [ite_bool_false]; rotate_left; first | rfl | decide)
        | (rw [ite_bool_true]; rotate_left; first | rfl | decide)
        | rw [layoutOfTyV2_tag]
        | rw [hPbId]
        | rw [hLoadB]
        | dsimp only [evalDiscriminantOfVal]
        | dsimp only)
      try (first | rw [ite_prop_true (by decide)] | rw [ite_prop_false (by decide)])
      try dsimp only [Trusted.MirSemantics.getElem?]
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)]; rfl)) ?_
    refine runs_step (eq_term rfl rfl rfl (.inr ⟨_, _, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    refine runs_step (eq_term rfl rfl rfl (.inl ⟨_, rfl⟩) rfl) ?_
    refine runs_step (eq_stmt rfl rfl rfl) ?_
    exact hK _ rfl rfl

/-! ## Calls and Returns -/

theorem step_return_top {p : Program} {f : FrameState} {cm : CallerMemory}
    {m : MemoryState} {body : Body} {bb : BasicBlock} {out : TerminalOut}
    (hBody : activeFrameBody p f = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx = none)
    (hLen : Nat.beq f.stmtIdx bb.statements.length = true)
    (hT : bb.terminator = .return_)
    (hEval : evalTerminatorV2 body bb f m cm p.panicStrategy p.hasLocalPanicHandler p.overflowChecks =
      .done out) :
    evalStepV2 p ⟨[f], cm, m⟩ = .done out := by
  unfold evalStepV2
  dsimp only
  rw [hBody]; dsimp only; rw [hBB]; dsimp only; rw [hStmt]; dsimp only
  rw [ite_bool_true hLen, hT]
  exact hEval

theorem step_return_caller {p : Program} {f c : FrameState} {rest : List FrameState}
    {cm : CallerMemory} {m : MemoryState} {body : Body} {bb : BasicBlock}
    {res : StepResult State TerminalOut}
    (hBody : activeFrameBody p f = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx = none)
    (hLen : Nat.beq f.stmtIdx bb.statements.length = true)
    (hT : bb.terminator = .return_)
    (hEval : evalReturnToCallerV2 p body bb f c rest m cm = res) :
    evalStepV2 p ⟨f :: c :: rest, cm, m⟩ = res := by
  unfold evalStepV2
  dsimp only
  rw [hBody]; dsimp only; rw [hBB]; dsimp only; rw [hStmt]; dsimp only
  rw [ite_bool_true hLen, hT]
  exact hEval

theorem step_call {p : Program} {f : FrameState} {callers : List FrameState}
    {cm : CallerMemory} {m : MemoryState} {body : Body} {bb : BasicBlock}
    {callee : DefId} {args : List Operand} {dst : Place} {t : Option BasicBlockId}
    {u : UnwindAction} {res : StepResult State TerminalOut}
    (hBody : activeFrameBody p f = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx = none)
    (hLen : Nat.beq f.stmtIdx bb.statements.length = true)
    (hT : bb.terminator = .call callee args dst t u ∨
      bb.terminator = .callNe callee args dst t u)
    (hEval : evalCallV2 p body f callers m cm callee args dst t u = res) :
    evalStepV2 p ⟨f :: callers, cm, m⟩ = res := by
  unfold evalStepV2
  dsimp only
  rw [hBody]; dsimp only; rw [hBB]; dsimp only; rw [hStmt]; dsimp only
  rw [ite_bool_true hLen]
  rcases hT with hT | hT <;> (rw [hT]; exact hEval)

/-- `<Tag as PartialEq>::eq` returning from the outermost frame. -/
theorem eq_return_top {e : Nat} {l : List LocalSlot} {cm : CallerMemory} {r : Bool}
    (hCM : validCallerMemory cm = true)
    (hl0 : Trusted.MirSemantics.getElem? l 0 = some (im (.bool r))) :
    evalStepV2 (entryProgForBody Captured.program e)
      ⟨[eqFr 5 1 l none none], cm, entryMemoryWithCaller cm⟩ =
      .done (.returned ⟨.bool r, cm⟩) := by
  refine step_return_top rfl rfl rfl rfl rfl ?_
  rw [evalTerminatorV2_return_ok rfl rfl rfl hl0 rfl rfl rfl rfl]
  rw [extractCallerMemory_entry cm hCM]

theorem eq_correct (q : Query) (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q := by
  rcases tag_ref_args_inv (body := Captured.body_1) rfl hValid with
    ⟨pa, pb, hList, hV0, hV1, hRA, hRB⟩
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  rcases tag_load_of_refValid hRA with ⟨ida, va, hPaId, hLoadA, hva⟩
  rcases tag_load_of_refValid hRB with ⟨idb, vb, hPbId, hLoadB, hvb⟩
  have hIdx : ∀ {v : Val}, (v = .enumVal tagE 0 ∨ v = .enumVal tagE 1) →
      ∃ i, v = .enumVal tagE i ∧ (i = 0 ∨ i = 1) := by
    intro v hv
    rcases hv with rfl | rfl
    · exact ⟨0, rfl, .inl rfl⟩
    · exact ⟨1, rfl, .inr rfl⟩
  rcases hIdx hva with ⟨ia, rfl, hia⟩
  rcases hIdx hvb with ⟨ib, rfl, hib⟩
  have hInit : initStateV2 (entryProgForBody Captured.program 1) q =
      .ok ⟨[⟨1, 0, 0, initLocalsLoop Captured.body_1 q.args 0 Captured.body_1.locals,
        none, none, none⟩], q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    apply initStateV2_ok_of (p := entryProgForBody Captured.program 1) (q := q)
      (body := Captured.body_1) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hArgs
    · exact hRefs
    · exact hDisj
  have hLocs : initLocalsLoop Captured.body_1 q.args 0 Captured.body_1.locals =
      [N, im (.ptr pa), im (.ptr pb), D, D, D, N, N, N, N, N, N] := by
    rw [hList]; rfl
  rw [hLocs] at hInit
  have hRuns : Runs (entryProgForBody Captured.program 1)
      (fun o => o = .returned ⟨.bool (Nat.beq ia ib), q.callerMem⟩)
      ⟨[eqFr 0 0 [N, im (.ptr pa), im (.ptr pb), D, D, D, N, N, N, N, N, N] none none],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ :=
    eq_run 1 (callers := []) hV0 hV1 hRA hRB hPaId hPbId hLoadA hLoadB hia hib
      (fun _ hl0 _ => runs_done (eq_return_top hCM hl0) rfl)
  let ⟨_, hExec⟩ := execProgV2_of_runs hInit hRuns
  exact (spec_and_behaviorV2_of_exec_eq hExec).1

/-! ## Body 0: `<Tag as AaaFake>::fake_eq` -/

theorem fake_eq_correct (q : Query) (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q := by
  rcases tag_ref_args_inv (body := Captured.body_0) rfl hValid with
    ⟨pa, pb, hList, _, _, _, _⟩
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  have hB0 : Trusted.MirSemantics.getElem? (entryProgForBody Captured.program 0).bodies 0 =
      some Captured.body_0 := rfl
  have hInit : initStateV2 (entryProgForBody Captured.program 0) q =
      .ok ⟨[⟨0, 0, 0, initLocalsLoop Captured.body_0 q.args 0 Captured.body_0.locals,
        none, none, none⟩], q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    apply initStateV2_ok_of (p := entryProgForBody Captured.program 0) (q := q)
      (body := Captured.body_0) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hArgs
    · exact hRefs
    · exact hDisj
  have hLocs : initLocalsLoop Captured.body_0 q.args 0 Captured.body_0.locals =
      [N, im (.ptr pa), im (.ptr pb)] := by
    rw [hList]; rfl
  rw [hLocs] at hInit
  let out : TerminalOut := .returned ⟨.bool false, q.callerMem⟩
  have hRuns : Runs (entryProgForBody Captured.program 0) (fun o => o = out)
      ⟨[⟨0, 0, 0, [N, im (.ptr pa), im (.ptr pb)], none, none, none⟩],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    -- bb0 stmt 0: `_0 = const false`
    apply runs_step (by rfl)
    -- bb0 terminator: `return`
    apply runs_done (by
      dsimp only [evalStepV2, activeFrameBody]
      rw [hB0]
      dsimp only [Captured.body_0, Captured.Shard_000.body_0, Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rfl)
    rfl
  let ⟨_, hExec⟩ := execProgV2_of_runs hInit hRuns
  exact (spec_and_behaviorV2_of_exec_eq hExec).1

/-! ## Bodies 2-19: `fake_caller_00` .. `fake_caller_17` -/

/-- The 18 `fake_caller_*` bodies differ only in their identities. -/
def fcBody (id : String) : Body := { Captured.body_2 with identity := id }

theorem fake_caller_correct (k : Nat) (id : String)
    (hB : Trusted.MirSemantics.getElem? Captured.program.bodies k = some (fcBody id))
    (q : Query) (hValid : ValidEntryArgsV2 (fcBody id) q) :
    WellFormedV2 (entryProgForBody Captured.program k) q := by
  rcases tag_ref_args_inv (body := fcBody id) rfl hValid with
    ⟨pa, pb, hList, hV0, hV1, hRA, hRB⟩
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  have hBk : Trusted.MirSemantics.getElem? (entryProgForBody Captured.program k).bodies k =
      some (fcBody id) := hB
  have hB0 : Trusted.MirSemantics.getElem? (entryProgForBody Captured.program k).bodies 0 =
      some Captured.body_0 := rfl
  have hInit : initStateV2 (entryProgForBody Captured.program k) q =
      .ok ⟨[⟨k, 0, 0, initLocalsLoop (fcBody id) q.args 0 (fcBody id).locals,
        none, none, none⟩], q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    apply initStateV2_ok_of (p := entryProgForBody Captured.program k) (q := q)
      (body := fcBody id) (by rfl) (by rfl) hCM hBk (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    · exact hArgs
    · exact hRefs
    · exact hDisj
  have hLocs : initLocalsLoop (fcBody id) q.args 0 (fcBody id).locals =
      [N, im (.ptr pa), im (.ptr pb), D, D] := by
    rw [hList]; rfl
  rw [hLocs] at hInit
  have hChk : checkArgsMatchV2 [.ptr pa, .ptr pb]
      (List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals)) = true := by
    rw [hList] at hArgs; exact hArgs
  have hRefsC : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      (List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals))
      [.ptr pa, .ptr pb] = true := by
    rw [hList] at hRefs; exact hRefs
  have hDisjC : spansPairwiseDisjoint (refAccessSpansList
      (List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals))
      [.ptr pa, .ptr pb]) = true := by
    rw [hList] at hDisj; exact hDisj
  have hTyped : typedArgsMatchV2 [(refTagTy, .ptr pa), (refTagTy, .ptr pb)]
      (List.take Captured.body_0.argumentCount (List.drop 1 Captured.body_0.locals)) = true := by
    rfl
  have hEvalArgs : evalArgOperandsV2 (fcBody id).locals
      [N, im (.ptr pa), im (.ptr pb), im (.ptr pa), im (.ptr pb)]
      (entryMemoryWithCaller q.callerMem)
      [.move ⟨3, []⟩, .move ⟨4, []⟩] =
      .ok ([(refTagTy, .ptr pa), (refTagTy, .ptr pb)],
        [N, im (.ptr pa), im (.ptr pb), liveUninitSlot refTagTy, liveUninitSlot refTagTy],
        entryMemoryWithCaller q.callerMem) := by
    dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
    dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
    rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
  have hLocs0 : initLocalsLoop Captured.body_0 [.ptr pa, .ptr pb] 0 Captured.body_0.locals =
      [N, im (.ptr pa), im (.ptr pb)] := rfl
  let out : TerminalOut := .returned ⟨.bool false, q.callerMem⟩
  have hRuns : Runs (entryProgForBody Captured.program k) (fun o => o = out)
      ⟨[⟨k, 0, 0, [N, im (.ptr pa), im (.ptr pb), D, D], none, none, none⟩],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    -- bb0 stmt 0: `StorageLive(_3)`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2]
      rfl)
    -- bb0 stmt 1: `_3 = &(*_1)`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2, attachCallers,
        Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [hRA]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV0 (by rfl) (by rfl)]; rfl)
    -- bb0 stmt 2: `StorageLive(_4)`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2]
      rfl)
    -- bb0 stmt 3: `_4 = &(*_2)`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2, attachCallers,
        Trusted.MirSemantics.getElem?, evalStatementV2, resolvePlaceDestV2,
        resolveIndexProjsV2, consResolvedProjV2, placeStaticTyV2, evalRvalueV2, evalRefRvalueV2]
      rw [ite_bool_false]; rotate_left; rfl
      rw [ite_bool_false]; rotate_left; decide
      rw [hRB]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hV1 (by rfl) (by rfl)]; rfl)
    -- bb0 terminator: `_0 = <Tag as AaaFake>::fake_eq(move _3, move _4) -> bb1`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2,
        Trusted.MirSemantics.getElem?]
      rw [ite_bool_true]; rotate_left; decide
      rw [pb_evalCallV2_ok (calleeBody := Captured.body_0) rfl hB0 (by decide) rfl
        rfl hEvalArgs rfl hTyped hChk hRefsC hDisjC hLocs0 rfl rfl rfl])
    -- callee bb0 stmt 0: `_0 = const false`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hB0]
      dsimp only [Captured.body_0, Captured.Shard_000.body_0]
      rfl)
    -- callee bb0 terminator: `return` into the caller's `_0`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hB0]
      dsimp only [Captured.body_0, Captured.Shard_000.body_0, Trusted.MirSemantics.getElem?,
        evalReturnToCallerV2, deallocateFrameLocalsV2, deallocateLocal, activeFrameBody]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2]
      rfl)
    -- bb1 stmt 0: `StorageDead(_4)`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2]
      rfl)
    -- bb1 stmt 1: `StorageDead(_3)`
    apply runs_step (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2]
      rfl)
    -- bb1 terminator: `return`
    apply runs_done (by
      dsimp only [evalStepV2, activeFrameBody, List.cons_append, List.nil_append]
      rw [hBk]
      dsimp only [fcBody, Captured.body_2, Captured.Shard_000.body_2,
        Trusted.MirSemantics.getElem?]
      rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
        (by rfl) (by rfl) (by rfl) (by rfl)]
      rw [extractCallerMemory_entry q.callerMem hCM]
      rfl)
    rfl
  let ⟨_, hExec⟩ := execProgV2_of_runs hInit hRuns
  exact (spec_and_behaviorV2_of_exec_eq hExec).1

/-! ## Promoting a `Tag` Local to Memory -/

/-- The one-byte stack allocation holding `Tag` variant `x`. -/
noncomputable def tagAlloc (id x : Nat) : Allocation :=
  { allocId := id, alignLog2 := 0, mutability := .mut,
    bytes := [.init (UInt8.ofNat x) none], live := true }

theorem replaceAllocation_append_fresh {a' : Allocation} {u : Allocation}
    (hId : u.allocId = a'.allocId) :
    ∀ (xs : List Allocation), (∀ a, a ∈ xs → a.allocId ≠ a'.allocId) →
      replaceAllocation a' (xs ++ [u]) = xs ++ [a']
  | [], _ => by
    change (if Nat.beq u.allocId a'.allocId then a' :: [] else u :: replaceAllocation a' []) = [a']
    rw [hId, Nat.beq_refl]; rfl
  | hd :: tl, hXs => by
    have hNe : hd.allocId ≠ a'.allocId := hXs hd (.head _)
    have hBeq : Nat.beq hd.allocId a'.allocId = false := by
      cases hEq : Nat.beq hd.allocId a'.allocId with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe
    change (if Nat.beq hd.allocId a'.allocId then a' :: tl ++ [u]
      else hd :: replaceAllocation a' (tl ++ [u])) = hd :: (tl ++ [a'])
    rw [hBeq]
    exact congrArg (hd :: ·) (replaceAllocation_append_fresh hId tl (fun a ha => hXs a (.tail _ ha)))

theorem encode_tag {x : Nat} (hx : x = 0 ∨ x = 1) :
    encodeValV2 profileV2TargetEndian tagTy (.enumVal tagE x) =
      .ok [.init (UInt8.ofNat x) none] := by
  rcases hx with rfl | rfl <;> rfl

/-- `promoteLocalToMemory` of an immediate `Tag` local allocates the next
allocation id and stores the variant byte there. -/
theorem promote_tag {bodyLocals : List MirTy} {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid x : Nat}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some tagTy)
    (hSlot : Trusted.MirSemantics.getElem? locals lid = some (im (.enumVal tagE x)))
    (hSet : Trusted.MirSemantics.setElem? locals lid (.indirect ⟨mem.nextAllocId, 0⟩) =
      some locals')
    (hLt : ∀ a, a ∈ mem.allocations → a.allocId < mem.nextAllocId)
    (hx : x = 0 ∨ x = 1) :
    promoteLocalToMemory bodyLocals locals mem lid =
      .ok (tagTy, ⟨mem.nextAllocId, 0⟩, locals',
        ⟨mem.nextAllocId + 1, mem.allocations ++ [tagAlloc mem.nextAllocId x]⟩) := by
  have hFresh : ∀ a, a ∈ mem.allocations → a.allocId ≠ mem.nextAllocId :=
    fun a ha => Nat.ne_of_lt (hLt a ha)
  let u : Allocation :=
    { allocId := mem.nextAllocId, alignLog2 := 0, mutability := .mut,
      bytes := List.replicate 1 .uninit, live := true }
  have hFind : findAllocation mem.nextAllocId (mem.allocations ++ [u]) = some u :=
    findAllocation_append_single_fresh (x := u) hFresh
  have hRepl : replaceAllocation (tagAlloc mem.nextAllocId x) (mem.allocations ++ [u]) =
      mem.allocations ++ [tagAlloc mem.nextAllocId x] :=
    replaceAllocation_append_fresh (u := u) (a' := tagAlloc mem.nextAllocId x) rfl _ hFresh
  unfold promoteLocalToMemory
  rw [hTy, hSlot]
  dsimp only
  rw [layoutOfTyV2_tag]
  dsimp only [allocateStack, MemoryState.reserveAllocId]
  unfold storeIndirectV2
  rw [layoutOfTyV2_tag]
  dsimp only
  rw [encode_tag hx]
  dsimp only
  unfold writeBytes
  rw [hFind]
  dsimp only
  rw [ite_bool_false]; rotate_left; rfl
  rw [ite_bool_false]; rotate_left; rfl
  try dsimp only
  erw [hRepl]
  try dsimp only
  rw [hSet]

theorem refValid_tagAlloc {n : Nat} {allocs : List Allocation} {id x : Nat}
    (hFind : findAllocation id allocs = some (tagAlloc id x)) (hx : x = 0 ∨ x = 1) :
    refValidInMem ⟨n, allocs⟩ .shared tagTy (.ptr ⟨some id, UInt64.ofNat 0, .isize⟩) =
      .ok () := by
  unfold refValidInMem
  rw [layoutOfTyV2_tag]
  dsimp only
  rw [hFind]
  rcases hx with rfl | rfl <;> rfl

theorem load_tagAlloc {n : Nat} {allocs : List Allocation} {id x : Nat}
    (hFind : findAllocation id allocs = some (tagAlloc id x)) (hx : x = 0 ∨ x = 1) :
    loadIndirectV2 ⟨n, allocs⟩ tagTy ⟨id, (UInt64.ofNat 0).toNat⟩ =
      .ok (some (.enumVal tagE x)) := by
  unfold loadIndirectV2
  rw [layoutOfTyV2_tag]
  dsimp only
  unfold readBytes
  rw [hFind]
  rcases hx with rfl | rfl <;> rfl

theorem entry_allocId_lt (cm : CallerMemory) :
    ∀ a, a ∈ (entryMemoryWithCaller cm).allocations →
      a.allocId < (entryMemoryWithCaller cm).nextAllocId := by
  intro a ha
  have hLe : a.allocId ≤ maxAllocAndProvId cm.allocations :=
    Nat.le_trans (allocId_le_maxAllocId ha) (Nat.le_max_left _ _)
  change a.allocId < Nat.max entryMemory.nextAllocId (maxAllocAndProvId cm.allocations + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hLe) (Nat.le_max_right _ _)

theorem allocId_lt_append_tag {allocs : List Allocation} {n x : Nat}
    (hLt : ∀ a, a ∈ allocs → a.allocId < n) :
    ∀ a, a ∈ allocs ++ [tagAlloc n x] → a.allocId < n + 1 := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact Nat.lt_succ_of_lt (hLt a h)
  · cases h with
    | head _ => exact Nat.lt_succ_self n
    | tail _ h' => cases h'

/-- `extractCallerMemory` ignores allocations appended after the caller's. -/
theorem extractCallerMemory_append {cm : CallerMemory} {n : Nat} (xs : List Allocation)
    (hValid : validCallerMemory cm = true) :
    extractCallerMemory cm ⟨n, cm.allocations ++ xs⟩ = cm := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    have hSelf : ∀ a, a ∈ allocs → findAllocation a.allocId allocs = some a :=
      findAllocation_in_allocIdsValid [] allocs [] (fun _ h => by cases h)
        (fun _ h => by cases h) hValid
    have hApp : ∀ a, a ∈ allocs → findAllocation a.allocId (allocs ++ xs) = some a := by
      intro a ha
      rw [findAllocation_append_left_of_lt ⟨a, hSelf a ha⟩]
      exact hSelf a ha
    rw [extractCallerAllocations_of_found _ allocs hApp]

theorem calleeLive_nil_of_ids {ids f : List AllocId} :
    ∀ {l : List Allocation}, (∀ a, a ∈ l → a.allocId ∈ ids ∨ a.allocId ∈ f) →
      calleeLiveAllocations ids f l = []
  | [], _ => rfl
  | a :: _, h => by
    unfold calleeLiveAllocations
    cases h a (.head _) with
    | inl hIn =>
      rw [rm2_natNotElem_false_of_mem hIn, Bool.and_false, Bool.false_and]
      exact calleeLive_nil_of_ids (fun b hb => h b (.tail _ hb))
    | inr hIn =>
      rw [rm2_natNotElem_false_of_mem hIn, Bool.and_false]
      exact calleeLive_nil_of_ids (fun b hb => h b (.tail _ hb))

theorem evalTerminatorV2_return_ok' {body : Body} {bb : BasicBlock} {frame : FrameState}
    {mem : MemoryState} {callerMem cm' : CallerMemory} {retTy : MirTy} {retVal : Val}
    {ps : PanicStrategy} {hLocal oc : Bool}
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 = some (.immediate (some retVal)))
    (hNoRodata : hasEscapingRodataPtr callerMem mem retTy retVal = false)
    (hStay : refsStayInCallerMem callerMem retTy retVal = true)
    (hValid : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true)
    (hRet : extractReturnMemoryV2 callerMem mem frame.locals = cm') :
    evalTerminatorV2 body bb frame mem callerMem ps hLocal oc =
      .done (.returned ⟨retVal, cm'⟩) := by
  unfold evalTerminatorV2
  rw [hTerm]
  dsimp only
  rw [ite_bool_false hCleanup, hRetTy, hRetSlot]
  dsimp only
  rw [ite_bool_false hNoRodata, ite_bool_false (by rw [hStay, hValid, hDisj]; rfl)]
  rw [hRet]

/-! ## Body 20: `tag_ne` -/

abbrev neBody : Body := Captured.Shard_001.body_0

abbrev neFr (b i : Nat) (l : List LocalSlot) : FrameState :=
  ⟨20, b, i, l, none, none, none⟩

theorem ne_stmt {b i : Nat} {l : List LocalSlot} {f' : FrameState}
    {callers : List FrameState} {cm cm' : CallerMemory} {m m' : MemoryState}
    {bb : BasicBlock} {stmt : StatementKind}
    (hBB : Trusted.MirSemantics.getElem? neBody.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = some stmt)
    (hEval : evalStatementV2 neBody (neFr b i l) m cm stmt = .step ⟨[f'], cm', m'⟩) :
    evalStepV2 (entryProgForBody Captured.program 20) ⟨neFr b i l :: callers, cm, m⟩ =
      .step ⟨f' :: callers, cm', m'⟩ :=
  step_stmt rfl hBB hStmt hEval

theorem bodyCallAdmitted_eq : bodyCallAdmittedV2 eqBody = true := by decide

theorem tag_ne_correct (q : Query) (hValid : ValidEntryArgsV2 Captured.body_20 q) :
    WellFormedV2 (entryProgForBody Captured.program 20) q ∧
    match q.args with
    | [.enumVal _ x, .enumVal _ y] =>
      BehaviorV2 (entryProgForBody Captured.program 20) q
        (TerminalOut.returned ⟨.bool (!(Nat.beq x y)), q.callerMem⟩)
    | _ => False := by
  rcases tag_val_args_inv (body := Captured.body_20) rfl hValid with ⟨x, y, hList, hx, hy⟩
  let ⟨hCM, hArgs, hRefs, hDisj⟩ := hValid
  have hInit : initStateV2 (entryProgForBody Captured.program 20) q =
      .ok ⟨[⟨20, 0, 0, initLocalsLoop Captured.body_20 q.args 0 Captured.body_20.locals,
        none, none, none⟩], q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    apply initStateV2_ok_of (p := entryProgForBody Captured.program 20) (q := q)
      (body := Captured.body_20) (by rfl) (by rfl) hCM (by rfl) (by rfl) (by rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hArgs
    · exact hRefs
    · exact hDisj
  have hLocs : initLocalsLoop Captured.body_20 q.args 0 Captured.body_20.locals =
      [N, im (.enumVal tagE x), im (.enumVal tagE y), D, D] := by
    rw [hList]; rfl
  rw [hLocs] at hInit
  have hLt0 := entry_allocId_lt q.callerMem
  have hLt1 := allocId_lt_append_tag (x := x) hLt0
  have hFind1 : findAllocation (entryMemoryWithCaller q.callerMem).nextAllocId
      ((entryMemoryWithCaller q.callerMem).allocations ++
        [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) =
      some (tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x) :=
    findAllocation_append_single_fresh (x := tagAlloc _ x) (fun a ha => Nat.ne_of_lt (hLt0 a ha))
  have hFind2 : findAllocation ((entryMemoryWithCaller q.callerMem).nextAllocId + 1)
      (((entryMemoryWithCaller q.callerMem).allocations ++
        [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
        [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]) =
      some (tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y) :=
    findAllocation_append_single_fresh (x := tagAlloc _ y) (fun a ha => Nat.ne_of_lt (hLt1 a ha))
  have hFind1' : findAllocation (entryMemoryWithCaller q.callerMem).nextAllocId
      (((entryMemoryWithCaller q.callerMem).allocations ++
        [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
        [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]) =
      some (tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x) := by
    rw [findAllocation_append_left_of_lt ⟨_, hFind1⟩]
    exact hFind1
  have hRuns : Runs (entryProgForBody Captured.program 20)
      (fun o => o = .returned ⟨.bool (!(Nat.beq x y)), q.callerMem⟩)
      ⟨[neFr 0 0 [N, im (.enumVal tagE x), im (.enumVal tagE y), D, D]],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
    -- bb0 stmt 0: storageLive 3
    refine runs_step (ne_stmt rfl rfl rfl) ?_
    -- bb0 stmt 1: _3 = &_1 (promotes `x` to a fresh stack allocation)
    refine runs_step (ne_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
        consResolvedProjV2, placeStaticTyV2, stepProjectedTyV2, placeProjectedTyV2,
        evalRvalueV2, evalRefRvalueV2, neBody, Captured.Shard_001.body_0,
        Trusted.MirSemantics.getElem?]
      rw [promote_tag (by rfl) (by rfl) (by rfl) hLt0 hx]
      repeat (first | (rw [ite_bool_false]; rotate_left; first | rfl | decide) | dsimp only)
      rw [refValid_tagAlloc hFind1 hx]
      repeat (first | (rw [ite_bool_false]; rotate_left; first | rfl | decide) | dsimp only)
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]; rfl)) ?_
    -- bb0 stmt 2: storageLive 4
    refine runs_step (ne_stmt rfl rfl rfl) ?_
    -- bb0 stmt 3: _4 = &_2 (promotes `y` to the next stack allocation)
    refine runs_step (ne_stmt rfl rfl (by
      dsimp only [evalStatementV2, resolvePlaceDestV2, resolveIndexProjsV2,
        consResolvedProjV2, placeStaticTyV2, stepProjectedTyV2, placeProjectedTyV2,
        evalRvalueV2, evalRefRvalueV2, neBody, Captured.Shard_001.body_0,
        Trusted.MirSemantics.getElem?]
      rw [promote_tag (mem := ⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1,
        (entryMemoryWithCaller q.callerMem).allocations ++
          [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]⟩)
        (by rfl) (by rfl) (by rfl) hLt1 hy]
      repeat (first | (rw [ite_bool_false]; rotate_left; first | rfl | decide) | dsimp only)
      rw [refValid_tagAlloc hFind2 hy]
      repeat (first | (rw [ite_bool_false]; rotate_left; first | rfl | decide) | dsimp only)
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)]; rfl)) ?_
    -- bb0 terminator: callNe 1 [move _3, move _4] -> _0, bb1
    have hRA : refValidInMem (⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1 + 1,
        ((entryMemoryWithCaller q.callerMem).allocations ++ [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
          [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]⟩ : MemoryState) .shared tagTy (.ptr (⟨some (entryMemoryWithCaller q.callerMem).nextAllocId, UInt64.ofNat 0, .isize⟩ : PtrVal)) = .ok () :=
      refValid_tagAlloc hFind1' hx
    have hRB : refValidInMem (⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1 + 1,
        ((entryMemoryWithCaller q.callerMem).allocations ++ [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
          [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]⟩ : MemoryState) .shared tagTy (.ptr (⟨some ((entryMemoryWithCaller q.callerMem).nextAllocId + 1), UInt64.ofNat 0, .isize⟩ : PtrVal)) = .ok () :=
      refValid_tagAlloc hFind2 hy
    have hEvalArgs : evalArgOperandsV2 neBody.locals [N, .indirect ⟨(entryMemoryWithCaller q.callerMem).nextAllocId, 0⟩, .indirect ⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1, 0⟩,
          im (.ptr (⟨some (entryMemoryWithCaller q.callerMem).nextAllocId, UInt64.ofNat 0, .isize⟩ : PtrVal)), im (.ptr (⟨some ((entryMemoryWithCaller q.callerMem).nextAllocId + 1), UInt64.ofNat 0, .isize⟩ : PtrVal))] (⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1 + 1,
        ((entryMemoryWithCaller q.callerMem).allocations ++ [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
          [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]⟩ : MemoryState)
        [.move ⟨3, []⟩, .move ⟨4, []⟩] =
        .ok ([(refTagTy, .ptr (⟨some (entryMemoryWithCaller q.callerMem).nextAllocId, UInt64.ofNat 0, .isize⟩ : PtrVal)), (refTagTy, .ptr (⟨some ((entryMemoryWithCaller q.callerMem).nextAllocId + 1), UInt64.ofNat 0, .isize⟩ : PtrVal))],
          [N, .indirect ⟨(entryMemoryWithCaller q.callerMem).nextAllocId, 0⟩, .indirect ⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1, 0⟩,
            liveUninitSlot refTagTy, liveUninitSlot refTagTy], (⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1 + 1,
        ((entryMemoryWithCaller q.callerMem).allocations ++ [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
          [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]⟩ : MemoryState)) := by
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
      dsimp only [evalArgOperandsV2, evalOperandToSlotV2]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by decide) (by rfl)]
    have hRefsC : refsValidInMemList (⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1 + 1,
        ((entryMemoryWithCaller q.callerMem).allocations ++ [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
          [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]⟩ : MemoryState)
        (List.take eqBody.argumentCount (List.drop 1 eqBody.locals))
        [.ptr (⟨some (entryMemoryWithCaller q.callerMem).nextAllocId, UInt64.ofNat 0, .isize⟩ : PtrVal), .ptr (⟨some ((entryMemoryWithCaller q.callerMem).nextAllocId + 1), UInt64.ofNat 0, .isize⟩ : PtrVal)] = true := by
      change refsValidInMemList (⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1 + 1,
        ((entryMemoryWithCaller q.callerMem).allocations ++ [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
          [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]⟩ : MemoryState) [refTagTy, refTagTy] [.ptr (⟨some (entryMemoryWithCaller q.callerMem).nextAllocId, UInt64.ofNat 0, .isize⟩ : PtrVal), .ptr (⟨some ((entryMemoryWithCaller q.callerMem).nextAllocId + 1), UInt64.ofNat 0, .isize⟩ : PtrVal)] = true
      dsimp only [refsValidInMemList, refsValidInMem]
      rw [hRA, hRB]
      rfl
    refine runs_step (step_call rfl rfl rfl rfl (.inr rfl)
      (pb_evalCallV2_ok (calleeBody := eqBody) rfl rfl bodyCallAdmitted_eq rfl rfl hEvalArgs rfl
        rfl rfl hRefsC rfl rfl rfl rfl rfl)) ?_
    refine eq_run 20 rfl rfl hRA hRB rfl rfl (load_tagAlloc hFind1' hx) (load_tagAlloc hFind2 hy)
      hx hy ?_
    intro l hl0 hDealloc
    -- callee return: `_0 = !eq(..)` in `tag_ne`, resuming at bb1
    refine runs_step (step_return_caller rfl rfl rfl rfl rfl (by
      unfold evalReturnToCallerV2
      dsimp only [eqBody, Captured.Shard_000.body_1, Trusted.MirSemantics.getElem?]
      rw [hl0]
      dsimp only
      rw [hDealloc]
      rfl)) ?_
    -- bb1: storageDead 4, storageDead 3
    refine runs_step (ne_stmt rfl rfl rfl) ?_
    refine runs_step (ne_stmt rfl rfl rfl) ?_
    -- bb1: return; the two promoted locals are frame-local, so the caller
    -- sees its own memory unchanged.
    refine runs_done (step_return_top rfl rfl rfl rfl rfl
      (evalTerminatorV2_return_ok' rfl rfl rfl rfl rfl rfl rfl rfl ?_)) rfl
    unfold extractReturnMemoryV2
    rw [calleeLive_nil_of_ids, List.append_nil]
    · have hX : extractCallerMemory q.callerMem
          ⟨(entryMemoryWithCaller q.callerMem).nextAllocId + 1 + 1,
            ((entryMemoryWithCaller q.callerMem).allocations ++ [tagAlloc (entryMemoryWithCaller q.callerMem).nextAllocId x]) ++
              [tagAlloc ((entryMemoryWithCaller q.callerMem).nextAllocId + 1) y]⟩ = q.callerMem := by
        rw [List.append_assoc]
        exact extractCallerMemory_append _ hCM
      rw [hX]
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact .inl (rm2_mem_allocIdsOf h')
        · cases h' with
          | head _ => exact .inr (.head _)
          | tail _ h'' => cases h''
      · cases h with
        | head _ => exact .inr (.tail _ (.head _))
        | tail _ h'' => cases h''
  let ⟨_, hExec⟩ := execProgV2_of_runs hInit hRuns
  let ⟨hWf, hBeh, _⟩ := spec_and_behaviorV2_of_exec_eq hExec
  refine ⟨hWf, ?_⟩
  rw [hList]
  exact hBeh

/-! ## Top-Level Crate Verification Theorem -/

theorem fake_case {k : Nat} {body : Body}
    (hBody : Trusted.MirSemantics.getElem? Captured.program.bodies k = some body)
    (hShape : body = fcBody body.identity)
    (hStatic : BodyStaticAdmittedV2 Captured.program body = true) :
    BodyVerifiedV2 Captured.program k body (Spec.specs.safety body.identity) := by
  refine ⟨hBody, hStatic, fun q hValid _ => ?_⟩
  refine fake_caller_correct k body.identity ?_ q ?_
  · rw [← hShape]; exact hBody
  · rw [← hShape]; exact hValid

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    match defId, hBody with
    | 0, hBody =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      exact ⟨rfl, by decide, fun q hValid _ => fake_eq_correct q hValid⟩
    | 1, hBody =>
      change some Captured.body_1 = some body at hBody
      cases hBody
      exact ⟨rfl, by decide, fun q hValid _ => eq_correct q hValid⟩
    | 2, hBody =>
      change some Captured.body_2 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 3, hBody =>
      change some Captured.body_3 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 4, hBody =>
      change some Captured.body_4 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 5, hBody =>
      change some Captured.body_5 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 6, hBody =>
      change some Captured.body_6 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 7, hBody =>
      change some Captured.body_7 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 8, hBody =>
      change some Captured.body_8 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 9, hBody =>
      change some Captured.body_9 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 10, hBody =>
      change some Captured.body_10 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 11, hBody =>
      change some Captured.body_11 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 12, hBody =>
      change some Captured.body_12 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 13, hBody =>
      change some Captured.body_13 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 14, hBody =>
      change some Captured.body_14 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 15, hBody =>
      change some Captured.body_15 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 16, hBody =>
      change some Captured.body_16 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 17, hBody =>
      change some Captured.body_17 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 18, hBody =>
      change some Captured.body_18 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 19, hBody =>
      change some Captured.body_19 = some body at hBody
      cases hBody; exact fake_case rfl rfl (by decide)
    | 20, hBody =>
      change some Captured.body_20 = some body at hBody
      cases hBody
      exact ⟨rfl, by decide, fun q hValid _ => (tag_ne_correct q hValid).1⟩
    | _ + 21, hBody =>
      change none = some body at hBody
      cases hBody
  · exact ⟨by decide, fun q hValid => (tag_ne_correct q hValid).2⟩

end Proof
