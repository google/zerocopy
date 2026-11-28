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

/-! ## Step, Prefix-Memory & CallerMemory Helpers -/

private theorem natBeq_add_left (n i j : Nat) :
    Nat.beq (n + i) (n + j) = Nat.beq i j := by
  cases h : Nat.beq i j with
  | true => rw [Nat.eq_of_beq_eq_true h, Nat.beq_refl]
  | false =>
    cases h2 : Nat.beq (n + i) (n + j) with
    | false => rfl
    | true =>
      have hIJ := Nat.add_left_cancel (Nat.eq_of_beq_eq_true h2)
      rw [hIJ, Nat.beq_refl] at h
      cases h

private theorem natBeq_add_ne (nid i j : Nat) (h : Nat.beq i j = false) :
    Nat.beq (nid + i) (nid + j) = false := by
  rw [natBeq_add_left, h]

private theorem natBeq_add_eq (nid i j : Nat) (h : Nat.beq i j = true) :
    Nat.beq (nid + i) (nid + j) = true := by
  rw [natBeq_add_left, h]

private theorem ite_bool_false {α : Type} (c : Bool) {a b : α}
    (h : c = false) :
    (if c = true then a else b) = b := by
  rw [h]; rfl

private theorem spansDisjoint_ownedBuf (elem : MirTy) (p : PtrVal)
    (cap : UInt64) :
    spansPairwiseDisjoint (ownedBufAccessSpans elem p cap) = true := by
  unfold ownedBufAccessSpans
  cases layoutOfTyV2 elem with
  | none => rfl
  | some lay =>
    cases p.allocId with
    | none => rfl
    | some aid =>
      dsimp only
      cases Nat.beq (cap.toNat * lay.size) 0 <;> rfl

private theorem spansDisjoint_vec_u8 (v : Val) :
    spansPairwiseDisjoint (refAccessSpans (.vec (.int .i8 false)) v) =
      true := by
  cases v <;> first | rfl | exact spansDisjoint_ownedBuf _ _ _

private theorem spansDisjoint3 {m1 m2 m3 : Bool} {a b c s1 s2 s3 n1 n2 n3 : Nat}
    (hab : Nat.beq a b = false) (hac : Nat.beq a c = false)
    (hbc : Nat.beq b c = false) :
    spansPairwiseDisjoint [(m1, a, s1, n1), (m2, b, s2, n2), (m3, c, s3, n3)] =
      true := by
  simp only [spansPairwiseDisjoint, spanDisjointWith, spanDisjoint, hab, hac,
    hbc, Bool.not_false, Bool.or_true, ite_true, Bool.and_true]

private theorem ite_bool_true {α : Type} (c : Bool) {a b : α}
    (h : c = true) :
    (if c = true then a else b) = a := by
  rw [h]; rfl

private theorem findAllocation_append_of_lt {id : AllocId}
    {pref ext : List Allocation}
    (hLt : ∀ a ∈ pref, a.allocId < id) :
    findAllocation id (pref ++ ext) = findAllocation id ext := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
    change (if Nat.beq x.allocId id then some x
        else findAllocation id (xs ++ ext)) =
      findAllocation id ext
    have hNe : Nat.beq x.allocId id = false := by
      cases hEq : Nat.beq x.allocId id with
      | false => rfl
      | true =>
        exact absurd (Nat.eq_of_beq_eq_true hEq)
          (Nat.ne_of_lt (hLt x (.head xs)))
    rw [hNe]
    exact ih (fun a ha => hLt a (.tail x ha))

private theorem replaceAllocation_append_of_lt {a' : Allocation}
    {pref ext : List Allocation}
    (hLt : ∀ a ∈ pref, a.allocId < a'.allocId) :
    replaceAllocation a' (pref ++ ext) =
      pref ++ replaceAllocation a' ext := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
    change (if Nat.beq x.allocId a'.allocId then a' :: (xs ++ ext)
        else x :: replaceAllocation a' (xs ++ ext)) =
      x :: (xs ++ replaceAllocation a' ext)
    have hNe : Nat.beq x.allocId a'.allocId = false := by
      cases hEq : Nat.beq x.allocId a'.allocId with
      | false => rfl
      | true =>
        exact absurd (Nat.eq_of_beq_eq_true hEq)
          (Nat.ne_of_lt (hLt x (.head xs)))
    rw [hNe]
    exact congrArg (x :: ·) (ih (fun a ha => hLt a (.tail x ha)))

private theorem findAllocation_cons_ne {id : AllocId} {x : Allocation}
    {xs : List Allocation} (h : Nat.beq x.allocId id = false) :
    findAllocation id (x :: xs) = findAllocation id xs := by
  change (if Nat.beq x.allocId id = true then some x
    else findAllocation id xs) = findAllocation id xs
  rw [h]; rfl

private theorem findAllocation_cons_eq {id : AllocId} {x : Allocation}
    {xs : List Allocation} (h : Nat.beq x.allocId id = true) :
    findAllocation id (x :: xs) = some x := by
  change (if Nat.beq x.allocId id = true then some x
    else findAllocation id xs) = some x
  rw [h]; rfl

private theorem replaceAllocation_cons_ne {a' x : Allocation}
    {xs : List Allocation} (h : Nat.beq x.allocId a'.allocId = false) :
    replaceAllocation a' (x :: xs) = x :: replaceAllocation a' xs := by
  change (if Nat.beq x.allocId a'.allocId = true then a' :: xs
    else x :: replaceAllocation a' xs) = x :: replaceAllocation a' xs
  rw [h]; rfl

private theorem replaceAllocation_cons_eq {a' x : Allocation}
    {xs : List Allocation} (h : Nat.beq x.allocId a'.allocId = true) :
    replaceAllocation a' (x :: xs) = a' :: xs := by
  change (if Nat.beq x.allocId a'.allocId = true then a' :: xs
    else x :: replaceAllocation a' xs) = a' :: xs
  rw [h]; rfl

private theorem maxAllocId_ge (a : Allocation) :
    ∀ allocs : List Allocation,
      a ∈ allocs → a.allocId ≤ maxAllocId allocs
  | [], h => by cases h
  | x :: xs, h => by
    cases h with
    | head _ =>
      dsimp only [maxAllocId]
      exact Nat.le_max_left _ _
    | tail _ hIn =>
      dsimp only [maxAllocId]
      exact Nat.le_trans (maxAllocId_ge a xs hIn) (Nat.le_max_right _ _)

private theorem mem_lt_entryNextAllocId (cm : CallerMemory) (k : Nat) :
    ∀ a ∈ cm.allocations,
      a.allocId < (entryMemoryWithCaller cm).nextAllocId + k := by
  intro a ha
  have h1 : a.allocId < maxAllocId cm.allocations + 1 :=
    Nat.lt_succ_of_le (maxAllocId_ge a cm.allocations ha)
  have h2 : maxAllocId cm.allocations + 1 ≤
      (entryMemoryWithCaller cm).nextAllocId := by
    dsimp only [entryMemoryWithCaller, maxAllocAndProvId]
    exact Nat.le_trans (Nat.succ_le_succ (Nat.le_max_left _ _)) (Nat.le_max_right _ _)
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h2) (Nat.le_add_right _ k)

private theorem findAllocation_append_nid {cm : CallerMemory}
    {ext : List Allocation} (k : Nat) :
    findAllocation ((entryMemoryWithCaller cm).nextAllocId + k)
        (cm.allocations ++ ext) =
      findAllocation ((entryMemoryWithCaller cm).nextAllocId + k) ext :=
  findAllocation_append_of_lt (mem_lt_entryNextAllocId cm k)

private theorem findAllocation_append_nid0 {cm : CallerMemory}
    {ext : List Allocation} :
    findAllocation (entryMemoryWithCaller cm).nextAllocId
        (cm.allocations ++ ext) =
      findAllocation (entryMemoryWithCaller cm).nextAllocId ext :=
  findAllocation_append_of_lt (mem_lt_entryNextAllocId cm 0)

private theorem replaceAllocation_append_nid {cm : CallerMemory}
    {a' : Allocation} {ext : List Allocation} {k : Nat}
    (hId : a'.allocId = (entryMemoryWithCaller cm).nextAllocId + k) :
    replaceAllocation a' (cm.allocations ++ ext) =
      cm.allocations ++ replaceAllocation a' ext :=
  replaceAllocation_append_of_lt
    (fun x hx => hId ▸ mem_lt_entryNextAllocId cm k x hx)

private theorem replaceAllocation_append_nid0 {cm : CallerMemory}
    {a' : Allocation} {ext : List Allocation}
    (hId : a'.allocId = (entryMemoryWithCaller cm).nextAllocId) :
    replaceAllocation a' (cm.allocations ++ ext) =
      cm.allocations ++ replaceAllocation a' ext :=
  replaceAllocation_append_of_lt
    (fun x hx => hId ▸ mem_lt_entryNextAllocId cm 0 x hx)

private theorem natNotElem_forall_ne {x : AllocId} :
    ∀ {l : List AllocId}, natNotElem x l = true → ∀ s ∈ l, x ≠ s
  | [], _, _, hs => by cases hs
  | l0 :: ls, hn, s, hs => by
    dsimp only [natNotElem] at hn
    cases hEq : Nat.beq x l0 with
    | true => rw [hEq] at hn; cases hn
    | false =>
      rw [hEq] at hn
      cases hs with
      | head _ => exact fun h => by rw [h, Nat.beq_refl] at hEq; cases hEq
      | tail _ hIn => exact natNotElem_forall_ne hn s hIn

private theorem findAllocation_in_valid_prefix {ext : List Allocation} :
    ∀ (seen : List AllocId) (pref : List Allocation),
      (∀ s ∈ seen, ∀ a ∈ pref, s ≠ a.allocId) →
      allocIdsValid seen pref = true →
      ∀ a ∈ pref, findAllocation a.allocId (pref ++ ext) = some a := by
  intro seen pref hSeen hVal a ha
  induction pref generalizing seen with
  | nil => cases ha
  | cons x xs ih =>
    dsimp only [allocIdsValid] at hVal
    cases h0 : Nat.beq x.allocId 0 with
    | true => rw [h0] at hVal; cases hVal
    | false =>
      rw [h0] at hVal
      cases hN : natNotElem x.allocId seen with
      | false => rw [hN] at hVal; cases hVal
      | true =>
        rw [hN] at hVal
        cases hB : Nat.blt x.bytes.length isizeMaxBytes with
        | false => rw [hB] at hVal; cases hVal
        | true =>
          rw [hB] at hVal
          cases hA : Nat.ble x.alignLog2 29 with
          | false => rw [hA] at hVal; cases hVal
          | true =>
            rw [hA] at hVal
            have hValidNotTail : ∀ y ∈ xs, x.allocId ≠ y.allocId := by
              have hAux : ∀ (sL : List AllocId) (ys : List Allocation),
                  x.allocId ∈ sL → allocIdsValid sL ys = true →
                  ∀ y ∈ ys, x.allocId ≠ y.allocId := by
                intro sL ys hInSL hV y hy hXY
                induction ys generalizing sL with
                | nil => cases hy
                | cons z zs ihZ =>
                  dsimp only [allocIdsValid] at hV
                  cases hz0 : Nat.beq z.allocId 0 with
                  | true => rw [hz0] at hV; cases hV
                  | false =>
                    rw [hz0] at hV
                    cases hzn : natNotElem z.allocId sL with
                    | false => rw [hzn] at hV; cases hV
                    | true =>
                      rw [hzn] at hV
                      cases hy with
                      | head _ =>
                        exact natNotElem_forall_ne hzn x.allocId hInSL hXY.symm
                      | tail _ hInZs =>
                        cases hzb : Nat.blt z.bytes.length isizeMaxBytes with
                        | false => rw [hzb] at hV; cases hV
                        | true =>
                          rw [hzb] at hV
                          cases hza : Nat.ble z.alignLog2 29 with
                          | false => rw [hza] at hV; cases hV
                          | true =>
                            rw [hza] at hV
                            exact ihZ (z.allocId :: sL)
                              (.tail z.allocId hInSL) hV hInZs
              exact hAux (x.allocId :: seen) xs (.head _) hVal
            cases ha with
            | head _ =>
              change (if Nat.beq a.allocId a.allocId then some a
                else findAllocation a.allocId (xs ++ ext)) = some a
              rw [Nat.beq_refl]
              rfl
            | tail _ hInXs =>
              have hXNeA : Nat.beq x.allocId a.allocId = false := by
                cases hEq : Nat.beq x.allocId a.allocId with
                | false => rfl
                | true =>
                  exact absurd (Nat.eq_of_beq_eq_true hEq)
                    (hValidNotTail a hInXs)
              change (if Nat.beq x.allocId a.allocId then some x
                else findAllocation a.allocId (xs ++ ext)) = some a
              rw [hXNeA]
              exact ih (x.allocId :: seen)
                (fun s hs y hy => by
                  cases hs with
                  | head _ => exact hValidNotTail y hy
                  | tail _ hInS => exact hSeen s hInS y (.tail x hy))
                hVal hInXs

private theorem extractCallerMemory_append_eq {cm : CallerMemory}
    {nid' : Nat} {ext : List Allocation}
    (hCM : validCallerMemory cm = true) :
    extractCallerMemory cm ⟨nid', cm.allocations ++ ext⟩ = cm := by
  cases cm with
  | mk allocs =>
    have hFind := findAllocation_in_valid_prefix (ext := ext) [] allocs
      (fun _ hs => by cases hs) hCM
    have hLoop : ∀ xs : List Allocation,
        (∀ a ∈ xs, findAllocation a.allocId (allocs ++ ext) = some a) →
        extractCallerAllocations ⟨nid', allocs ++ ext⟩ xs = xs := by
      intro xs hF
      induction xs with
      | nil => rfl
      | cons y ys ih =>
        dsimp only [extractCallerAllocations]
        rw [hF y (.head ys)]
        exact congrArg (y :: ·) (ih (fun a ha => hF a (.tail y ha)))
    dsimp only [extractCallerMemory]
    rw [hLoop allocs hFind]

private theorem natNotElem_false_of_mem {x : AllocId} :
    ∀ {l : List AllocId}, x ∈ l → natNotElem x l = false
  | [], h => by cases h
  | l0 :: ls, h => by
    dsimp only [natNotElem]
    cases hEq : Nat.beq x l0 with
    | true => rfl
    | false =>
      cases h with
      | head _ => rw [Nat.beq_refl] at hEq; cases hEq
      | tail _ hIn => exact natNotElem_false_of_mem hIn

private theorem natNotElem_true_of_forall {x : AllocId} :
    ∀ {l : List AllocId}, (∀ s ∈ l, s < x) → natNotElem x l = true
  | [], _ => rfl
  | l0 :: ls, h => by
    dsimp only [natNotElem]
    have hNe : Nat.beq x l0 = false := by
      cases hEq : Nat.beq x l0 with
      | false => rfl
      | true =>
        have h1 := Nat.eq_of_beq_eq_true hEq
        exact absurd (h1 ▸ h l0 (.head ls)) (Nat.lt_irrefl _)
    rw [hNe]
    exact natNotElem_true_of_forall (fun s hs => h s (.tail l0 hs))

private theorem mem_allocIdsOf {s : AllocId} :
    ∀ {l : List Allocation}, s ∈ allocIdsOf l → ∃ a ∈ l, a.allocId = s
  | [], h => by cases h
  | a :: rest, h => by
    cases h with
    | head _ => exact ⟨a, .head rest, rfl⟩
    | tail _ hIn =>
      let ⟨b, hb, hEq⟩ := mem_allocIdsOf hIn
      exact ⟨b, .tail a hb, hEq⟩

private theorem allocId_mem_allocIdsOf {a : Allocation} :
    ∀ {l : List Allocation}, a ∈ l → a.allocId ∈ allocIdsOf l
  | [], h => by cases h
  | b :: rest, h => by
    cases h with
    | head _ => exact .head _
    | tail _ hIn => exact .tail _ (allocId_mem_allocIdsOf hIn)

private theorem calleeLive_append (cIds fIds : List AllocId) :
    ∀ l1 l2 : List Allocation,
      calleeLiveAllocations cIds fIds (l1 ++ l2) =
        calleeLiveAllocations cIds fIds l1 ++
          calleeLiveAllocations cIds fIds l2
  | [], _ => rfl
  | a :: rest, l2 => by
    change (if (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId cIds &&
        natNotElem a.allocId fIds) = true then
        a :: calleeLiveAllocations cIds fIds (rest ++ l2)
      else calleeLiveAllocations cIds fIds (rest ++ l2)) =
      (if (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId cIds &&
        natNotElem a.allocId fIds) = true then
        a :: calleeLiveAllocations cIds fIds rest
      else calleeLiveAllocations cIds fIds rest) ++
        calleeLiveAllocations cIds fIds l2
    cases (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId cIds &&
        natNotElem a.allocId fIds) with
    | true =>
      exact congrArg (a :: ·) (calleeLive_append cIds fIds rest l2)
    | false =>
      exact calleeLive_append cIds fIds rest l2

private theorem calleeLive_caller (fIds : List AllocId)
    (cm : List Allocation) :
    ∀ l : List Allocation, (∀ a ∈ l, a ∈ cm) →
      calleeLiveAllocations (allocIdsOf cm) fIds l = []
  | [], _ => rfl
  | a :: rest, h => by
    change (if (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId (allocIdsOf cm) &&
        natNotElem a.allocId fIds) = true then
        a :: calleeLiveAllocations (allocIdsOf cm) fIds rest
      else calleeLiveAllocations (allocIdsOf cm) fIds rest) = []
    rw [natNotElem_false_of_mem (allocId_mem_allocIdsOf (h a (.head rest)))]
    rw [Bool.and_false, Bool.false_and]
    exact calleeLive_caller fIds cm rest (fun b hb => h b (.tail a hb))

private theorem calleeLive_cons_keep {cIds fIds : List AllocId}
    {a : Allocation} {rest : List Allocation}
    (hLive : a.live = true) (hC : natNotElem a.allocId cIds = true)
    (hF : natNotElem a.allocId fIds = true)
    (hMut : a.mutability = .mut := by rfl) :
    calleeLiveAllocations cIds fIds (a :: rest) =
      a :: calleeLiveAllocations cIds fIds rest := by
  change (if (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId cIds &&
      natNotElem a.allocId fIds) = true then
      a :: calleeLiveAllocations cIds fIds rest
    else calleeLiveAllocations cIds fIds rest) = _
  rw [hLive, hMut, hC, hF]; rfl

private theorem calleeLive_cons_dead {cIds fIds : List AllocId}
    {a : Allocation} {rest : List Allocation}
    (hLive : a.live = false) :
    calleeLiveAllocations cIds fIds (a :: rest) =
      calleeLiveAllocations cIds fIds rest := by
  change (if (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId cIds &&
      natNotElem a.allocId fIds) = true then
      a :: calleeLiveAllocations cIds fIds rest
    else calleeLiveAllocations cIds fIds rest) = _
  rw [hLive]; rfl

private theorem calleeLive_cons_frame {cIds fIds : List AllocId}
    {a : Allocation} {rest : List Allocation}
    (hF : natNotElem a.allocId fIds = false) :
    calleeLiveAllocations cIds fIds (a :: rest) =
      calleeLiveAllocations cIds fIds rest := by
  change (if (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId cIds &&
      natNotElem a.allocId fIds) = true then
      a :: calleeLiveAllocations cIds fIds rest
    else calleeLiveAllocations cIds fIds rest) = _
  rw [hF, Bool.and_false]; rfl

/-- On return from memory `cm ++ ext`, the caller-visible memory is `cm`
followed by the live callee allocations in `ext`. -/
private theorem extractReturnMemoryV2_append {cm : CallerMemory}
    {nid' : Nat} {ext : List Allocation} {locals : List LocalSlot}
    (hCM : validCallerMemory cm = true) :
    extractReturnMemoryV2 cm ⟨nid', cm.allocations ++ ext⟩ locals =
      ⟨cm.allocations ++ calleeLiveAllocations (allocIdsOf cm.allocations)
        (frameLocalAllocIds locals) ext⟩ := by
  unfold extractReturnMemoryV2
  rw [extractCallerMemory_append_eq hCM]
  rw [calleeLive_append, calleeLive_caller _ cm.allocations cm.allocations
    (fun _ h => h)]
  rfl

private theorem natNotElem_callerIds (cm : CallerMemory) (k : Nat) :
    natNotElem ((entryMemoryWithCaller cm).nextAllocId + k)
      (allocIdsOf cm.allocations) = true :=
  natNotElem_true_of_forall (fun _ hs =>
    let ⟨a, ha, hEq⟩ := mem_allocIdsOf hs
    hEq ▸ mem_lt_entryNextAllocId cm k a ha)

private inductive ChainStepV2 (p : Program) :
    State → StepResult State TerminalOut → Prop where
  | base {s : State} {r : StepResult State TerminalOut}
      (h : evalStepV2 p s = r) : ChainStepV2 p s r
  | step {s s' : State} {r : StepResult State TerminalOut}
      (h : evalStepV2 p s = .step s')
      (rest : ChainStepV2 p s' r) : ChainStepV2 p s r

private def isStepResult : StepResult State TerminalOut → Bool
  | .step _ => true
  | _ => false

private theorem reachesV2_chainStepV2 {p : Program} {s₀ s : State}
    {r : StepResult State TerminalOut}
    (hNonStep : isStepResult r = false)
    (hChain : ChainStepV2 p s₀ r) (hReach : ReachesV2 p s₀ s) :
    ChainStepV2 p s r := by
  induction hReach with
  | refl => exact hChain
  | tail _ hStep ih =>
    cases ih with
    | base hEnd =>
      let ⟨_, _, hEval⟩ := hStep
      have hEval' : evalStepV2 p _ = .step _ := hEval
      rw [hEnd] at hEval'
      rw [hEval'] at hNonStep
      cases hNonStep
    | step hNext rest =>
      let ⟨_, _, hEval⟩ := hStep
      have hEval' : evalStepV2 p _ = .step _ := hEval
      rw [hNext] at hEval'
      injection hEval' with hEq
      subst hEq
      exact rest

private theorem chainStepV2_reachesResultV2 {p : Program} {s : State}
    {r : StepResult State TerminalOut}
    (hChain : ChainStepV2 p s r) :
    ∃ sEnd, ReachesV2 p s sEnd ∧ StepV2 p sEnd r := by
  induction hChain with
  | @base sEnd r h => exact ⟨sEnd, .refl sEnd, ⟨0, rfl, h⟩⟩
  | @step s s' r h _ ih =>
    let ⟨sEnd, hRest, hEnd⟩ := ih
    exact ⟨sEnd, ReachesV2.head ⟨0, rfl, h⟩ hRest, hEnd⟩

private theorem spec_and_behaviorV2_of_chainStep {p : Program} {q : Query}
    {s₀ : State} {out : TerminalOut}
    (hInit : initStateV2 p q = .ok s₀)
    (hChain : ChainStepV2 p s₀ (.done out)) :
    WellFormedV2 p q ∧ BehaviorV2 p q out := by
  have hNon : isStepResult (.done out) = false := rfl
  refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_⟩
  · intro k hFault
    unfold ReachesResultV2 at hFault
    rw [hInit] at hFault
    let ⟨s, hReach, _, _, hEval⟩ := hFault
    have hEval' : evalStepV2 p s = .fault k := hEval
    cases reachesV2_chainStepV2 hNon hChain hReach with
    | base hDone => rw [hDone] at hEval'; cases hEval'
    | step hStep _ => rw [hStep] at hEval'; cases hEval'
  · unfold BehaviorV2 ReachesResultV2
    rw [hInit]
    exact chainStepV2_reachesResultV2 hChain

private inductive ChainTo (p : Program) : State → State → Prop where
  | refl (s : State) : ChainTo p s s
  | step {s s' s'' : State}
      (h : evalStepV2 p s = .step s')
      (rest : ChainTo p s' s'') : ChainTo p s s''

private theorem chainTo_chainStepV2 {p : Program} {s1 s2 : State}
    {r : StepResult State TerminalOut}
    (h1 : ChainTo p s1 s2) (h2 : ChainStepV2 p s2 r) :
    ChainStepV2 p s1 r := by
  induction h1 with
  | refl _ => exact h2
  | step h _ ih => exact .step h (ih h2)

private theorem chainTo_trans {p : Program} {s1 s2 s3 : State}
    (h1 : ChainTo p s1 s2) (h2 : ChainTo p s2 s3) : ChainTo p s1 s3 := by
  induction h1 with
  | refl _ => exact h2
  | step h _ ih => exact .step h (ih h2)

/-! ## O(1) Small-Step, Memory, and Contract Helpers -/

private theorem getElem_statements_length_none {α : Type} :
    ∀ xs : List α, Trusted.MirSemantics.getElem? xs xs.length = none
  | [] => rfl
  | _ :: rest => getElem_statements_length_none rest

private theorem evalStepV2_stmt {p : Program} {s : State} {frame : FrameState}
    {body : Body} {bb : BasicBlock} {stmt : StatementKind}
    (hF : s.frames = [frame])
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt :
      Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx = some stmt) :
    evalStepV2 p s = evalStatementV2 body frame s.mem s.callerMem stmt := by
  unfold evalStepV2; rw [hF]; dsimp only; rw [hB]; dsimp only
  rw [hBB]; dsimp only; rw [hSt]

private theorem evalStepV2_term {p : Program} {s : State} {frame : FrameState}
    {body : Body} {bb : BasicBlock}
    (hF : s.frames = [frame])
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hEnd : frame.stmtIdx = bb.statements.length) :
    evalStepV2 p s =
      evalTerminatorV2 body bb frame s.mem s.callerMem p.panicStrategy
        p.hasLocalPanicHandler p.overflowChecks := by
  unfold evalStepV2; rw [hF]; dsimp only; rw [hB]; dsimp only
  rw [hBB]; dsimp only; rw [hEnd, getElem_statements_length_none]
  simp only [Nat.beq_refl]; rfl

private theorem readBytes_ok {m : MemoryState} {place : MemPlace}
    {size alignLog2 : Nat} {a : Allocation}
    (hSz : Nat.beq size 0 = false)
    (hFind : findAllocation place.allocId m.allocations = some a)
    (hLive : a.live = true)
    (hBounds : isInBounds a place.offset size = true)
    (hAlign : isAligned a place.offset alignLog2 = true) :
    readBytes m place size alignLog2 =
      .ok ((a.bytes.drop place.offset).take size) := by
  unfold readBytes
  rw [hFind]; dsimp only
  rw [ite_bool_false (Nat.beq size 0) hSz]
  rw [ite_bool_false
    (!a.live || !isInBounds a place.offset size ||
      !isAligned a place.offset alignLog2)
    (by rw [hLive, hBounds, hAlign]; rfl)]

private theorem writeBytes_ok {m : MemoryState} {place : MemPlace}
    {alignLog2 : Nat} {bs : List AllocByte} (a : Allocation)
    (hBs : Nat.beq bs.length 0 = false)
    (hFind : findAllocation place.allocId m.allocations = some a)
    (hLive : a.live = true)
    (hBounds : isInBounds a place.offset bs.length = true)
    (hAlign : isAligned a place.offset alignLog2 = true)
    (hMut : a.mutability = .mut) :
    writeBytes m place alignLog2 bs =
      .ok ⟨m.nextAllocId, replaceAllocation
        ⟨a.allocId, a.alignLog2, a.mutability,
          a.bytes.take place.offset ++ bs ++
            a.bytes.drop (place.offset + bs.length),
          a.live⟩
        m.allocations⟩ := by
  unfold writeBytes
  rw [hFind]; dsimp only
  rw [ite_bool_false (Nat.beq bs.length 0) hBs]
  rw [ite_bool_false
    (!a.live || !isInBounds a place.offset bs.length ||
      !isAligned a place.offset alignLog2)
    (by rw [hLive, hBounds, hAlign]; rfl)]
  rw [hMut]

private theorem writeUninit_ok {m m' : MemoryState} {place : MemPlace}
    {size alignLog2 : Nat}
    (hW : writeBytes m place alignLog2 (List.replicate size .uninit) = .ok m') :
    writeUninit m place size alignLog2 = .ok m' := hW

private theorem loadIndirectV2_ok {m : MemoryState} {ty : MirTy}
    {place : MemPlace} {lay : LayoutData} {bs : List AllocByte}
    {optVal : Option Val}
    (hLay : layoutOfTyV2 ty = some lay)
    (hRead : readBytes m place lay.size lay.alignLog2 = .ok bs)
    (hDec : decodeValV2 profileV2TargetEndian ty bs = .ok optVal) :
    loadIndirectV2 m ty place = .ok optVal := by
  unfold loadIndirectV2; rw [hLay]; dsimp only; rw [hRead]; dsimp only
  exact hDec

private theorem storeIndirectV2_ok {m m' : MemoryState} {ty : MirTy}
    {place : MemPlace} {val : Val} {lay : LayoutData} {bs : List AllocByte}
    (hLay : layoutOfTyV2 ty = some lay)
    (hEnc : encodeValV2 profileV2TargetEndian ty val = .ok bs)
    (hWrite : writeBytes m place lay.alignLog2 bs = .ok m') :
    storeIndirectV2 m ty place val = .ok m' := by
  unfold storeIndirectV2; rw [hLay]; dsimp only; rw [hEnc]; dsimp only
  exact hWrite

private theorem deallocateStack_ok {m : MemoryState} {place : MemPlace}
    (a : Allocation)
    (hOff : Nat.beq place.offset 0 = true)
    (hFind : findAllocation place.allocId m.allocations = some a)
    (hLive : a.live = true)
    (hMut : a.mutability = .mut) :
    deallocateStack m place =
      .ok ⟨m.nextAllocId, replaceAllocation
        ⟨a.allocId, a.alignLog2, a.mutability, a.bytes, false⟩
        m.allocations⟩ := by
  unfold deallocateStack
  rw [ite_bool_false (!Nat.beq place.offset 0) (by rw [hOff]; rfl)]
  rw [hFind]; dsimp only
  rw [ite_bool_false (!a.live) (by rw [hLive]; rfl)]
  rw [hMut]

private theorem readPtrProv_init8 (aid : AllocId)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    readPtrProv? [.init b0 (some aid), .init b1 (some aid),
      .init b2 (some aid), .init b3 (some aid), .init b4 (some aid),
      .init b5 (some aid), .init b6 (some aid), .init b7 (some aid)] =
      some (some aid) := by
  dsimp only [readPtrProv?, provMatch]
  simp only [Nat.beq_refl, ite_true]

private theorem encodeValV2_vec_u8 (aid : AllocId) (cap len : UInt64) :
    encodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
        (.vec ⟨some aid, 0, .isize⟩ cap len) =
      .ok (List.replicate 8 (.init 0 (some aid)) ++
        (encodeUInt .little 8 cap.toNat).map (fun b => .init b none) ++
        (encodeUInt .little 8 len.toNat).map (fun b => .init b none)) := by
  have hZ : encodeUInt profileV2TargetEndian 8 (UInt64.toNat 0) =
      [0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have hChk : checkValV2 (.vec ⟨some aid, 0, .isize⟩ cap len)
      (.vec (.int .i8 false)) = true := rfl
  delta encodeValV2; dsimp only; delta encodeValV2._f; dsimp only
  rw [hChk]; try dsimp only
  rw [hZ]; rfl

private theorem encodeValV2_vec_dangling (off cap len : UInt64) :
    encodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
        (.vec ⟨none, off, .isize⟩ cap len) =
      .ok ((encodeUInt .little 8 off.toNat).map (fun b => .init b none) ++
        (encodeUInt .little 8 cap.toNat).map (fun b => .init b none) ++
        (encodeUInt .little 8 len.toNat).map (fun b => .init b none)) := by
  have hChk : checkValV2 (.vec ⟨none, off, .isize⟩ cap len)
      (.vec (.int .i8 false)) = true := rfl
  delta encodeValV2; dsimp only; delta encodeValV2._f; dsimp only
  rw [hChk]; rfl

private theorem encodeValV2_box_slice_u8 (aid : AllocId) (len : UInt64) :
    encodeValV2 profileV2TargetEndian (.box (.slice (.int .i8 false)))
        (.boxPtr ⟨some aid, 0, .isize⟩ (some len)) =
      .ok (List.replicate 8 (.init 0 (some aid)) ++
        (encodeUInt .little 8 len.toNat).map (fun b => .init b none)) := by
  have hZ : encodeUInt profileV2TargetEndian 8 (UInt64.toNat 0) =
      [0, 0, 0, 0, 0, 0, 0, 0] := rfl
  have hChk : checkValV2 (.boxPtr ⟨some aid, 0, .isize⟩ (some len))
      (.box (.slice (.int .i8 false))) = true := rfl
  delta encodeValV2; dsimp only; delta encodeValV2._f; dsimp only
  rw [hChk]; try dsimp only
  rw [hZ]; rfl

private theorem decodeValV2_vec_u8_zero (aid : AllocId)
    (c0 c1 c2 c3 c4 c5 c6 c7 l0 l1 l2 l3 l4 l5 l6 l7 : UInt8) :
    decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
        [.init 0 (some aid), .init 0 (some aid), .init 0 (some aid),
         .init 0 (some aid), .init 0 (some aid), .init 0 (some aid),
         .init 0 (some aid), .init 0 (some aid),
         .init c0 none, .init c1 none, .init c2 none, .init c3 none,
         .init c4 none, .init c5 none, .init c6 none, .init c7 none,
         .init l0 none, .init l1 none, .init l2 none, .init l3 none,
         .init l4 none, .init l5 none, .init l6 none, .init l7 none] =
      .ok (some (.vec ⟨some aid, 0, .isize⟩
        (UInt64.ofNat (decodeUInt profileV2TargetEndian
          [c0, c1, c2, c3, c4, c5, c6, c7]))
        (UInt64.ofNat (decodeUInt profileV2TargetEndian
          [l0, l1, l2, l3, l4, l5, l6, l7])))) := by
  delta decodeValV2; dsimp only; delta decodeValV2._f; dsimp only
  dsimp only [List.length, List.take, List.drop, initBytes?]
  rw [readPtrProv_init8]; rfl

private theorem decodeValV2_box_slice_u8_zero (aid : AllocId)
    (l0 l1 l2 l3 l4 l5 l6 l7 : UInt8) :
    decodeValV2 profileV2TargetEndian (.box (.slice (.int .i8 false)))
        [.init 0 (some aid), .init 0 (some aid), .init 0 (some aid),
         .init 0 (some aid), .init 0 (some aid), .init 0 (some aid),
         .init 0 (some aid), .init 0 (some aid),
         .init l0 none, .init l1 none, .init l2 none, .init l3 none,
         .init l4 none, .init l5 none, .init l6 none, .init l7 none] =
      .ok (some (.boxPtr ⟨some aid, 0, .isize⟩ (some (UInt64.ofNat
        (decodeUInt profileV2TargetEndian [l0, l1, l2, l3, l4, l5, l6, l7])))))
    := by
  delta decodeValV2; dsimp only; delta decodeValV2._f; dsimp only
  dsimp only [List.length, List.take, List.drop, initBytes?]
  rw [readPtrProv_init8]; rfl

private theorem decodeValV2_vec_u8_dangling (off c0 c1 c2 c3 c4 c5 c6 c7
    l0 l1 l2 l3 l4 l5 l6 l7 : UInt8) :
    decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
        [.init off none, .init 0 none, .init 0 none, .init 0 none,
         .init 0 none, .init 0 none, .init 0 none, .init 0 none,
         .init c0 none, .init c1 none, .init c2 none, .init c3 none,
         .init c4 none, .init c5 none, .init c6 none, .init c7 none,
         .init l0 none, .init l1 none, .init l2 none, .init l3 none,
         .init l4 none, .init l5 none, .init l6 none, .init l7 none] =
      .ok (some (.vec
        ⟨none, UInt64.ofNat (decodeUInt profileV2TargetEndian
          [off, 0, 0, 0, 0, 0, 0, 0]), .isize⟩
        (UInt64.ofNat (decodeUInt profileV2TargetEndian
          [c0, c1, c2, c3, c4, c5, c6, c7]))
        (UInt64.ofNat (decodeUInt profileV2TargetEndian
          [l0, l1, l2, l3, l4, l5, l6, l7])))) := by
  rfl

private theorem layoutOfTyV2_vec_u8 :
    layoutOfTyV2 (.vec (.int .i8 false)) = some ⟨24, 3⟩ := rfl
private theorem layoutOfTyV2_box_slice_u8 :
    layoutOfTyV2 (.box (.slice (.int .i8 false))) = some ⟨16, 3⟩ := rfl
private theorem layoutOfTyV2_box_u64 :
    layoutOfTyV2 (.box (.int .i64 false)) = some ⟨8, 3⟩ := rfl
private theorem layoutOfTyV2_u8 :
    layoutOfTyV2 (.int .i8 false) = some ⟨1, 0⟩ := rfl
private theorem layoutOfTyV2_u64 :
    layoutOfTyV2 (.int .i64 false) = some ⟨8, 3⟩ := rfl

private theorem ptrGuard_u8 :
    (!isSupportedV2PointeeTy (.int .i8 false) &&
      !isHeapHandleTyV2 (.int .i8 false)) = false := by decide
private theorem ptrGuard_u64 :
    (!isSupportedV2PointeeTy (.int .i64 false) &&
      !isHeapHandleTyV2 (.int .i64 false)) = false := by decide
private theorem ptrGuard_boxSlice :
    (!isSupportedV2PointeeTy (.box (.slice (.int .i8 false))) &&
      !isHeapHandleTyV2 (.box (.slice (.int .i8 false)))) = false := by decide
private theorem sliceGuard_u8 :
    (!isSizedNoRefV2Ty (.int .i8 false)) = false := by decide

private theorem heapBufValidInMem_int_ok {m : MemoryState} {isMut : Bool}
    {w : IntWidth} {signed : Bool} {aid : AllocId} {off : UInt64}
    {cap len : UInt64} {lay : LayoutData} (a : Allocation)
    (hLay : layoutOfTyV2 (.int w signed) = some lay)
    (hLaySz : Nat.beq lay.size 0 = false)
    (hLenCap : Nat.ble len.toNat cap.toNat = true)
    (hBound : Nat.blt (cap.toNat * lay.size) isizeMaxBytes = true)
    (hCapPos : Nat.beq cap.toNat 0 = false)
    (hFind : findAllocation aid m.allocations = some a)
    (hLive : a.live = true)
    (hInB : isInBounds a off.toNat (cap.toNat * lay.size) = true)
    (hAlign : isAligned a off.toNat lay.alignLog2 = true)
    (hMut : (isMut && !Mutability.beq a.mutability .mut) = false)
    (hInit : isSliceAllInit
      ((a.bytes.drop off.toNat).take (len.toNat * lay.size)) = true) :
    heapBufValidInMem m isMut (.int w signed) ⟨some aid, off, .isize⟩ cap len =
      .ok () := by
  unfold heapBufValidInMem
  rw [ite_bool_false (!IntWidth.beq .isize .isize) rfl]
  rw [hLay]; dsimp only
  rw [ite_bool_false (!Nat.ble len.toNat cap.toNat) (by rw [hLenCap]; rfl)]
  rw [ite_bool_false (!Nat.blt (cap.toNat * lay.size) isizeMaxBytes)
    (by rw [hBound]; rfl)]
  rw [ite_bool_false (Nat.beq lay.size 0) hLaySz]
  rw [ite_bool_false (Nat.beq cap.toNat 0) hCapPos]
  rw [hFind]; dsimp only
  rw [ite_bool_false
    (!a.live || !isInBounds a off.toNat (cap.toNat * lay.size) ||
      !isAligned a off.toNat lay.alignLog2)
    (by rw [hLive, hInB, hAlign]; rfl)]
  rw [ite_bool_false (isMut && !Mutability.beq a.mutability .mut) hMut]
  rw [ite_bool_false
    (!isSliceAllInit
      ((a.bytes.drop off.toNat).take (len.toNat * lay.size)))
    (by rw [hInit]; rfl)]
  rw [ite_bool_true (isIntMirTy (.int w signed)) rfl]

private theorem heapBufValidInMem_zero_ok {m : MemoryState} {isMut : Bool}
    {w : IntWidth} {signed : Bool} {off : UInt64} {lay : LayoutData}
    (hLay : layoutOfTyV2 (.int w signed) = some lay)
    (hLaySz : Nat.beq lay.size 0 = false)
    (hOffNz : Nat.beq off.toNat 0 = false)
    (hOffAl : Nat.beq (Nat.mod off.toNat (Nat.pow 2 lay.alignLog2)) 0 = true) :
    heapBufValidInMem m isMut (.int w signed) ⟨none, off, .isize⟩ 0 0 =
      .ok () := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  unfold heapBufValidInMem
  rw [ite_bool_false (!IntWidth.beq .isize .isize) rfl]
  rw [hLay]; dsimp only
  rw [hZ0]
  rw [ite_bool_false (!Nat.ble 0 0) rfl]
  rw [Nat.zero_mul]
  rw [ite_bool_false (!Nat.blt 0 isizeMaxBytes) rfl]
  rw [ite_bool_false (Nat.beq lay.size 0) hLaySz]
  rw [ite_bool_true (Nat.beq 0 0) rfl]
  unfold zeroCapPtrValidInMem
  rw [ite_bool_false
    (Nat.beq off.toNat 0 ||
      !Nat.beq (Nat.mod off.toNat (Nat.pow 2 lay.alignLog2)) 0)
    (by rw [hOffNz, hOffAl]; rfl)]

private theorem ownedBuf_of_heap {m : MemoryState} {isMut : Bool}
    {w : IntWidth} {signed : Bool} {aid : AllocId}
    {cap len : UInt64} {lay : LayoutData} (a : Allocation)
    (hHeap : heapBufValidInMem m isMut (.int w signed)
      ⟨some aid, 0, .isize⟩ cap len = .ok ())
    (hLay : layoutOfTyV2 (.int w signed) = some lay)
    (hLaySz : Nat.beq lay.size 0 = false)
    (hCapPos : Nat.beq cap.toNat 0 = false)
    (hFind : findAllocation aid m.allocations = some a)
    (hLenEq : Nat.beq a.bytes.length (cap.toNat * lay.size) = true)
    (hAlEq : Nat.beq a.alignLog2 lay.alignLog2 = true) :
    ownedHeapBufValidInMem m isMut (.int w signed) ⟨some aid, 0, .isize⟩
      cap len = .ok () := by
  unfold ownedHeapBufValidInMem
  rw [hHeap]; dsimp only; rw [hLay]; dsimp only
  rw [ite_bool_false (Nat.beq lay.size 0 || Nat.beq cap.toNat 0)
    (by rw [hLaySz, hCapPos]; rfl)]
  rw [hFind]; dsimp only
  rw [ite_bool_false (!Nat.beq (UInt64.toNat 0) 0 ||
      !Nat.beq a.bytes.length (cap.toNat * lay.size) ||
      !Nat.beq a.alignLog2 lay.alignLog2)
    (by rw [hLenEq, hAlEq]; rfl)]

private theorem ownedBuf_int_ok {m : MemoryState} {isMut : Bool}
    {w : IntWidth} {signed : Bool} {aid : AllocId}
    {cap len : UInt64} {lay : LayoutData} (a : Allocation)
    (hLay : layoutOfTyV2 (.int w signed) = some lay)
    (hLaySz : Nat.beq lay.size 0 = false)
    (hLenCap : Nat.ble len.toNat cap.toNat = true)
    (hBound : Nat.blt (cap.toNat * lay.size) isizeMaxBytes = true)
    (hCapPos : Nat.beq cap.toNat 0 = false)
    (hFind : findAllocation aid m.allocations = some a)
    (hLive : a.live = true)
    (hInB : isInBounds a (UInt64.toNat 0) (cap.toNat * lay.size) = true)
    (hAlign : isAligned a (UInt64.toNat 0) lay.alignLog2 = true)
    (hMut : (isMut && !Mutability.beq a.mutability .mut) = false)
    (hInit : isSliceAllInit
      ((a.bytes.drop (UInt64.toNat 0)).take (len.toNat * lay.size)) = true)
    (hLenEq : Nat.beq a.bytes.length (cap.toNat * lay.size) = true := by rfl)
    (hAlEq : Nat.beq a.alignLog2 lay.alignLog2 = true := by rfl) :
    ownedHeapBufValidInMem m isMut (.int w signed) ⟨some aid, 0, .isize⟩
      cap len = .ok () :=
  ownedBuf_of_heap a
    (heapBufValidInMem_int_ok a hLay hLaySz hLenCap hBound hCapPos hFind
      hLive hInB hAlign hMut hInit)
    hLay hLaySz hCapPos hFind hLenEq hAlEq

private theorem ownedBuf_zero_ok {m : MemoryState} {isMut : Bool}
    {w : IntWidth} {signed : Bool} {off : UInt64} {lay : LayoutData}
    (hLay : layoutOfTyV2 (.int w signed) = some lay)
    (hLaySz : Nat.beq lay.size 0 = false)
    (hOffNz : Nat.beq off.toNat 0 = false)
    (hOffAl : Nat.beq (Nat.mod off.toNat (Nat.pow 2 lay.alignLog2)) 0 = true) :
    ownedHeapBufValidInMem m isMut (.int w signed) ⟨none, off, .isize⟩ 0 0 =
      .ok () := by
  unfold ownedHeapBufValidInMem
  rw [heapBufValidInMem_zero_ok hLay hLaySz hOffNz hOffAl]; dsimp only
  rw [hLay]; dsimp only
  rw [ite_bool_true (Nat.beq lay.size 0 || Nat.beq (UInt64.toNat 0) 0)
    (by rw [hLaySz]; rfl)]

private theorem sliceFromRawPartsCheck_u8_ok {m : MemoryState} {isMut : Bool}
    {aid : AllocId} {off len : UInt64} (a : Allocation)
    (hBound : Nat.blt (len.toNat * 1) isizeMaxBytes = true)
    (hFind : findAllocation aid m.allocations = some a)
    (hLive : a.live = true)
    (hInB : isInBounds a off.toNat (len.toNat * 1) = true)
    (hAlign : isAligned a off.toNat 0 = true)
    (hMut : (isMut && !Mutability.beq a.mutability .mut) = false)
    (hInit : isSliceAllInit
      ((a.bytes.drop off.toNat).take (len.toNat * 1)) = true) :
    sliceFromRawPartsCheck m isMut 1 0 ⟨some aid, off, .isize⟩ len =
      .ok (.slicePtr ⟨some aid, off, .isize⟩ len) := by
  unfold sliceFromRawPartsCheck sliceRefRawCheck; dsimp only
  rw [ite_bool_false (!Nat.blt (len.toNat * 1) isizeMaxBytes)
    (by rw [hBound]; rfl)]
  rw [hFind]; dsimp only
  rw [ite_bool_false
    (!a.live || !isInBounds a off.toNat (len.toNat * 1) ||
      !isAligned a off.toNat 0)
    (by rw [hLive, hInB, hAlign]; rfl)]
  rw [ite_bool_false (isMut && !Mutability.beq a.mutability .mut) hMut]
  dsimp only
  rw [ite_bool_false
    (!isSliceAllInit ((a.bytes.drop off.toNat).take (len.toNat * 1)))
    (by rw [hInit]; rfl)]

private theorem refValidInMem_vec_u8_ok {m : MemoryState}
    {reqMut : Mutability} {aid : AllocId} {a : Allocation}
    {bufPtr : PtrVal} {cap len : UInt64}
    (hFind : findAllocation aid m.allocations = some a)
    (hLive : a.live = true)
    (hInB : isInBounds a 0 24 = true)
    (hAlign : isAligned a 0 3 = true)
    (hMut : (Mutability.beq reqMut .mut &&
      !Mutability.beq a.mutability .mut) = false)
    (hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      ((a.bytes.drop 0).take 24) = .ok (some (.vec bufPtr cap len)))
    (hBuf : ownedHeapBufValidInMem m (Mutability.beq reqMut .mut)
      (.int .i8 false) bufPtr cap len = .ok ()) :
    refValidInMem m reqMut (.vec (.int .i8 false))
      (.ptr ⟨some aid, UInt64.ofNat 0, .isize⟩) = .ok () := by
  have hZ0 : (UInt64.ofNat 0).toNat = 0 := rfl
  unfold refValidInMem
  rw [layoutOfTyV2_vec_u8]; dsimp only
  rw [hFind, hZ0]; dsimp only
  rw [ite_bool_false
    (!a.live || !isInBounds a 0 24 || !isAligned a 0 3)
    (by rw [hLive, hInB, hAlign]; rfl)]
  rw [ite_bool_false
    (Mutability.beq reqMut .mut && !Mutability.beq a.mutability .mut) hMut]
  rw [hDec]; exact hBuf

private theorem readVecFromRef_u8_ok {m : MemoryState} {reqMut : Bool}
    {aid : AllocId} {bufPtr : PtrVal} {cap len : UInt64}
    (hRef : refValidInMem m (if reqMut then .mut else .shared)
      (.vec (.int .i8 false)) (.ptr ⟨some aid, UInt64.ofNat 0, .isize⟩) =
      .ok ())
    (hLoad : loadIndirectV2 m (.vec (.int .i8 false)) ⟨aid, 0⟩ =
      .ok (some (.vec bufPtr cap len)))
    (hBuf : ownedHeapBufValidInMem m reqMut (.int .i8 false) bufPtr cap len =
      .ok ()) :
    readVecFromRef m reqMut (.int .i8 false)
      ⟨some aid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, bufPtr, cap, len⟩ := by
  have hZ0 : (UInt64.ofNat 0).toNat = 0 := rfl
  unfold readVecFromRef
  rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false)) rfl]
  dsimp only
  rw [hRef]; dsimp only; rw [hZ0, hLoad]; dsimp only [vecValidInMem]
  rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false)) rfl]
  rw [hBuf]

private theorem writeVecToRef_u8_ok {m m' : MemoryState} {aid : AllocId}
    {bufPtr : PtrVal} {cap len : UInt64}
    (hStore : storeIndirectV2 m (.vec (.int .i8 false)) ⟨aid, 0⟩
      (.vec bufPtr cap len) = .ok m') :
    writeVecToRef m ⟨some aid, UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, bufPtr, cap, len⟩ = .ok m' := by
  have hZ0 : (UInt64.ofNat 0).toNat = 0 := rfl
  unfold writeVecToRef
  dsimp only [VecModel.toVal]; rw [hZ0]; exact hStore

private theorem writePlaceV2_local {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {ty : MirTy} {val : Val} :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val =
      writePlaceDestV2 locals mem (.local lid) ty val := rfl

private theorem writePlaceDestV2_imm_ok {locals locals' : List LocalSlot}
    {mem : MemoryState} {lid : LocalId} {ty : MirTy} {val : Val}
    {oldOpt : Option Val}
    (hChk : checkValV2 val ty = true)
    (hGet : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid
      (.immediate (some val)) = some locals') :
    writePlaceDestV2 locals mem (.local lid) ty val = .ok (locals', mem) :=
  by
  unfold writePlaceDestV2
  rw [ite_bool_false (!checkValV2 val ty) (by rw [hChk]; rfl)]
  dsimp only; rw [hGet]; dsimp only; rw [hSet]

private theorem writePlaceV2_imm_ok {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem : MemoryState}
    {lid : LocalId} {ty : MirTy} {val : Val} {oldOpt : Option Val}
    (hChk : checkValV2 val ty = true)
    (hGet : Trusted.MirSemantics.getElem? locals lid = some (.immediate oldOpt))
    (hSet : Trusted.MirSemantics.setElem? locals lid
      (.immediate (some val)) = some locals') :
    writePlaceV2 bodyLocals locals mem ⟨lid, []⟩ ty val = .ok (locals', mem) :=
  writePlaceV2_local.trans (writePlaceDestV2_imm_ok hChk hGet hSet)

private theorem promoteLocalToMemory_imm_ok {bodyLocals : List MirTy}
    {locals locals1 : List LocalSlot} {mem mem2 : MemoryState}
    {src : LocalId} {localTy : MirTy} {val : Val} {lay : LayoutData}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals src = some localTy)
    (hSlot : Trusted.MirSemantics.getElem? locals src =
      some (.immediate (some val)))
    (hLay : layoutOfTyV2 localTy = some lay)
    (hStore : storeIndirectV2
      ⟨mem.nextAllocId + 1, mem.allocations ++
        [⟨mem.nextAllocId, lay.alignLog2, .mut,
          List.replicate lay.size .uninit, true⟩]⟩
      localTy ⟨mem.nextAllocId, 0⟩ val = .ok mem2)
    (hSet : Trusted.MirSemantics.setElem? locals src
      (.indirect ⟨mem.nextAllocId, 0⟩) = some locals1) :
    promoteLocalToMemory bodyLocals locals mem src =
      .ok (localTy, ⟨mem.nextAllocId, 0⟩, locals1, mem2) := by
  unfold promoteLocalToMemory allocateStack MemoryState.reserveAllocId
  rw [hTy, hSlot]; dsimp only; rw [hLay]; dsimp only; rw [hStore]; dsimp only
  rw [hSet]

private theorem evalStepV2_assign_ref_local {p : Program} {frame : FrameState}
    {mem mem1 : MemoryState} {cm : CallerMemory} {body : Body}
    {bb : BasicBlock} {dst src : LocalId} {reqMut : Mutability}
    {localTy : MirTy} {mplace : MemPlace} {locals1 locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.ref reqMut ⟨src, []⟩)))
    (hTy : placeStaticTyV2 body.locals ⟨dst, []⟩ = some (.ref reqMut localTy))
    (hProm : promoteLocalToMemory body.locals frame.locals mem src =
      .ok (localTy, mplace, locals1, mem1))
    (hRef : refValidInMem mem1 reqMut localTy
      (.ptr ⟨some mplace.allocId, UInt64.ofNat mplace.offset, .isize⟩) =
      .ok ())
    (hWp : writePlaceV2 body.locals locals1 mem1 ⟨dst, []⟩ (.ref reqMut localTy)
      (.ptr ⟨some mplace.allocId, UInt64.ofNat mplace.offset, .isize⟩) =
      .ok (locals2, mem1)) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem1⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalRefRvalueV2; dsimp only; rw [hProm]; dsimp only
  rw [MirTy.beq_iff.mpr rfl, hRef]
  rw [ite_bool_false (!true) rfl]; dsimp only; rw [hWp]; rfl

/-- A `CoreCallOutcome` whose `Except` projection is `.ok (v, m)` is
`.ok v m`. -/
private theorem coreOutcome_eq_ok {o : CoreCallOutcome} {v : Val}
    {m : MemoryState} (h : o.toExcept = .ok (v, m)) : o = .ok v m := by
  cases o <;> unfold CoreCallOutcome.toExcept at h <;> cases h <;> rfl

/-- `CoreCallOutcome.ofExcept` round-trips through `toExcept`. -/
private theorem coreOutcome_toExcept_ofExcept
    (e : Except FaultKind (Val × MemoryState)) :
    (CoreCallOutcome.ofExcept e).toExcept = e := by
  cases e with
  | error k => rfl
  | ok r => cases r; rfl

/-- An allocation call without a modeled panic path returns the result of
`execAllocCoreCallInfallible`. -/
private theorem execCoreCallOpWithMem_eq_allocInfallible {m : MemoryState}
    {op : CoreCallOp} {args : List (MirTy × Val)} {dstTy : MirTy}
    {e : Except FaultKind (Val × MemoryState)}
    (hO : execAllocCoreCallOutcome m op args dstTy =
      match execAllocCoreCallInfallible m op args dstTy with
      | some res => some (CoreCallOutcome.ofExcept res)
      | none => none)
    (h : execAllocCoreCallInfallible m op args dstTy = some e) :
    execCoreCallOpWithMem m op args dstTy = e := by
  unfold execCoreCallOpWithMem execCoreCallOpWithMemOutcome
  rw [hO, h]; exact coreOutcome_toExcept_ofExcept e

/-- An allocation call whose outcome is `.ok v m'` returns `.ok (v, m')`. -/
private theorem execCoreCallOpWithMem_eq_allocOutcome {m m' : MemoryState}
    {op : CoreCallOp} {args : List (MirTy × Val)} {dstTy : MirTy} {v : Val}
    (h : execAllocCoreCallOutcome m op args dstTy = some (.ok v m')) :
    execCoreCallOpWithMem m op args dstTy = .ok (v, m') := by
  unfold execCoreCallOpWithMem execCoreCallOpWithMemOutcome
  rw [h]; rfl

private theorem evalStepV2_coreCall {p : Program} {frame : FrameState}
    {mem mem2 mem3 : MemoryState} {cm : CallerMemory} {body : Body}
    {bb : BasicBlock} {op : CoreCallOp} {args : List Operand} {dst : Place}
    {target : BasicBlockId} {uw : UnwindAction} {dstTy : MirTy}
    {typedArgs : List (MirTy × Val)} {resVal : Val}
    {locals1 locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hEnd : frame.stmtIdx = bb.statements.length)
    (hTerm : bb.terminator = .coreCall op args dst (some target) uw)
    (hNoProj : dst.projection.isEmpty = true)
    (hTy : Trusted.MirSemantics.getElem? body.locals dst.localId = some dstTy)
    (hArgs : evalArgOperandsV2 body.locals frame.locals mem args =
      .ok (typedArgs, locals1, mem))
    (hCall :
      execCoreCallOpWithMem mem op typedArgs dstTy = .ok (resVal, mem2))
    (hWp : writePlaceV2 body.locals locals1 mem2 dst dstTy resVal =
      .ok (locals2, mem3)) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[
        { frame with
          blockIdx := target, stmtIdx := 0, locals := locals2 }], cm, mem3⟩
      := by
  rw [evalStepV2_term rfl hB hBB hEnd]
  unfold evalTerminatorV2; rw [hTerm]; dsimp only
  rw [ite_bool_false (!dst.projection.isEmpty) (by rw [hNoProj]; rfl)]
  have hCall' : execCoreCallOpWithMemOutcome mem op typedArgs dstTy =
      .ok resVal mem2 := coreOutcome_eq_ok hCall
  rw [hTy]; dsimp only; rw [hArgs]; dsimp only
  rw [hCall']; dsimp only; rw [hWp]; rfl

private theorem evalStepV2_storageDead_indirect {p : Program}
    {frame : FrameState} {mem mem1 : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {lid : LocalId} {mplace : MemPlace}
    {locals1 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.storageDead lid))
    (hNz : Nat.beq lid 0 = false)
    (hGet : Trusted.MirSemantics.getElem? frame.locals lid =
      some (.indirect mplace))
    (hSet : Trusted.MirSemantics.setElem? frame.locals lid .dead =
      some locals1)
    (hDealloc : deallocateStack mem mplace = .ok mem1) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals1 }],
        cm, mem1⟩ := by
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only
  rw [ite_bool_false (Nat.beq lid 0) hNz]
  rw [hGet]; dsimp only; rw [hSet]; dsimp only
  unfold deallocateLocal; dsimp only; rw [hDealloc]

private theorem refValidInMem_box_slice_u8_ok {m : MemoryState}
    {reqMut : Mutability} {aid : AllocId} {a : Allocation}
    {boxPtr : PtrVal} {len : UInt64}
    (hFind : findAllocation aid m.allocations = some a)
    (hLive : a.live = true)
    (hInB : isInBounds a 0 16 = true)
    (hAlign : isAligned a 0 3 = true)
    (hMut : (Mutability.beq reqMut .mut &&
      !Mutability.beq a.mutability .mut) = false)
    (hDec : decodeValV2 profileV2TargetEndian
      (.box (.slice (.int .i8 false))) ((a.bytes.drop 0).take 16) =
      .ok (some (.boxPtr boxPtr (some len))))
    (hBuf : ownedHeapBufValidInMem m (Mutability.beq reqMut .mut)
      (.int .i8 false) boxPtr len len = .ok ()) :
    refValidInMem m reqMut (.box (.slice (.int .i8 false)))
      (.ptr ⟨some aid, UInt64.ofNat 0, .isize⟩) = .ok () := by
  have hZ0 : (UInt64.ofNat 0).toNat = 0 := rfl
  unfold refValidInMem
  rw [layoutOfTyV2_box_slice_u8]; dsimp only
  rw [hFind, hZ0]; dsimp only
  rw [ite_bool_false
    (!a.live || !isInBounds a 0 16 || !isAligned a 0 3)
    (by rw [hLive, hInB, hAlign]; rfl)]
  rw [ite_bool_false
    (Mutability.beq reqMut .mut && !Mutability.beq a.mutability .mut) hMut]
  rw [hDec]
  exact hBuf

private theorem readBoxFromRef_slice_u8_ok {m : MemoryState} {reqMut : Bool}
    {aid : AllocId} {boxPtr : PtrVal} {len : UInt64}
    (hRef : refValidInMem m (if reqMut then .mut else .shared)
      (.box (.slice (.int .i8 false)))
      (.ptr ⟨some aid, UInt64.ofNat 0, .isize⟩) = .ok ())
    (hLoad : loadIndirectV2 m (.box (.slice (.int .i8 false))) ⟨aid, 0⟩ =
      .ok (some (.boxPtr boxPtr (some len))))
    (hBuf : ownedHeapBufValidInMem m reqMut (.int .i8 false) boxPtr len len =
      .ok ()) :
    readBoxFromRef m reqMut (.slice (.int .i8 false))
      ⟨some aid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.slice (.int .i8 false), boxPtr, some len⟩ := by
  have hZ0 : (UInt64.ofNat 0).toNat = 0 := rfl
  unfold readBoxFromRef
  dsimp only
  rw [hRef]; dsimp only; rw [hZ0, hLoad]
  dsimp only [boxValidInMem]
  rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false)) rfl]
  dsimp only [boxPointeeValidInMem]
  rw [hBuf]

private theorem refValidInMem_u8_ok {m : MemoryState}
    {reqMut : Mutability} {aid : AllocId} {off : UInt64} {a : Allocation}
    {decVal : Val}
    (hFind : findAllocation aid m.allocations = some a)
    (hLive : a.live = true)
    (hInB : isInBounds a off.toNat 1 = true)
    (hAlign : isAligned a off.toNat 0 = true)
    (hMut : (Mutability.beq reqMut .mut &&
      !Mutability.beq a.mutability .mut) = false)
    (hDec : decodeValV2 profileV2TargetEndian (.int .i8 false)
      ((a.bytes.drop off.toNat).take 1) = .ok (some decVal)) :
    refValidInMem m reqMut (.int .i8 false)
      (.ptr ⟨some aid, off, .isize⟩) = .ok () := by
  unfold refValidInMem; dsimp only
  rw [ite_bool_false _ ptrGuard_u8]
  rw [layoutOfTyV2_u8]; dsimp only
  rw [hFind]; dsimp only
  rw [ite_bool_false
    (!a.live || !isInBounds a off.toNat 1 || !isAligned a off.toNat 0)
    (by rw [hLive, hInB, hAlign]; rfl)]
  rw [ite_bool_false
    (Mutability.beq reqMut .mut && !Mutability.beq a.mutability .mut) hMut]
  rw [hDec]

private theorem refValidInMem_slice_u8_ok {m : MemoryState}
    {reqMut : Mutability} {aid : AllocId} {off len : UInt64} (a : Allocation)
    (hBound : Nat.blt (len.toNat * 1) isizeMaxBytes = true)
    (hFind : findAllocation aid m.allocations = some a)
    (hLive : a.live = true)
    (hInB : isInBounds a off.toNat (len.toNat * 1) = true)
    (hAlign : isAligned a off.toNat 0 = true)
    (hMut : (Mutability.beq reqMut .mut &&
      !Mutability.beq a.mutability .mut) = false)
    (hInit : isSliceAllInit
      ((a.bytes.drop off.toNat).take (len.toNat * 1)) = true) :
    refValidInMem m reqMut (.slice (.int .i8 false))
      (.slicePtr ⟨some aid, off, .isize⟩ len) = .ok () := by
  unfold refValidInMem; dsimp only [intLayout]
  rw [ite_bool_false _ sliceGuard_u8, layoutOfTyV2_u8]; dsimp only
  rw [sliceFromRawPartsCheck_u8_ok a hBound hFind hLive hInB hAlign hMut hInit]

private theorem evalVecPush_u8_inBounds {m m1 m2 : MemoryState}
    {vecAid bufAid : AllocId} {cap curLen : UInt64} {val : Val}
    {valBytes : List AllocByte}
    (hRead : readVecFromRef m true (.int .i8 false)
      ⟨some vecAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap, curLen⟩)
    (hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) val =
      .ok valBytes)
    (hVal : checkValV2 val (.int .i8 false) = true)
    (hLe1 : Nat.ble curLen.toNat (curLen.toNat + 1) = true)
    (hCap : Nat.ble (curLen.toNat + 1) cap.toNat = true)
    (hWrBuf : writeBytes m ⟨bufAid, curLen.toNat⟩ 0 valBytes = .ok m1)
    (hWrVec : writeVecToRef m1 ⟨some vecAid, UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap,
        UInt64.ofNat (curLen.toNat + 1)⟩ = .ok m2) :
    execCoreCallOpWithMem m .vecPush
      [(.ref .mut (.vec (.int .i8 false)),
          .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩),
       (.int .i8 false, val)]
      .unit = .ok (.unit, m2) := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  refine execCoreCallOpWithMem_eq_allocOutcome ?_
  unfold execAllocCoreCallOutcome evalVecPushOutcome
  try dsimp only
  rw [ite_bool_false (!MirTy.unit.beq .unit ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  try dsimp only
  rw [ite_bool_false (!checkValV2 val (.int .i8 false)) (by rw [hVal]; rfl)]
  rw [hRead, layoutOfTyV2_u8, hEnc]
  dsimp only [ensureVecCapacityOutcome]
  rw [ite_bool_false (!Nat.ble curLen.toNat (curLen.toNat + 1))
    (by rw [hLe1]; rfl)]
  rw [ite_bool_true (Nat.ble (curLen.toNat + 1) cap.toNat) hCap]
  dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [hZ0, Nat.zero_add, Nat.mul_one, hWrBuf]; dsimp only; rw [hWrVec]
  rfl

private theorem evalVecPush_u8_fromEmpty {m m2 m3 : MemoryState}
    {vecAid : AllocId} {ptr0 : PtrVal} {val : Val}
    {valBytes : List AllocByte}
    (hRead : readVecFromRef m true (.int .i8 false)
      ⟨some vecAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ptr0, 0, 0⟩)
    (hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) val =
      .ok valBytes)
    (hVal : checkValV2 val (.int .i8 false) = true)
    (hWrBuf : writeBytes
      ⟨m.nextAllocId + 1, m.allocations ++
        [⟨m.nextAllocId, 0, .mut, List.replicate 8 .uninit, true⟩]⟩
      ⟨m.nextAllocId, 0⟩ 0 valBytes = .ok m2)
    (hWrVec : writeVecToRef m2 ⟨some vecAid, UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, ⟨some m.nextAllocId, 0, .isize⟩, 8, 1⟩ = .ok m3) :
    execCoreCallOpWithMem m .vecPush
      [(.ref .mut (.vec (.int .i8 false)),
          .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩),
       (.int .i8 false, val)]
      .unit = .ok (.unit, m3) := by
  have hGrow : vecGrowCap 1 0 1 = some 8 := rfl
  have hL0 : (UInt64.toNat 0) = 0 := rfl
  have hL1 : UInt64.ofNat (0 + 1) = (1 : UInt64) := rfl
  have hC8 : UInt64.ofNat 8 = (8 : UInt64) := rfl
  refine execCoreCallOpWithMem_eq_allocOutcome ?_
  unfold execAllocCoreCallOutcome evalVecPushOutcome
  try dsimp only
  rw [ite_bool_false (!MirTy.unit.beq .unit ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  try dsimp only
  rw [ite_bool_false (!checkValV2 val (.int .i8 false)) (by rw [hVal]; rfl)]
  rw [hRead, layoutOfTyV2_u8, hEnc]
  dsimp only [ensureVecCapacityOutcome, allocHeapBuffer,
    MemoryState.reserveAllocId]
  rw [hL0]
  rw [ite_bool_false (!Nat.ble 0 (0 + 1)) rfl]
  rw [ite_bool_false (Nat.ble (0 + 1) 0) rfl]
  rw [hGrow]; dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [ite_bool_true (Nat.beq (0 * 1) 0) rfl]
  rw [ite_bool_true (Nat.beq 0 0) rfl]
  dsimp only
  rw [ite_bool_true (Nat.beq (0 * 1) 0) rfl]
  dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [hL0, Nat.zero_mul, Nat.zero_add, hWrBuf]; dsimp only
  rw [hC8, hL1, hWrVec]
  rfl

private theorem truncateBits_isize_toNat_of_lt (x : Nat) (hLt64 : x < 2 ^ 64) :
    (UInt64.ofNat (truncateBits .isize (BitVec.ofNat 128 x)).toNat).toNat =
      x := by
  have hLt128 : x < 2 ^ 128 := Nat.lt_trans hLt64 (by decide)
  have hBW : IntWidth.isize.bitWidth = 64 := rfl
  have hSh : ∀ n : Nat, Nat.shiftRight n 0 = n := fun _ => rfl
  unfold truncateBits bvExtractLsb bvExtractLsb' bvZeroExtend
  rw [hBW]; dsimp only
  change (BitVec.ofNat 64 (BitVec.ofNat 128 (BitVec.ofNat 64
    (Nat.shiftRight (BitVec.ofNat 128 x).toNat 0)).toNat).toNat).toNat = x
  rw [hSh, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hLt128, Nat.mod_eq_of_lt hLt64,
    Nat.mod_eq_of_lt hLt128, Nat.mod_eq_of_lt hLt64]

private theorem evalVecResize_u8_growInBounds {m m1 m2 : MemoryState}
    {vecAid bufAid : AllocId} {cap curLen newLen : UInt64} {val : Val}
    {valBytes : List AllocByte}
    (hRead : readVecFromRef m true (.int .i8 false)
      ⟨some vecAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap, curLen⟩)
    (hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) val =
      .ok valBytes)
    (hVal : checkValV2 val (.int .i8 false) = true)
    (hGrow : Nat.ble newLen.toNat curLen.toNat = false)
    (hLe : Nat.ble curLen.toNat newLen.toNat = true)
    (hCap : Nat.ble newLen.toNat cap.toNat = true)
    (hWrBuf : writeBytes m ⟨bufAid, curLen.toNat⟩ 0
      (repeatBytes (newLen.toNat - curLen.toNat) valBytes) = .ok m1)
    (hWrVec : writeVecToRef m1 ⟨some vecAid, UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap, newLen⟩ = .ok m2) :
    execCoreCallOpWithMem m .vecResize
      [(.ref .mut (.vec (.int .i8 false)),
          .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩),
       (.int .isize false,
          .scalar ⟨.isize, false, truncateBits .isize
            (BitVec.ofNat 128 newLen.toNat)⟩),
       (.int .i8 false, val)]
      .unit = .ok (.unit, m2) := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  have hTrunc : (UInt64.ofNat (truncateBits .isize
      (BitVec.ofNat 128 newLen.toNat)).toNat) = newLen := by
    cases newLen with
    | ofBitVec bv =>
      exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq
        (truncateBits_isize_toNat_of_lt bv.toNat bv.isLt))
  refine execCoreCallOpWithMem_eq_allocOutcome ?_
  unfold execAllocCoreCallOutcome evalVecResizeOutcome
  try dsimp only
  rw [ite_bool_false (!MirTy.unit.beq .unit ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  try dsimp only
  rw [ite_bool_false (!checkValV2 val (.int .i8 false)) (by rw [hVal]; rfl)]
  rw [hRead, layoutOfTyV2_u8, hEnc]; dsimp only
  rw [hTrunc]
  rw [ite_bool_false (Nat.ble newLen.toNat curLen.toNat) hGrow]
  dsimp only [ensureVecCapacityOutcome]
  rw [ite_bool_false (!Nat.ble curLen.toNat newLen.toNat) (by rw [hLe]; rfl)]
  rw [ite_bool_true (Nat.ble newLen.toNat cap.toNat) hCap]
  dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [hZ0, Nat.zero_add, Nat.mul_one, hWrBuf]; dsimp only; rw [hWrVec]
  rfl

private theorem evalVecDeref_shared_u8 {m : MemoryState}
    {reqMut : Mutability} {vecAid bufAid : AllocId} {cap len : UInt64}
    (hRead : readVecFromRef m false (.int .i8 false)
      ⟨some vecAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap, len⟩)
    (hRef : refValidInMem m .shared (.slice (.int .i8 false))
      (.slicePtr ⟨some bufAid, 0, .isize⟩ len) = .ok ()) :
    execCoreCallOpWithMem m .vecDeref
      [(.ref reqMut (.vec (.int .i8 false)),
          .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩)]
      (.ref .shared (.slice (.int .i8 false))) =
      .ok (.slicePtr ⟨some bufAid, 0, .isize⟩ len, m) := by
  refine execCoreCallOpWithMem_eq_allocInfallible rfl ?_
  unfold execAllocCoreCallInfallible evalVecDeref
  try dsimp only
  rw [ite_bool_false (!MirTy.beq (.ref .shared (.slice (.int .i8 false)))
      (.ref .shared (.slice (.int .i8 false)))) rfl]
  dsimp only [Mutability.beq]
  rw [hRead]; dsimp only; rw [hRef]

private theorem evalVecExtendFromSlice_u8_inBounds {m m1 m2 : MemoryState}
    {reqMut : Mutability} {vecAid dstAid srcAid : AllocId}
    {cap curLen srcLen : UInt64} {srcBytes : List AllocByte}
    (hRead : readVecFromRef m true (.int .i8 false)
      ⟨some vecAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some dstAid, 0, .isize⟩, cap, curLen⟩)
    (hSrcValid : heapBufValidInMem m false (.int .i8 false)
      ⟨some srcAid, 0, .isize⟩ srcLen srcLen = .ok ())
    (hBound64 : Nat.blt (curLen.toNat + srcLen.toNat) (Nat.pow 2 64) = true)
    (hSrcNz : Nat.beq (srcLen.toNat * 1) 0 = false)
    (hReadSrc : readBytes m ⟨srcAid, 0⟩ (srcLen.toNat * 1) 0 = .ok srcBytes)
    (hLe : Nat.ble curLen.toNat (curLen.toNat + srcLen.toNat) = true)
    (hCap : Nat.ble (curLen.toNat + srcLen.toNat) cap.toNat = true)
    (hNe : Nat.beq srcAid dstAid = false)
    (hWrBuf : writeBytes m ⟨dstAid, curLen.toNat⟩ 0 srcBytes = .ok m1)
    (hWrVec : writeVecToRef m1 ⟨some vecAid, UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, ⟨some dstAid, 0, .isize⟩, cap,
        UInt64.ofNat (curLen.toNat + srcLen.toNat)⟩ = .ok m2) :
    execCoreCallOpWithMem m .vecExtendFromSlice
      [(.ref .mut (.vec (.int .i8 false)),
          .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩),
       (.ref reqMut (.slice (.int .i8 false)),
          .slicePtr ⟨some srcAid, 0, .isize⟩ srcLen)]
      .unit = .ok (.unit, m2) := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  refine execCoreCallOpWithMem_eq_allocOutcome ?_
  unfold execAllocCoreCallOutcome evalVecExtendFromSliceOutcome
  try dsimp only
  rw [ite_bool_false (!MirTy.unit.beq .unit ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  try dsimp only
  rw [hRead, hSrcValid, layoutOfTyV2_u8]; dsimp only
  rw [ite_bool_false (!Nat.blt (curLen.toNat + srcLen.toNat) (Nat.pow 2 64))
    (by rw [hBound64]; rfl)]
  dsimp only [ensureVecCapacityOutcome]
  rw [ite_bool_false (!Nat.ble curLen.toNat (curLen.toNat + srcLen.toNat))
    (by rw [hLe]; rfl)]
  rw [ite_bool_true (Nat.ble (curLen.toNat + srcLen.toNat) cap.toNat) hCap]
  dsimp only
  rw [ite_bool_false (Nat.beq (srcLen.toNat * 1) 0) hSrcNz]
  rw [hZ0, hReadSrc]; dsimp only
  rw [ite_bool_false (Nat.beq (srcLen.toNat * 1) 0) hSrcNz]
  rw [ite_bool_false (Nat.beq srcAid dstAid && _ && _) (by rw [hNe]; rfl)]
  rw [Nat.mul_one, Nat.zero_add, hWrBuf]; dsimp only; rw [hWrVec]
  rfl

private theorem evalVecLen_u8 {m : MemoryState} {reqMut : Mutability}
    {vecAid : AllocId} {bufPtr : PtrVal} {cap len : UInt64}
    (hRead : readVecFromRef m false (.int .i8 false)
      ⟨some vecAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, bufPtr, cap, len⟩) :
    execCoreCallOpWithMem m .vecLen
      [(.ref reqMut (.vec (.int .i8 false)),
          .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩)]
      (.int .isize false) = .ok (usizeScalarVal len.toNat, m) := by
  refine execCoreCallOpWithMem_eq_allocInfallible rfl ?_
  unfold execAllocCoreCallInfallible evalVecLen
  try dsimp only
  rw [ite_bool_false (!MirTy.beq (.int .isize false) (.int .isize false)) rfl]
  (try dsimp only); rw [hRead]

private theorem evalVecIndex_u8 {m : MemoryState} {inMut reqMut : Mutability}
    {vecAid bufAid : AllocId} {bufAlloc : Allocation}
    {cap len : UInt64} {idx : Nat}
    (hRead : readVecFromRef m (Mutability.beq reqMut .mut) (.int .i8 false)
      ⟨some vecAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap, len⟩)
    (hIdxLt : Nat.blt idx len.toNat = true)
    (hBound : Nat.blt (idx * 1) isizeMaxBytes = true)
    (hFind : findAllocation bufAid m.allocations = some bufAlloc)
    (hLive : bufAlloc.live = true)
    (hBle : Nat.ble (0 + idx * 1) bufAlloc.bytes.length = true)
    (hRef : refValidInMem m reqMut (.int .i8 false)
      (.ptr ⟨some bufAid, UInt64.ofNat (0 + idx * 1), .isize⟩) = .ok ()) :
    (match reqMut with
     | .shared => execCoreCallOpWithMem m .vecIndex
         [(.ref inMut (.vec (.int .i8 false)),
             .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩),
          (.int .isize false, usizeScalarVal idx)]
         (.ref .shared (.int .i8 false))
     | .mut => execCoreCallOpWithMem m .vecIndexMut
         [(.ref .mut (.vec (.int .i8 false)),
             .ptr ⟨some vecAid, UInt64.ofNat 0, .isize⟩),
          (.int .isize false, usizeScalarVal idx)]
         (.ref .mut (.int .i8 false))) =
      .ok (.ptr ⟨some bufAid, UInt64.ofNat (0 + idx * 1), .isize⟩, m) := by
  have hTrunc : (UInt64.ofNat (truncateBits .isize
      (BitVec.ofNat 128 idx)).toNat).toNat = idx := by
    have hLtIsize : idx < isizeMaxBytes :=
      Nat.lt_of_le_of_lt (Nat.le_of_eq (Nat.mul_one idx).symm)
        (Nat.le_of_ble_eq_true hBound)
    have hLt64 : idx < 2 ^ 64 := Nat.lt_trans hLtIsize (by decide)
    exact truncateBits_isize_toNat_of_lt idx hLt64
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  cases reqMut with
  | shared =>
    dsimp only [Mutability.beq] at hRead
    refine execCoreCallOpWithMem_eq_allocOutcome ?_
    unfold execAllocCoreCallOutcome evalVecIndexOutcome usizeScalarVal
    try dsimp only [Mutability.beq]
    rw [ite_bool_false (!MirTy.beq (.ref .shared (.int .i8 false))
        (.ref .shared (.int .i8 false))) rfl]
    (try dsimp only); rw [hRead, layoutOfTyV2_u8]; dsimp only
    rw [hTrunc]
    rw [ite_bool_false (!Nat.blt idx len.toNat) (by rw [hIdxLt]; rfl)]
    dsimp only [ptrAdvanceElem]
    rw [ite_bool_false (Nat.beq 1 0) rfl]
    unfold ptrAddInMem; dsimp only
    rw [ite_bool_false (!Nat.blt (idx * 1) isizeMaxBytes)
      (by rw [hBound]; rfl)]
    rw [hFind]; dsimp only; rw [hZ0]
    rw [ite_bool_false (!bufAlloc.live ||
        !Nat.ble (0 + idx * 1) bufAlloc.bytes.length)
      (by rw [hLive, hBle]; rfl)]
    dsimp only; rw [hRef]
  | _ =>
    dsimp only [Mutability.beq] at hRead
    refine execCoreCallOpWithMem_eq_allocOutcome ?_
    unfold execAllocCoreCallOutcome evalVecIndexOutcome usizeScalarVal
    try dsimp only [Mutability.beq]
    rw [ite_bool_false (!MirTy.beq (.ref .mut (.int .i8 false))
        (.ref .mut (.int .i8 false))) rfl]
    (try dsimp only); rw [hRead, layoutOfTyV2_u8]; dsimp only
    rw [hTrunc]
    rw [ite_bool_false (!Nat.blt idx len.toNat) (by rw [hIdxLt]; rfl)]
    dsimp only [ptrAdvanceElem]
    rw [ite_bool_false (Nat.beq 1 0) rfl]
    unfold ptrAddInMem; dsimp only
    rw [ite_bool_false (!Nat.blt (idx * 1) isizeMaxBytes)
      (by rw [hBound]; rfl)]
    rw [hFind]; dsimp only; rw [hZ0]
    rw [ite_bool_false (!bufAlloc.live ||
        !Nat.ble (0 + idx * 1) bufAlloc.bytes.length)
      (by rw [hLive, hBle]; rfl)]
    dsimp only; rw [hRef]

private theorem evalBoxFromVec_u8_realloc {m m1 m3 : MemoryState}
    {aid : AllocId} {cap len : UInt64} {bytes : List AllocByte}
    (hBuf : ownedHeapBufValidInMem m true (.int .i8 false)
      ⟨some aid, 0, .isize⟩ cap len = .ok ())
    (hNe : Nat.beq cap.toNat len.toNat = false)
    (hNz : Nat.beq (len.toNat * 1) 0 = false)
    (hRead : readBytes m ⟨aid, 0⟩ (len.toNat * 1) 0 = .ok bytes)
    (hRetire : deallocateStack m ⟨aid, 0⟩ = .ok m1)
    (hWr : writeBytes
      ⟨m1.nextAllocId + 1, m1.allocations ++
        [⟨m1.nextAllocId, 0, .mut,
          List.replicate (len.toNat * 1) .uninit, true⟩]⟩
      ⟨m1.nextAllocId, 0⟩ 0 bytes = .ok m3) :
    execCoreCallOpWithMem m .boxFromVec
      [(.vec (.int .i8 false), .vec ⟨some aid, 0, .isize⟩ cap len)]
      (.box (.slice (.int .i8 false))) =
      .ok (.boxPtr ⟨some m1.nextAllocId, 0, .isize⟩ (some len), m3) := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  refine execCoreCallOpWithMem_eq_allocInfallible rfl ?_
  unfold execAllocCoreCallInfallible evalBoxFromVec vecValidInMem
  try dsimp only
  rw [ite_bool_false (!MirTy.beq (.box (.slice (.int .i8 false)))
      (.box (.slice (.int .i8 false)))) rfl]
  try dsimp only
  rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false)) rfl]
  rw [hBuf, layoutOfTyV2_u8]; dsimp only
  rw [ite_bool_false (Nat.beq 1 0 || Nat.beq cap.toNat len.toNat)
    (by rw [hNe]; rfl)]
  rw [ite_bool_false (Nat.beq (len.toNat * 1) 0) hNz]
  rw [hZ0, hRead]; dsimp only [retireHeapBuffer]; rw [hZ0, hRetire]
  dsimp only
  rw [ite_bool_false (Nat.beq (len.toNat * 1) 0) hNz]
  dsimp only [allocHeapBuffer, MemoryState.reserveAllocId]
  rw [hWr]

private theorem evalBoxClone_slice_u8 {m m2 : MemoryState} {reqMut : Mutability}
    {boxAid bufAid : AllocId} {len : UInt64} {copied : List AllocByte}
    (hReadBox : readBoxFromRef m false (.slice (.int .i8 false))
      ⟨some boxAid, UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.slice (.int .i8 false), ⟨some bufAid, 0, .isize⟩, some len⟩)
    (hNz : Nat.beq (len.toNat * 1) 0 = false)
    (hRead : readBytes m ⟨bufAid, 0⟩ (len.toNat * 1) 0 = .ok copied)
    (hWr : writeBytes
      ⟨m.nextAllocId + 1, m.allocations ++
        [⟨m.nextAllocId, 0, .mut,
          List.replicate (len.toNat * 1) .uninit, true⟩]⟩
      ⟨m.nextAllocId, 0⟩ 0 copied = .ok m2) :
    execCoreCallOpWithMem m .boxClone
      [(.ref reqMut (.box (.slice (.int .i8 false))),
          .ptr ⟨some boxAid, UInt64.ofNat 0, .isize⟩)]
      (.box (.slice (.int .i8 false))) =
      .ok (.boxPtr ⟨some m.nextAllocId, 0, .isize⟩ (some len), m2) := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  refine execCoreCallOpWithMem_eq_allocInfallible rfl ?_
  unfold execAllocCoreCallInfallible evalBoxClone
  try dsimp only
  rw [ite_bool_false (!MirTy.beq (.box (.slice (.int .i8 false)))
      (.box (.slice (.int .i8 false)))) rfl]
  try dsimp only
  rw [hReadBox]; dsimp only; rw [layoutOfTyV2_u8]; dsimp only
  rw [ite_bool_false (Nat.beq (len.toNat * 1) 0) hNz]
  rw [hZ0, hRead]
  dsimp only [allocHeapBuffer, MemoryState.reserveAllocId]
  rw [hWr]

private theorem evalBoxNew_u64 {m m2 : MemoryState} {val : Val}
    {valBytes : List AllocByte}
    (hVal : checkValV2 val (.int .i64 false) = true)
    (hEnc : encodeValV2 profileV2TargetEndian (.int .i64 false) val =
      .ok valBytes)
    (hWr : writeBytes
      ⟨m.nextAllocId + 1, m.allocations ++
        [⟨m.nextAllocId, 3, .mut, List.replicate 8 .uninit, true⟩]⟩
      ⟨m.nextAllocId, 0⟩ 3 valBytes = .ok m2) :
    execCoreCallOpWithMem m (.boxNew (.int .i64 false))
      [(.int .i64 false, val)] (.box (.int .i64 false)) =
      .ok (.boxPtr ⟨some m.nextAllocId, 0, .isize⟩ none, m2) := by
  refine execCoreCallOpWithMem_eq_allocInfallible rfl ?_
  unfold execAllocCoreCallInfallible evalBoxNew
  try dsimp only
  rw [ite_bool_false (!MirTy.beq (.int .i64 false) (.int .i64 false) ||
      !MirTy.beq (.box (.int .i64 false)) (.box (.int .i64 false))) rfl]
  try dsimp only
  rw [ite_bool_false
    (isUnsizedTy (.int .i64 false) ||
      !isSupportedPointeeTy (.int .i64 false) ||
      !checkValV2 val (.int .i64 false))
    (by rw [hVal]; rfl)]
  rw [layoutOfTyV2_u64, hEnc]; dsimp only
  rw [ite_bool_false (Nat.beq 8 0) rfl]
  dsimp only [allocHeapBuffer, MemoryState.reserveAllocId]
  rw [hWr]

private theorem evalStepV2_assign_copy_deref {p : Program} {frame : FrameState}
    {mem : MemoryState} {cm : CallerMemory} {body : Body} {bb : BasicBlock}
    {dst ptrLid : LocalId} {ptrTy valTy : MirTy} {pv : PtrVal}
    {aid : AllocId} {lay : LayoutData} {resVal : Val}
    {locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.use (.copy ⟨ptrLid, [.deref]⟩))))
    (hDstTy : placeStaticTyV2 body.locals ⟨dst, []⟩ = some valTy)
    (hPtrTy : Trusted.MirSemantics.getElem? body.locals ptrLid = some ptrTy)
    (hPtrMatch :
      (ptrTy = .ref .shared valTy) ∨ (ptrTy = .rawPtr .shared valTy))
    (hUnsized : isUnsizedTy valTy = false)
    (hLay : layoutOfTyV2 valTy = some lay)
    (hSlot : Trusted.MirSemantics.getElem? frame.locals ptrLid =
      some (.immediate (some (.ptr pv))))
    (hAid : pv.allocId = some aid)
    (hLoad : loadIndirectV2 mem valTy ⟨aid, pv.offsetBytes.toNat⟩ =
      .ok (some resVal))
    (hWp : writePlaceV2 body.locals frame.locals mem ⟨dst, []⟩ valTy resVal =
      .ok (locals2, mem))
    (hHaz : checkAssignCopyHazardV2 body.locals frame.locals mem (.local dst)
      valTy (.use (.copy ⟨ptrLid, [.deref]⟩)) = .ok () := by rfl) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hDstTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalOperandToSlotV2 readPlaceV2; dsimp only
  rw [hPtrTy, hSlot]; dsimp only
  cases hPtrMatch with
  | inl hEq =>
    rw [hEq]; dsimp only
    rw [ite_bool_false (isUnsizedTy valTy) hUnsized]
    rw [hLay]; dsimp only
    rw [ite_bool_false false rfl, ite_bool_false (![].isEmpty) rfl]
    rw [hAid]; dsimp only
    rw [hLoad]; dsimp only
    rw [ite_bool_false (!valTy.beq valTy) (by rw [MirTy.beq_iff.mpr rfl]; rfl)]
    dsimp only; rw [hWp]; rw [hHaz]
  | inr hEq =>
    rw [hEq]; dsimp only
    rw [ite_bool_false (isUnsizedTy valTy) hUnsized]
    rw [hLay]; dsimp only
    rw [ite_bool_false false rfl, ite_bool_false (![].isEmpty) rfl]
    rw [hAid]; dsimp only
    rw [hLoad]; dsimp only
    rw [ite_bool_false (!valTy.beq valTy) (by rw [MirTy.beq_iff.mpr rfl]; rfl)]
    dsimp only; rw [hWp]; rw [hHaz]

private theorem evalStepV2_assign_deref_write_u8 {p : Program}
    {frame : FrameState} {mem mem1 : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {ptrLid : LocalId} {pv : PtrVal}
    {aid : AllocId} {a : Allocation} {val : Val}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨ptrLid, [.deref]⟩ (.use (.constant ⟨.int .i8 false,
        .scalar (BitVec.ofNat 128 42)⟩))))
    (hPtrTy : Trusted.MirSemantics.getElem? body.locals ptrLid =
      some (.ref .mut (.int .i8 false)))
    (hSlot : Trusted.MirSemantics.getElem? frame.locals ptrLid =
      some (.immediate (some (.ptr pv))))
    (hAid : pv.allocId = some aid)
    (hFind : findAllocation aid mem.allocations = some a)
    (hLive : a.live = true)
    (hMut : a.mutability = .mut)
    (hEval : evalConstLit (.int .i8 false) (.scalar (BitVec.ofNat 128 42)) =
      .ok val)
    (hStore : storeIndirectV2 mem (.int .i8 false)
      ⟨aid, pv.offsetBytes.toNat⟩ val = .ok mem1) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1 }], cm, mem1⟩ := by
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only
  unfold placeStaticTyV2; rw [hPtrTy]; dsimp only
  rw [ite_bool_false (isUnsizedTy (.int .i8 false)) rfl]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  rw [hPtrTy, hSlot]; dsimp only
  rw [ite_bool_false (isUnsizedTy (.int .i8 false) ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  rw [ite_bool_false (!Mutability.beq .mut .mut) rfl]
  rw [layoutOfTyV2_u8]; dsimp only
  unfold evalRvalueV2 evalOperandToSlotV2; dsimp only; rw [hEval]; dsimp only
  rw [ite_bool_false (!MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  dsimp only
  unfold writePlaceDestV2; dsimp only
  have hVal : checkValV2 val (.int .i8 false) = true := by
    have hV : val = .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 42)⟩
        := by
      cases hEval; rfl
    rw [hV]; rfl
  rw [ite_bool_false (!checkValV2 val (.int .i8 false))
    (by rw [hVal]; rfl)]
  rw [hAid]; dsimp only; rw [hFind]
  dsimp only
  rw [ite_bool_false
    (Nat.blt 0 1 && (!a.live || !Mutability.beq a.mutability .mut))
    (by rw [hLive, hMut]; rfl)]
  rw [hStore]; rfl

private theorem checkAssignCopyHazardV2_copy_deref_imm {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {dst ptrLid : LocalId}
    {valTy : MirTy} {pv : PtrVal} {aid : AllocId} {lay : LayoutData}
    {v : Option Val}
    (hDst : Trusted.MirSemantics.getElem? locals dst = some (.immediate v))
    (hPtrTy : Trusted.MirSemantics.getElem? bodyLocals ptrLid =
      some (.ref .shared valTy))
    (hSlot : Trusted.MirSemantics.getElem? locals ptrLid =
      some (.immediate (some (.ptr pv))))
    (hAid : pv.allocId = some aid)
    (hLay : layoutOfTyV2 valTy = some lay) :
    checkAssignCopyHazardV2 bodyLocals locals mem (.local dst) valTy
      (.use (.copy ⟨ptrLid, [.deref]⟩)) = .ok () := by
  unfold checkAssignCopyHazardV2 destCopySpanV2 srcPlaceCopySpanV2
  dsimp only
  rw [hDst, hPtrTy, hSlot]; dsimp only
  rw [hAid]; dsimp only
  rw [hLay]
  cases isMemoryCopyReprTyV2 valTy <;> rfl

private theorem evalStepV2_assign_move_indirect {p : Program}
    {frame : FrameState} {mem mem1 : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {dst src : LocalId} {ty : MirTy}
    {mplace : MemPlace} {val : Val} {locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.use (.move ⟨src, []⟩))))
    (hDstTy : placeStaticTyV2 body.locals ⟨dst, []⟩ = some ty)
    (hSrcTy : Trusted.MirSemantics.getElem? body.locals src = some ty)
    (hSupp : isSupportedV2LocalTy ty = true)
    (hSlot : Trusted.MirSemantics.getElem? frame.locals src =
      some (.indirect mplace))
    (hLoad : loadIndirectV2 mem ty mplace = .ok (some val))
    (hDeinit : deinitIndirectV2 mem ty mplace = .ok mem1)
    (hWp : writePlaceV2 body.locals frame.locals mem1 ⟨dst, []⟩ ty val =
      .ok (locals2, mem1))
    (hHaz : checkAssignCopyHazardV2 body.locals frame.locals mem (.local dst)
      ty (.use (.move ⟨src, []⟩)) = .ok () := by rfl) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem1⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hDstTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalOperandToSlotV2 readPlaceV2; dsimp only
  rw [hSrcTy, hSlot]; dsimp only
  rw [ite_bool_false (!isSupportedV2LocalTy ty) (by rw [hSupp]; rfl)]
  rw [hLoad]; dsimp only; rw [hDeinit]
  rw [ite_bool_true true rfl]; dsimp only
  rw [ite_bool_false (!ty.beq ty) (by rw [MirTy.beq_iff.mpr rfl]; rfl)]
  dsimp only; rw [hWp]; rw [hHaz]

private theorem evalStepV2_assign_useRetag_indirect {p : Program}
    {frame : FrameState} {mem mem1 : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {dst src : LocalId} {ty : MirTy}
    {mplace : MemPlace} {val : Val} {locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.useRetag (.move ⟨src, []⟩))))
    (hDstTy : placeStaticTyV2 body.locals ⟨dst, []⟩ = some ty)
    (hSrcTy : Trusted.MirSemantics.getElem? body.locals src = some ty)
    (hSupp : isSupportedV2LocalTy ty = true)
    (hSlot : Trusted.MirSemantics.getElem? frame.locals src =
      some (.indirect mplace))
    (hLoad : loadIndirectV2 mem ty mplace = .ok (some val))
    (hDeinit : deinitIndirectV2 mem ty mplace = .ok mem1)
    (hRefs : refsValidInMem mem1 ty val = true)
    (hWp : writePlaceV2 body.locals frame.locals mem1 ⟨dst, []⟩ ty val =
      .ok (locals2, mem1))
    (hHaz : checkAssignCopyHazardV2 body.locals frame.locals mem (.local dst)
      ty (.useRetag (.move ⟨src, []⟩)) = .ok () := by rfl) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem1⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hDstTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalOperandToSlotV2 readPlaceV2; dsimp only
  rw [hSrcTy, hSlot]; dsimp only
  rw [ite_bool_false (!isSupportedV2LocalTy ty) (by rw [hSupp]; rfl)]
  rw [hLoad]; dsimp only; rw [hDeinit]
  rw [ite_bool_true true rfl]; dsimp only
  rw [ite_bool_false (!ty.beq ty) (by rw [MirTy.beq_iff.mpr rfl]; rfl)]
  rw [ite_bool_false (!refsValidInMem mem1 ty val) (by rw [hRefs]; rfl)]
  dsimp only; rw [hWp]; rw [hHaz]

private theorem evalStepV2_assign_useRetag_imm {p : Program}
    {frame : FrameState} {mem : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {dst src : LocalId} {ty : MirTy}
    {val : Val} {locals1 locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.useRetag (.move ⟨src, []⟩))))
    (hDstTy : placeStaticTyV2 body.locals ⟨dst, []⟩ = some ty)
    (hSrcTy : Trusted.MirSemantics.getElem? body.locals src = some ty)
    (hSupp : isSupportedV2LocalTy ty = true)
    (hSlot : Trusted.MirSemantics.getElem? frame.locals src =
      some (.immediate (some val)))
    (hClr : Trusted.MirSemantics.setElem? frame.locals src
      (liveUninitSlot ty) = some locals1)
    (hRefs : refsValidInMem mem ty val = true)
    (hWp : writePlaceV2 body.locals locals1 mem ⟨dst, []⟩ ty val =
      .ok (locals2, mem))
    (hHaz : checkAssignCopyHazardV2 body.locals frame.locals mem (.local dst)
      ty (.useRetag (.move ⟨src, []⟩)) = .ok () := by rfl) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hDstTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalOperandToSlotV2 readPlaceV2; dsimp only
  rw [hSrcTy, hSlot]; dsimp only
  rw [ite_bool_false (!isSupportedV2LocalTy ty) (by rw [hSupp]; rfl)]
  rw [hClr]
  rw [ite_bool_true true rfl]; dsimp only
  rw [ite_bool_false (!ty.beq ty) (by rw [MirTy.beq_iff.mpr rfl]; rfl)]
  rw [ite_bool_false (!refsValidInMem mem ty val) (by rw [hRefs]; rfl)]
  dsimp only; rw [hWp]; rw [hHaz]

private theorem evalStepV2_return_imm {p : Program} {frame : FrameState}
    {mem : MemoryState} {cm : CallerMemory} {body : Body} {bb : BasicBlock}
    {retTy : MirTy} {retVal : Val}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hEnd : frame.stmtIdx = bb.statements.length)
    (hTerm : bb.terminator = .return_)
    (hNoClean : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? frame.locals 0 =
      some (.immediate (some retVal)))
    (hStay : refsStayInCallerMem cm retTy retVal = true)
    (hRefs : refsValidInMem mem retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true)
    (hNoRodata : hasEscapingRodataPtr cm mem retTy retVal = false := by rfl) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .done (.returned
        ⟨retVal, extractReturnMemoryV2 cm mem frame.locals⟩) := by
  rw [evalStepV2_term rfl hB hBB hEnd]
  unfold evalTerminatorV2; rw [hTerm]; dsimp only
  rw [ite_bool_false bb.cleanup hNoClean]
  rw [hRetTy, hRetSlot]; dsimp only
  rw [ite_bool_false _ hNoRodata]
  rw [ite_bool_false (!refsStayInCallerMem cm retTy retVal ||
      !refsValidInMem mem retTy retVal ||
      !spansPairwiseDisjoint (refAccessSpans retTy retVal))
    (by rw [hStay, hRefs, hDisj]; rfl)]



private theorem promoteLocalToMemory_indirect_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {src : LocalId}
    {localTy : MirTy} {aid off : Nat}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals src = some localTy)
    (hSlot : Trusted.MirSemantics.getElem? locals src =
      some (.indirect ⟨aid, off⟩))
    (hUnsized : isUnsizedTy localTy = false) :
    promoteLocalToMemory bodyLocals locals mem src =
      .ok (localTy, ⟨aid, off⟩, locals, mem) := by
  unfold promoteLocalToMemory; rw [hTy, hSlot]; dsimp only
  rw [ite_bool_false (isUnsizedTy localTy) hUnsized]

private theorem evalStepV2_assign_reborrow_slice_u8 {p : Program}
    {frame : FrameState} {mem : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {dst src : LocalId}
    {pv : PtrVal} {len : UInt64} {locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.ref .shared ⟨src, [.deref]⟩)))
    (hDstTy : placeStaticTyV2 body.locals ⟨dst, []⟩ =
      some (.ref .shared (.slice (.int .i8 false))))
    (hSrcTy : Trusted.MirSemantics.getElem? body.locals src =
      some (.ref .shared (.slice (.int .i8 false))))
    (hSlot : Trusted.MirSemantics.getElem? frame.locals src =
      some (.immediate (some (.slicePtr pv len))))
    (hRef : refValidInMem mem .shared (.slice (.int .i8 false))
      (.slicePtr pv len) = .ok ())
    (hWp : writePlaceV2 body.locals frame.locals mem ⟨dst, []⟩
      (.ref .shared (.slice (.int .i8 false))) (.slicePtr pv len) =
      .ok (locals2, mem)) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hDstTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalRefRvalueV2; dsimp only
  rw [hSrcTy, hSlot]; dsimp only
  rw [ite_bool_false (Mutability.beq .shared .shared &&
      Mutability.beq .shared .mut) rfl]
  rw [ite_bool_false (!MirTy.beq (.ref .shared (.slice (.int .i8 false)))
      (.ref .shared (.slice (.int .i8 false)))) rfl]
  rw [hRef]; dsimp only; rw [hWp]; rfl

private theorem initStateV2_ok_of {p : Program} {body : Body} {q : Query}
    (hEntry : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hStatic : BodyStaticAdmittedV2 p body = true)
    (hValid : ValidEntryArgsV2 body q)
    (hNoRaw : tyListHasRawPtrV2
      ((body.locals.drop 1).take body.argumentCount) = false := by rfl) :
    initStateV2 p q =
      .ok ⟨[⟨p.entryDefId, 0, 0, initLocalsLoop body q.args 0 body.locals, none, none, none⟩],
        q.callerMem, entryMemoryWithCaller q.callerMem⟩ := by
  have hStatic' := hStatic
  unfold BodyStaticAdmittedV2 at hStatic'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hStatic'
  rcases hStatic' with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPW, hMV⟩, _⟩, hEmpty⟩, hArgLt⟩, hStB⟩, hDisc⟩, hCast⟩, hAssert⟩,
      _⟩, _⟩, hLocs⟩
  rcases hValid with ⟨hCM, hArgs, hRefs, hSpans⟩
  unfold initStateV2
  rw [ite_bool_false (!Nat.beq p.pointerWidthBits 64 ||
      !Nat.beq p.mirProfileVersion 2) (by rw [hPW, hMV]; rfl)]
  rw [ite_bool_false (!validCallerMemory q.callerMem) (by rw [hCM]; rfl)]
  rw [hEntry]; dsimp only
  rw [ite_bool_false body.basicBlocks.isEmpty hEmpty]
  rw [ite_bool_false (!Nat.blt body.argumentCount body.locals.length)
    (by rw [hArgLt]; rfl)]
  rw [ite_bool_false (!storageAnnotationsInBounds body) (by rw [hStB]; rfl)]
  rw [ite_bool_false (!discriminantTypesValidV2 body) (by rw [hDisc]; rfl)]
  rw [ite_bool_false (!castTypesValid body) (by rw [hCast]; rfl)]
  rw [ite_bool_false (!assertConditionTypesValid body) (by rw [hAssert]; rfl)]
  rw [ite_bool_false (!body.locals.all isSupportedV2LocalTy)
    (by rw [hLocs]; rfl)]
  rw [ite_bool_false (!checkArgsMatchV2 q.args
      ((body.locals.drop 1).take body.argumentCount))
    (by rw [hArgs]; rfl)]
  have hMem : entryMemoryForArgsV2 q.callerMem
      ((body.locals.drop 1).take body.argumentCount) q.args =
      entryMemoryWithCaller q.callerMem := by
    unfold entryMemoryForArgsV2; rw [hNoRaw]; rfl
  rw [hMem]
  rw [ite_bool_false (!refsValidInMemList (entryMemoryWithCaller q.callerMem)
      ((body.locals.drop 1).take body.argumentCount) q.args ||
      !spansPairwiseDisjoint (refAccessSpansList
        ((body.locals.drop 1).take body.argumentCount) q.args))
    (by rw [hRefs, hSpans]; rfl)]

private theorem isInBounds_zero_append {n : Nat} {bs : List AllocByte}
    (id align : Nat) (mty : Mutability) (live : Bool)
    (hLen : n ≤ bs.length) :
    isInBounds ⟨id, align, mty, bs, live⟩ 0 n = true := by
  unfold isInBounds
  rw [Nat.zero_add]
  exact Nat.ble_eq.mpr hLen

private theorem isInBounds_zero_replicate (id align : Nat) (mty : Mutability)
    (live : Bool) (n : Nat) :
    isInBounds ⟨id, align, mty, List.replicate n .uninit, live⟩ 0 n = true :=
  isInBounds_zero_append id align mty live
    (by rw [List.length_replicate]; exact Nat.le_refl n)

private theorem isAligned_zero (a : Allocation) :
    isAligned a 0 0 = true := rfl

private theorem isAligned_align0 (a : Allocation) (off : Nat)
    (h : Nat.ble 0 a.alignLog2 = true) :
    isAligned a off 0 = true := by
  unfold isAligned
  rw [h, Bool.true_and]
  change Nat.beq (off % 1) 0 = true
  rw [Nat.mod_one]; rfl

private theorem decodeValV2_u64_1234 :
    decodeValV2 profileV2TargetEndian (.int .i64 false)
      [.init 52 none, .init 18 none, .init 0 none, .init 0 none,
       .init 0 none, .init 0 none, .init 0 none, .init 0 none] =
      .ok (some (.scalar ⟨.i64, false,
        truncateBits .i64 (BitVec.ofNat 128 0x1234)⟩)) := rfl

private theorem refsValidInMemList_nil (m : MemoryState) :
    refsValidInMemList m [] [] = true := rfl

private theorem refsValidInMemList_cons (m : MemoryState) (t : MirTy)
    (ts : List MirTy) (v : Val) (vs : List Val)
    (h1 : refsValidInMem m t v = true)
    (h2 : refsValidInMemList m ts vs = true) :
    refsValidInMemList m (t :: ts) (v :: vs) = true := by
  unfold refsValidInMemList; rw [h1, h2]; rfl

private theorem refsValidInMem_vec_true {m : MemoryState} {elem : MirTy}
    {ptr : PtrVal} {cap len : UInt64}
    (h : ownedHeapBufValidInMem m true elem ptr cap len = .ok ()) :
    refsValidInMem m (.vec elem) (.vec ptr cap len) = true := by
  unfold refsValidInMem; rw [h]

private theorem refsValidInMem_box_slice_true {m : MemoryState} {elem : MirTy}
    {ptr : PtrVal} {len : UInt64}
    (h : ownedHeapBufValidInMem m true elem ptr len len = .ok ()) :
    refsValidInMem m (.box (.slice elem)) (.boxPtr ptr (some len)) = true := by
  unfold refsValidInMem boxPointeeValidInMem; dsimp only; rw [h]

private theorem refsValidInMem_box_u64_true {m : MemoryState} {ptr : PtrVal}
    (h : ownedHeapBufValidInMem m true (.int .i64 false) ptr 1 1 = .ok ()) :
    refsValidInMem m (.box (.int .i64 false)) (.boxPtr ptr none) = true := by
  unfold refsValidInMem boxPointeeValidInMem; dsimp only
  rw [ite_bool_false (isUnsizedTy (.int .i64 false)) rfl, h]


private theorem heap_of_owned {m : MemoryState} {isMut : Bool}
    {elem : MirTy} {p : PtrVal} {cap len : UInt64}
    (h : ownedHeapBufValidInMem m isMut elem p cap len = .ok ()) :
    heapBufValidInMem m isMut elem p cap len = .ok () := by
  unfold ownedHeapBufValidInMem at h
  cases hH : heapBufValidInMem m isMut elem p cap len with
  | error k => rw [hH] at h; cases h
  | ok u => rfl

private noncomputable def mBuf0_init (nid : Nat) : Allocation :=
  ⟨nid + 0, 0, .mut,
    [.uninit], true⟩

private noncomputable def mBuf0_1 (nid : Nat) : Allocation :=
  ⟨nid + 0, 0, .mut,
    [.init 9 none], true⟩

private noncomputable def mVec1_0 (nid : Nat) : Allocation :=
  ⟨nid + 1, 3, .mut,
    [.init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 1 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none], true⟩

private noncomputable def mVec1_1 (nid : Nat) : Allocation :=
  ⟨nid + 1, 3, .mut,
    [.init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 0 (some (nid + 0))
    , .init 1 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 1 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none], true⟩

private noncomputable def mVec1_uninit (nid : Nat) : Allocation :=
  ⟨nid + 1, 3, .mut,
    [.uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], true⟩

private noncomputable def mVec1_dead (nid : Nat) : Allocation :=
  ⟨nid + 1, 3, .mut,
    [.uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], false⟩

private noncomputable def mVec2_0 (nid : Nat) : Allocation :=
  ⟨nid + 2, 3, .mut,
    [.init 1 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none], true⟩

private noncomputable def mVec2_1 (nid : Nat) : Allocation :=
  ⟨nid + 2, 3, .mut,
    [.init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 8 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 1 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none], true⟩

private noncomputable def mVec2_2 (nid : Nat) : Allocation :=
  ⟨nid + 2, 3, .mut,
    [.init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 0 (some (nid + 3))
    , .init 8 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 2 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none], true⟩

private noncomputable def mVec2_uninit (nid : Nat) : Allocation :=
  ⟨nid + 2, 3, .mut,
    [.uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], true⟩

private noncomputable def mVec2_dead (nid : Nat) : Allocation :=
  ⟨nid + 2, 3, .mut,
    [.uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], false⟩

private noncomputable def mBuf3_1 (nid : Nat) : Allocation :=
  ⟨nid + 3, 0, .mut,
    [.init 10 none
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], true⟩

private noncomputable def mBuf3_2 (nid : Nat) : Allocation :=
  ⟨nid + 3, 0, .mut,
    [.init 10 none
    , .init 9 none
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], true⟩

private noncomputable def mBuf3_dead (nid : Nat) : Allocation :=
  ⟨nid + 3, 0, .mut,
    [.init 10 none
    , .init 9 none
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], false⟩

private noncomputable def mBuf4 (nid : Nat) : Allocation :=
  ⟨nid + 4, 0, .mut,
    [.init 10 none
    , .init 9 none], true⟩

private noncomputable def mBox5_0 (nid : Nat) : Allocation :=
  ⟨nid + 5, 3, .mut,
    [.init 0 (some (nid + 4))
    , .init 0 (some (nid + 4))
    , .init 0 (some (nid + 4))
    , .init 0 (some (nid + 4))
    , .init 0 (some (nid + 4))
    , .init 0 (some (nid + 4))
    , .init 0 (some (nid + 4))
    , .init 0 (some (nid + 4))
    , .init 2 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none], true⟩

private noncomputable def mBox5_uninit (nid : Nat) : Allocation :=
  ⟨nid + 5, 3, .mut,
    [.uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], true⟩

private noncomputable def mBox5_dead (nid : Nat) : Allocation :=
  ⟨nid + 5, 3, .mut,
    [.uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit
    , .uninit], false⟩

private noncomputable def mClone6 (nid : Nat) : Allocation :=
  ⟨nid + 6, 0, .mut,
    [.init 10 none
    , .init 9 none], true⟩

private noncomputable def mBox64 (nid : Nat) : Allocation :=
  ⟨nid + 0, 3, .mut,
    [.init 52 none
    , .init 18 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none
    , .init 0 none], true⟩

private noncomputable def m_b0_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 0, 0,
    [.immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate none], none, none, none⟩],
    cm, ⟨nid + 0, cm.allocations⟩⟩

private noncomputable def m_b0_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 0, 2,
    [.immediate none
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 0, cm.allocations⟩⟩

private noncomputable def m_b1_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 1, 0,
    [.immediate none
    , .immediate (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBuf0_init nid]⟩⟩

private noncomputable def m_b1_2 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 1, 2,
    [.immediate none
    , .immediate (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0))
    , .immediate (some .unit)
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBuf0_init nid]⟩⟩

private noncomputable def m_b1_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 1, 3,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 2, cm.allocations ++ [mBuf0_init nid, mVec1_0 nid]⟩⟩

private noncomputable def m_b2_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 2, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .immediate (some (.unit))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid]⟩⟩

private noncomputable def m_b2_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 2, 3,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid]⟩⟩

private noncomputable def m_b3_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 3, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .immediate (some (.vec ⟨none, 1, .isize⟩ 0 0))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid]⟩⟩

private noncomputable def m_b3_3 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 3, 3,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .immediate (some (.vec ⟨none, 1, .isize⟩ 0 0))
    , .immediate (some .unit)
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid]⟩⟩

private noncomputable def m_b3_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 3, 4,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 3, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid]⟩⟩

private noncomputable def m_b4_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 4, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .immediate (some (.unit))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b4_4 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 4, 4,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some .unit)
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b4_5 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 4, 5,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b4_8 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 4, 8,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .immediate none
    , .immediate none
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b4_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 4, 9,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .immediate none
    , .immediate none
    , .immediate (some (.ptr ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b5_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 5, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .immediate none
    , .immediate (some (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b5_1 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 5, 1,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .immediate (some (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1))
    , .immediate (some (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b5_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 5, 2,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some .unit)
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .immediate (some (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1))
    , .immediate (some (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_1 nid, mBuf3_1 nid]⟩⟩

private noncomputable def m_b6_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 6, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .immediate (some (.unit))
    , .immediate none
    , .immediate none
    , .immediate (some (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b6_6 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 6, 6,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate none
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b6_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 6, 7,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate none
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b7_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 7, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b7_4 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 7, 4,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate none
    , .immediate none
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b7_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 7, 5,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate none
    , .immediate none
    , .immediate (some (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b8_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 8, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate none
    , .immediate (some (.ptr ⟨some (nid + 3), UInt64.ofNat 0, .isize⟩))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b8_1 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 8, 1,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .immediate (some (.ptr ⟨some (nid + 3), UInt64.ofNat 0, .isize⟩))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool true))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b8_6 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 8, 6,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .immediate none
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_2 nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b8_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 8, 7,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .immediate none
    , .immediate (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 2))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 4, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_uninit nid, mBuf3_2 nid]⟩⟩

private noncomputable def m_b9_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 9, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 5, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid]⟩⟩

private noncomputable def m_b9_3 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 9, 3,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)))
    , .dead
    , .immediate none
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 5, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid]⟩⟩

private noncomputable def m_b9_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 9, 4,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate none
    , .immediate (some (.ptr ⟨some (nid + 5), UInt64.ofNat 0, .isize⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 6, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_0 nid]⟩⟩

private noncomputable def m_b10_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 0,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)))
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_0 nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_6 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 6,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)))
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .immediate none
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_1 nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_0 nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_7 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 7,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)))
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .immediate (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1))
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_0 nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_8 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 8,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)))
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .immediate (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1))
    , .immediate none
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_0 nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_9 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 9,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)))
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .immediate (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1))
    , .immediate (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)))
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_uninit nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_10 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 10,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate (some (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)))
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .immediate (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1))
    , .immediate (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)))
    , .immediate none
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_uninit nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_11 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 11,
    [.immediate none
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .immediate none
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .immediate (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1))
    , .immediate (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)))
    , .immediate (some (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)))
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_uninit nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_18 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 18,
    [.immediate (some (
        .tuple
            [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
            , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
            , .vec
                ⟨some (nid + 0),
                  0, .isize⟩ 1 1
            , .boxPtr
                ⟨some (nid + 4),
                  0, .isize⟩ (some 2)
            , .boxPtr
                ⟨some (nid + 6),
                  0, .isize⟩ (some 2)
            ]))
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .indirect ⟨nid + 5, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_uninit nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_19 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 19,
    [.immediate (some (
        .tuple
            [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
            , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
            , .vec
                ⟨some (nid + 0),
                  0, .isize⟩ 1 1
            , .boxPtr
                ⟨some (nid + 4),
                  0, .isize⟩ (some 2)
            , .boxPtr
                ⟨some (nid + 6),
                  0, .isize⟩ (some 2)
            ]))
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (
        .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩))
    , .dead
    , .immediate (some (
        .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_dead nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_22 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 22,
    [.immediate (some (
        .tuple
            [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
            , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
            , .vec
                ⟨some (nid + 0),
                  0, .isize⟩ 1 1
            , .boxPtr
                ⟨some (nid + 4),
                  0, .isize⟩ (some 2)
            , .boxPtr
                ⟨some (nid + 6),
                  0, .isize⟩ (some 2)
            ]))
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .indirect ⟨nid + 2, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_dead nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_23 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 23,
    [.immediate (some (
        .tuple
            [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
            , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
            , .vec
                ⟨some (nid + 0),
                  0, .isize⟩ 1 1
            , .boxPtr
                ⟨some (nid + 4),
                  0, .isize⟩ (some 2)
            , .boxPtr
                ⟨some (nid + 6),
                  0, .isize⟩ (some 2)
            ]))
    , .indirect ⟨nid + 1, 0⟩
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid,
       mVec2_dead nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_dead nid, mClone6 nid]⟩⟩

private noncomputable def m_b10_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨0, 10, 24,
    [.immediate (some (
        .tuple
            [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
            , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
            , .vec
                ⟨some (nid + 0),
                  0, .isize⟩ 1 1
            , .boxPtr
                ⟨some (nid + 4),
                  0, .isize⟩ (some 2)
            , .boxPtr
                ⟨some (nid + 6),
                  0, .isize⟩ (some 2)
            ]))
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.bool false))], none, none, none⟩],
    cm, ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_dead nid,
       mVec2_dead nid, mBuf3_dead nid, mBuf4 nid,
       mBox5_dead nid, mClone6 nid]⟩⟩

private theorem m0_tr_0 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b0_0 cm nid) (m_b0_t cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl (ChainTo.refl _)))

private theorem m0_tr_1 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b0_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b1_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  have hCall : execCoreCallOpWithMem ⟨nid + 0, cm.allocations⟩
      (.vecWithCapacity (.int .i8 false))
      [(.int .isize false, .scalar
  ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 1)⟩)]
      (.vec (.int .i8 false)) =
      .ok (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0,
        ⟨nid + 1, cm.allocations ++ [mBuf0_init nid]⟩) := by
    refine execCoreCallOpWithMem_eq_allocOutcome ?_
    unfold execAllocCoreCallOutcome evalVecWithCapacityOutcome
    rfl
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl hCall
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_2 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b1_0 cm nid) (m_b1_2 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl (ChainTo.refl _)))

private theorem m0_tr_3 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b1_2 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b1_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m1 : MemoryState := ⟨nid + 2,
    cm.allocations ++ [mBuf0_init nid,
      ⟨nid + 1, 3, .mut, List.replicate 24 .uninit, true⟩]⟩
  have hFindV0 : findAllocation (nid + 1)
      (m1).allocations =
      some (⟨nid + 1, 3, .mut, List.replicate 24 .uninit, true⟩) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hStore : storeIndirectV2 m1 (.vec (.int .i8 false)) ⟨nid + 1, 0⟩
      (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0) =
      .ok ⟨nid + 2,
        cm.allocations ++ [mBuf0_init nid, mVec1_0 nid]⟩
      := by
    refine storeIndirectV2_ok layoutOfTyV2_vec_u8
      (encodeValV2_vec_u8 (nid + 0) 1 0) ?_
    rw [writeBytes_ok
      (⟨nid + 1, 3, .mut, List.replicate 24 .uninit, true⟩)
      rfl hFindV0 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
    rfl
  have hStore' : storeIndirectV2
      ⟨nid + 2, (cm.allocations ++ [mBuf0_init nid]) ++
        [⟨nid + 1, 3, .mut, List.replicate 24 .uninit, true⟩]⟩
      (.vec (.int .i8 false)) ⟨nid + 1, 0⟩
      (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0) =
      .ok ⟨nid + 2,
        cm.allocations ++ [mBuf0_init nid, mVec1_0 nid]⟩
      := by
    rw [List.append_assoc]; exact hStore
  let m2 : MemoryState :=
    ⟨nid + 2, cm.allocations ++ [mBuf0_init nid, mVec1_0 nid]⟩
  have hFindV : findAllocation (nid + 1)
      (m2).allocations = some (mVec1_0 nid) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hFindB : findAllocation (nid + 0)
      (m2).allocations = some (mBuf0_init nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec1_0 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0)) := by
    have hBs : ((mVec1_0 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m2 true (.int .i8 false)
      ⟨some (nid + 0), 0, .isize⟩ 1 0 = .ok () :=
    ownedBuf_int_ok (mBuf0_init nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRef : refValidInMem m2 .mut (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  exact evalStepV2_assign_ref_local rfl rfl rfl rfl
    (promoteLocalToMemory_imm_ok rfl rfl layoutOfTyV2_vec_u8 hStore' rfl)
    hRef (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_4 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b1_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b2_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState :=
    ⟨nid + 2, cm.allocations ++ [mBuf0_init nid, mVec1_0 nid]⟩
  have hFindV0 : findAllocation (nid + 1)
      (m0).allocations = some (mVec1_0 nid) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hFindB0 : findAllocation (nid + 0)
      (m0).allocations = some (mBuf0_init nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec1_0 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0)) := by
    have hBs : ((mVec1_0 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 true (.int .i8 false)
      ⟨some (nid + 0), 0, .isize⟩ 1 0 = .ok () :=
    ownedBuf_int_ok (mBuf0_init nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB0 rfl rfl rfl rfl rfl
  have hRef : refValidInMem m0 .mut (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV0 rfl rfl rfl rfl hDec hBuf
  have hLoad : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 1, 0⟩ =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 0)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV0 rfl rfl rfl) hDec
  have hRead : readVecFromRef m0 true (.int .i8 false)
      ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some (nid + 0), 0, .isize⟩, 1, 0⟩ :=
    readVecFromRef_u8_ok hRef hLoad hBuf
  have hWrBuf : writeBytes m0 ⟨nid + 0, 0⟩ 0 [.init 9 none] =
      .ok ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_0 nid]⟩ := by
    rw [writeBytes_ok (mBuf0_init nid) rfl hFindB0 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
    rfl
  let m1 : MemoryState :=
    ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_0 nid]⟩
  have hFindV1 : findAllocation (nid + 1)
      (m1).allocations = some (mVec1_0 nid) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hWrVec : writeVecToRef m1 ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, ⟨some (nid + 0), 0, .isize⟩, 1,
        UInt64.ofNat (0 + 1)⟩ =
      .ok ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid]⟩ := by
    refine writeVecToRef_u8_ok
      (storeIndirectV2_ok layoutOfTyV2_vec_u8
        (encodeValV2_vec_u8 (nid + 0) 1 1) ?_)
    rw [writeBytes_ok (mVec1_0 nid) rfl hFindV1 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
    rfl
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalVecPush_u8_inBounds hRead rfl rfl rfl rfl hWrBuf hWrVec)
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_5 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b2_0 cm nid) (m_b2_t cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl (ChainTo.refl _))))

private theorem m0_tr_6 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b2_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b3_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState :=
    ⟨nid + 2, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid]⟩
  have hCall : execCoreCallOpWithMem m0 (.vecNew (.int .i8 false)) []
      (.vec (.int .i8 false)) = .ok (.vec ⟨none, 1, .isize⟩ 0 0, m0) := by
    refine execCoreCallOpWithMem_eq_allocInfallible rfl ?_
    unfold execAllocCoreCallInfallible evalVecNew
    rfl
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl hCall
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_7 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b3_0 cm nid) (m_b3_3 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl (ChainTo.refl _))))

private theorem m0_tr_8 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b3_3 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b3_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m1 : MemoryState := ⟨nid + 3,
    cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid,
      ⟨nid + 2, 3, .mut, List.replicate 24 .uninit, true⟩]⟩
  have hFindV0 : findAllocation (nid + 2)
      (m1).allocations =
      some (⟨nid + 2, 3, .mut, List.replicate 24 .uninit, true⟩) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hStore : storeIndirectV2 m1 (.vec (.int .i8 false)) ⟨nid + 2, 0⟩
      (.vec ⟨none, 1, .isize⟩ 0 0) =
      .ok ⟨nid + 3,
        cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid]⟩ := by
    refine storeIndirectV2_ok layoutOfTyV2_vec_u8
      (encodeValV2_vec_dangling 1 0 0) ?_
    rw [writeBytes_ok
      (⟨nid + 2, 3, .mut, List.replicate 24 .uninit, true⟩)
      rfl hFindV0 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
    rfl
  have hStore' : storeIndirectV2
      ⟨nid + 3, (cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid]) ++
        [⟨nid + 2, 3, .mut, List.replicate 24 .uninit, true⟩]⟩
      (.vec (.int .i8 false)) ⟨nid + 2, 0⟩ (.vec ⟨none, 1, .isize⟩ 0 0) =
      .ok ⟨nid + 3,
        cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid]⟩ := by
    rw [List.append_assoc]; exact hStore
  let m2 : MemoryState :=
    ⟨nid + 3, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid]⟩
  have hFindV : findAllocation (nid + 2)
      (m2).allocations = some (mVec2_0 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_0 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨none, 1, .isize⟩ 0 0)) := by
    have hBs : ((mVec2_0 nid).bytes.drop 0).take 24 =
         [.init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_dangling]; rfl
  have hBuf : ownedHeapBufValidInMem m2 true (.int .i8 false)
      ⟨none, 1, .isize⟩ 0 0 = .ok () :=
    ownedBuf_zero_ok layoutOfTyV2_u8 rfl rfl rfl
  have hRef : refValidInMem m2 .mut (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  exact evalStepV2_assign_ref_local rfl rfl rfl rfl
    (promoteLocalToMemory_imm_ok rfl rfl layoutOfTyV2_vec_u8 hStore' rfl)
    hRef (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_9 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b3_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b4_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState :=
    ⟨nid + 3, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid]⟩
  have hFindV0 : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_0 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_0 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨none, 1, .isize⟩ 0 0)) := by
    have hBs : ((mVec2_0 nid).bytes.drop 0).take 24 =
         [.init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_dangling]; rfl
  have hBuf : ownedHeapBufValidInMem m0 true (.int .i8 false)
      ⟨none, 1, .isize⟩ 0 0 = .ok () :=
    ownedBuf_zero_ok layoutOfTyV2_u8 rfl rfl rfl
  have hRef : refValidInMem m0 .mut (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV0 rfl rfl rfl rfl hDec hBuf
  have hLoad : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 2, 0⟩ =
      .ok (some (.vec ⟨none, 1, .isize⟩ 0 0)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV0 rfl rfl rfl) hDec
  have hRead : readVecFromRef m0 true (.int .i8 false)
      ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨none, 1, .isize⟩, 0, 0⟩ :=
    readVecFromRef_u8_ok hRef hLoad hBuf
  let m2a : MemoryState :=
    ⟨nid + 4, cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid,
      ⟨nid + 3, 0, .mut, List.replicate 8 .uninit, true⟩]⟩
  have hFindB0 : findAllocation (nid + 3)
      (m2a).allocations =
      some (⟨nid + 3, 0, .mut, List.replicate 8 .uninit, true⟩) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hWrBuf : writeBytes m2a ⟨nid + 3, 0⟩ 0 [.init 10 none] =
      .ok ⟨nid + 4, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid, mBuf3_1 nid]⟩ := by
    rw [writeBytes_ok
      (⟨nid + 3, 0, .mut, List.replicate 8 .uninit, true⟩)
      rfl hFindB0 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
    rfl
  have hWrBuf' : writeBytes
      ⟨nid + 4, (cm.allocations ++ [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid]) ++
        [⟨nid + 3, 0, .mut, List.replicate 8 .uninit, true⟩]⟩
      ⟨nid + 3, 0⟩ 0 [.init 10 none] =
      .ok ⟨nid + 4, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid, mBuf3_1 nid]⟩ := by
    rw [List.append_assoc]; exact hWrBuf
  have hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false)
      (.scalar
  ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩) =
      .ok [.init 10 none] := rfl
  let m2b : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_0 nid, mBuf3_1 nid]⟩
  have hFindV1 : findAllocation (nid + 2)
      (m2b).allocations = some (mVec2_0 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hWrVec : writeVecToRef m2b ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, ⟨some (nid + 3), 0, .isize⟩, 8, 1⟩ =
      .ok ⟨nid + 4, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_1 nid, mBuf3_1 nid]⟩ := by
    refine writeVecToRef_u8_ok
      (storeIndirectV2_ok layoutOfTyV2_vec_u8
        (encodeValV2_vec_u8 (nid + 3) 8 1) ?_)
    rw [writeBytes_ok (mVec2_0 nid) rfl hFindV1 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
    rfl
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalVecPush_u8_fromEmpty hRead hEnc rfl hWrBuf' hWrVec)
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_10 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b4_0 cm nid) (m_b4_4 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl
        (ChainTo.step rfl (ChainTo.refl _)))))

private theorem m0_tr_11 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b4_4 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b4_5 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid,
     mVec2_1 nid, mBuf3_1 nid]⟩
  have hFindV : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_1 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hFindB : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_1 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_1 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩
        8 1)) := by
    have hBs : ((mVec2_1 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 8 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 true (.int .i8 false)
      ⟨some (nid + 3), 0, .isize⟩
      8 1 = .ok () :=
    ownedBuf_int_ok (mBuf3_1 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRef : refValidInMem m0 .mut (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) =
      .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  exact evalStepV2_assign_ref_local rfl rfl rfl rfl
    (promoteLocalToMemory_indirect_ok rfl rfl rfl)
    hRef (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_12 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b4_5 cm nid) (m_b4_8 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl (ChainTo.refl _))))

private theorem m0_tr_13 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b4_8 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b4_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid,
     mVec2_1 nid, mBuf3_1 nid]⟩
  have hFindV : findAllocation (nid + 1)
      (m0).allocations = some (mVec1_1 nid) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hFindB : findAllocation (nid + 0)
      (m0).allocations = some (mBuf0_1 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec1_1 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩
        1 1)) := by
    have hBs : ((mVec1_1 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 0), 0, .isize⟩
      1 1 = .ok () :=
    ownedBuf_int_ok (mBuf0_1 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRef : refValidInMem m0 .shared (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩) =
      .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  exact evalStepV2_assign_ref_local rfl rfl rfl rfl
    (promoteLocalToMemory_indirect_ok rfl rfl rfl)
    hRef (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_14 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b4_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b5_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_1 nid, mBuf3_1 nid]⟩
  have hFindV : findAllocation (nid + 1)
      (m0).allocations = some (mVec1_1 nid) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hFindB : findAllocation (nid + 0)
      (m0).allocations = some (mBuf0_1 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec1_1 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1)) := by
    have hBs : ((mVec1_1 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 0), 0, .isize⟩ 1 1 = .ok () :=
    ownedBuf_int_ok (mBuf0_1 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRefV : refValidInMem m0 .shared (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  have hLoad : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 1, 0⟩ =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV rfl rfl rfl) hDec
  have hRead : readVecFromRef m0 false (.int .i8 false)
      ⟨some (nid + 1), UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some (nid + 0), 0, .isize⟩, 1, 1⟩ :=
    readVecFromRef_u8_ok hRefV hLoad hBuf
  have hRefS : refValidInMem m0 .shared (.slice (.int .i8 false))
      (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1) = .ok () :=
    refValidInMem_slice_u8_ok (mBuf0_1 nid) rfl hFindB rfl rfl rfl rfl rfl
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalVecDeref_shared_u8 hRead hRefS)
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_15 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b5_0 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b5_1 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_1 nid, mBuf3_1 nid]⟩
  have hFindB : findAllocation (nid + 0)
      (m0).allocations = some (mBuf0_1 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hRefS : refValidInMem m0 .shared (.slice (.int .i8 false))
      (.slicePtr ⟨some (nid + 0), 0, .isize⟩ 1) = .ok () :=
    refValidInMem_slice_u8_ok (mBuf0_1 nid) rfl hFindB rfl rfl rfl rfl rfl
  exact evalStepV2_assign_reborrow_slice_u8 rfl rfl rfl rfl rfl rfl hRefS
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_16 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b5_1 cm nid) (m_b5_t cm nid) :=
  (ChainTo.step rfl (ChainTo.refl _))

private theorem m0_tr_17 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b5_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b6_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_1 nid, mBuf3_1 nid]⟩
  have hFindV2 : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_1 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hFindB3 : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_1 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hFindB0 : findAllocation (nid + 0)
      (m0).allocations = some (mBuf0_1 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_1 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 1)) := by
    have hBs : ((mVec2_1 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 8 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf3 : ownedHeapBufValidInMem m0 true (.int .i8 false)
      ⟨some (nid + 3), 0, .isize⟩ 8 1 = .ok () :=
    ownedBuf_int_ok (mBuf3_1 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB3 rfl rfl rfl rfl rfl
  have hRefV2 : refValidInMem m0 .mut (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV2 rfl rfl rfl rfl hDec hBuf3
  have hLoadV2 : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 2, 0⟩ =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 1)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV2 rfl rfl rfl) hDec
  have hRead : readVecFromRef m0 true (.int .i8 false)
      ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some (nid + 3), 0, .isize⟩, 8, 1⟩ :=
    readVecFromRef_u8_ok hRefV2 hLoadV2 hBuf3
  have hSrcValid : heapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 0), 0, .isize⟩ 1 1 = .ok () :=
    heapBufValidInMem_int_ok (mBuf0_1 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB0 rfl rfl rfl rfl rfl
  have hReadSrc : readBytes m0 ⟨nid + 0, 0⟩ (UInt64.toNat 1 * 1) 0 =
      .ok [.init 9 none] := by
    rw [readBytes_ok rfl hFindB0 rfl rfl rfl]; rfl
  have hWrBuf : writeBytes m0 ⟨nid + 3, 1⟩ 0 [.init 9 none] =
      .ok ⟨nid + 4, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_1 nid, mBuf3_2 nid]⟩ := by
    rw [writeBytes_ok (mBuf3_1 nid) rfl hFindB3 rfl rfl
      (isAligned_align0 (mBuf3_1 nid) 1 rfl) rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
    rfl
  let m1 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_1 nid, mBuf3_2 nid]⟩
  have hFindV2b : findAllocation (nid + 2)
      (m1).allocations = some (mVec2_1 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hWrVec : writeVecToRef m1 ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩
      ⟨.int .i8 false, ⟨some (nid + 3), 0, .isize⟩, 8,
        UInt64.ofNat (UInt64.toNat 1 + UInt64.toNat 1)⟩ =
      .ok ⟨nid + 4, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_2 nid, mBuf3_2 nid]⟩ := by
    refine writeVecToRef_u8_ok
      (storeIndirectV2_ok layoutOfTyV2_vec_u8
        (encodeValV2_vec_u8 (nid + 3) 8 (UInt64.ofNat (1 + 1))) ?_)
    rw [writeBytes_ok (mVec2_1 nid) rfl hFindV2b rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
    rfl
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalVecExtendFromSlice_u8_inBounds hRead hSrcValid rfl rfl hReadSrc rfl rfl
      (natBeq_add_ne nid 0 3 rfl) hWrBuf hWrVec)
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_18 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b6_0 cm nid) (m_b6_6 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl
        (ChainTo.step rfl
          (ChainTo.step rfl
            (ChainTo.step rfl (ChainTo.refl _)))))))

private theorem m0_tr_19 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b6_6 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b6_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid,
     mVec2_2 nid, mBuf3_2 nid]⟩
  have hFindV : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_2 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hFindB : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_2 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_2 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩
        8 2)) := by
    have hBs : ((mVec2_2 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 8 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 3), 0, .isize⟩
      8 2 = .ok () :=
    ownedBuf_int_ok (mBuf3_2 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRef : refValidInMem m0 .shared (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) =
      .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  exact evalStepV2_assign_ref_local rfl rfl rfl rfl
    (promoteLocalToMemory_indirect_ok rfl rfl rfl)
    hRef (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_20 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b6_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b7_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_2 nid, mBuf3_2 nid]⟩
  have hFindV : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_2 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hFindB : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_2 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_2 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 2)) := by
    have hBs : ((mVec2_2 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 8 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 3), 0, .isize⟩ 8 2 = .ok () :=
    ownedBuf_int_ok (mBuf3_2 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRef : refValidInMem m0 .shared (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  have hLoad : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 2, 0⟩ =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 2)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV rfl rfl rfl) hDec
  have hRead : readVecFromRef m0 false (.int .i8 false)
      ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some (nid + 3), 0, .isize⟩, 8, 2⟩ :=
    readVecFromRef_u8_ok hRef hLoad hBuf
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalVecLen_u8 hRead)
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_21 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b7_0 cm nid) (m_b7_4 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl
        (ChainTo.step rfl (ChainTo.refl _)))))

private theorem m0_tr_22 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b7_4 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b7_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid,
     mVec2_2 nid, mBuf3_2 nid]⟩
  have hFindV : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_2 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hFindB : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_2 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_2 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩
        8 2)) := by
    have hBs : ((mVec2_2 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 8 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 3), 0, .isize⟩
      8 2 = .ok () :=
    ownedBuf_int_ok (mBuf3_2 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRef : refValidInMem m0 .shared (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) =
      .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  exact evalStepV2_assign_ref_local rfl rfl rfl rfl
    (promoteLocalToMemory_indirect_ok rfl rfl rfl)
    hRef (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_23 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b7_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b8_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_2 nid, mBuf3_2 nid]⟩
  have hFindV : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_2 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hFindB : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_2 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_2 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 2)) := by
    have hBs : ((mVec2_2 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 8 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 3), 0, .isize⟩ 8 2 = .ok () :=
    ownedBuf_int_ok (mBuf3_2 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRefV : refValidInMem m0 .shared (.vec (.int .i8 false))
      (.ptr ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_vec_u8_ok hFindV rfl rfl rfl rfl hDec hBuf
  have hLoad : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 2, 0⟩ =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 2)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV rfl rfl rfl) hDec
  have hRead : readVecFromRef m0 false (.int .i8 false)
      ⟨some (nid + 2), UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.int .i8 false, ⟨some (nid + 3), 0, .isize⟩, 8, 2⟩ :=
    readVecFromRef_u8_ok hRefV hLoad hBuf
  have hRefE : refValidInMem m0 .shared (.int .i8 false)
      (.ptr ⟨some (nid + 3), UInt64.ofNat (0 + 0 * 1), .isize⟩) = .ok () :=
    refValidInMem_u8_ok hFindB rfl rfl rfl rfl rfl
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalVecIndex_u8 hRead rfl rfl hFindB rfl rfl hRefE)
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_24 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b8_0 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b8_1 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_2 nid, mBuf3_2 nid]⟩
  have hFindB : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_2 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hLoad : loadIndirectV2 m0 (.int .i8 false) ⟨nid + 3, 0⟩ =
      .ok (some (.scalar
  ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩)) :=
    loadIndirectV2_ok layoutOfTyV2_u8
      (readBytes_ok rfl hFindB rfl rfl rfl) rfl
  exact evalStepV2_assign_copy_deref rfl rfl rfl rfl rfl (Or.inl rfl) rfl
    layoutOfTyV2_u8 rfl rfl hLoad (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_25 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b8_1 cm nid) (m_b8_6 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl
        (ChainTo.step rfl
          (ChainTo.step rfl (ChainTo.refl _))))))

private theorem m0_tr_26 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b8_6 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b8_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_2 nid, mBuf3_2 nid]⟩
  have hFindV : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_2 nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec2_2 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 2)) := by
    have hBs : ((mVec2_2 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 0 (some (nid + 3))
         , .init 8 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hLoad : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 2, 0⟩ =
      .ok (some (.vec ⟨some (nid + 3), 0, .isize⟩ 8 2)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV rfl rfl rfl) hDec
  have hDeinit : deinitIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 2, 0⟩ =
      .ok ⟨nid + 4, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_2 nid]⟩ := by
    refine writeUninit_ok ?_
    rw [writeBytes_ok (mVec2_2 nid) rfl hFindV rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
    rfl
  exact evalStepV2_assign_move_indirect rfl rfl rfl rfl rfl rfl rfl hLoad
    hDeinit (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_27 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b8_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b9_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 4, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_2 nid]⟩
  have hFindB : findAllocation (nid + 3)
      (m0).allocations = some (mBuf3_2 nid) := by
    rw [findAllocation_append_nid 3]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
  have hBuf : ownedHeapBufValidInMem m0 true (.int .i8 false)
      ⟨some (nid + 3), 0, .isize⟩ 8 2 = .ok () :=
    ownedBuf_int_ok (mBuf3_2 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB rfl rfl rfl rfl rfl
  have hRead : readBytes m0 ⟨nid + 3, 0⟩ (UInt64.toNat 2 * 1) 0 =
      .ok [.init 10 none, .init 9 none] := by
    rw [readBytes_ok rfl hFindB rfl rfl rfl]; rfl
  have hDealloc : deallocateStack m0 ⟨nid + 3, 0⟩ =
      .ok ⟨nid + 4, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid]⟩ := by
    rw [deallocateStack_ok (mBuf3_2 nid) rfl hFindB rfl rfl]
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 3 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 3 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 3 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 3 3 rfl)]
    rfl
  let m1 : MemoryState := ⟨nid + 5, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
      ⟨nid + 4, 0, .mut,
        List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩]⟩
  have hFind4 : findAllocation (nid + 4)
      (m1).allocations =
      some (⟨nid + 4, 0, .mut,
      List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩) := by
    rw [findAllocation_append_nid 4]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 4 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 4 4 rfl)]
  have hWr : writeBytes m1 ⟨nid + 4, 0⟩ 0 [.init 10 none, .init 9 none] =
      .ok ⟨nid + 5, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
          mBuf4 nid]⟩ := by
    rw [writeBytes_ok
      (⟨nid + 4, 0, .mut,
      List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩)
      rfl hFind4 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 4 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 4 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 4 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 3 4 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 4 4 rfl)]
    rfl
  have hWr' : writeBytes
      ⟨nid + 4 + 1, (cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid]) ++
        [⟨nid + 4, 0, .mut,
        List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩]⟩
      ⟨nid + 4, 0⟩ 0 [.init 10 none, .init 9 none] =
      .ok ⟨nid + 5, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
          mBuf4 nid]⟩ := by
    rw [List.append_assoc]; exact hWr
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalBoxFromVec_u8_realloc hBuf rfl rfl hRead hDealloc hWr')
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_28 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b9_0 cm nid) (m_b9_3 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl (ChainTo.refl _))))

private theorem m0_tr_29 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b9_3 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b9_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m1 : MemoryState := ⟨nid + 6, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
      ⟨nid + 5, 3, .mut, List.replicate 16 .uninit, true⟩]⟩
  have hFindB4_0 : findAllocation (nid + 5)
      (m1).allocations =
      some (⟨nid + 5, 3, .mut, List.replicate 16 .uninit, true⟩) := by
    rw [findAllocation_append_nid 5]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
  have hStore : storeIndirectV2 m1
      (.box (.slice (.int .i8 false))) ⟨nid + 5, 0⟩
      (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)) =
      .ok ⟨nid + 6, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid,
         mBuf3_dead nid, mBuf4 nid, mBox5_0 nid]⟩ := by
    refine storeIndirectV2_ok layoutOfTyV2_box_slice_u8
      (encodeValV2_box_slice_u8 (nid + 4) 2) ?_
    rw [writeBytes_ok
      (⟨nid + 5, 3, .mut, List.replicate 16 .uninit, true⟩)
      rfl hFindB4_0 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
    rfl
  have hStore' : storeIndirectV2
      ⟨nid + 6, (cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
         mBuf4 nid]) ++
        [⟨nid + 5, 3, .mut, List.replicate 16 .uninit, true⟩]⟩
      (.box (.slice (.int .i8 false))) ⟨nid + 5, 0⟩
      (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)) =
      .ok ⟨nid + 6, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid,
         mBuf3_dead nid, mBuf4 nid, mBox5_0 nid]⟩ := by
    rw [List.append_assoc]; exact hStore
  let m2 : MemoryState := ⟨nid + 6, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
     mBuf4 nid, mBox5_0 nid]⟩
  have hFindB4 : findAllocation (nid + 5)
      (m2).allocations = some (mBox5_0 nid) := by
    rw [findAllocation_append_nid 5]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
  have hFindB3 : findAllocation (nid + 4)
      (m2).allocations = some (mBuf4 nid) := by
    rw [findAllocation_append_nid 4]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 4 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 4 4 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian
      (.box (.slice (.int .i8 false)))
      (((mBox5_0 nid).bytes.drop 0).take 16) =
      .ok (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2))) := by
    have hBs : ((mBox5_0 nid).bytes.drop 0).take 16 =
         [.init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_box_slice_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m2 false (.int .i8 false)
      ⟨some (nid + 4), 0, .isize⟩ 2 2 = .ok () :=
    ownedBuf_int_ok (mBuf4 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB3 rfl rfl rfl rfl rfl
  have hRef : refValidInMem m2 .shared (.box (.slice (.int .i8 false)))
      (.ptr ⟨some (nid + 5), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_box_slice_u8_ok hFindB4 rfl rfl rfl rfl hDec hBuf
  exact evalStepV2_assign_ref_local rfl rfl rfl rfl
    (promoteLocalToMemory_imm_ok rfl rfl layoutOfTyV2_box_slice_u8 hStore' rfl)
    hRef (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_30 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b9_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b10_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 6, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
     mBuf4 nid, mBox5_0 nid]⟩
  have hFindB4 : findAllocation (nid + 5)
      (m0).allocations = some (mBox5_0 nid) := by
    rw [findAllocation_append_nid 5]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
  have hFindB3 : findAllocation (nid + 4)
      (m0).allocations = some (mBuf4 nid) := by
    rw [findAllocation_append_nid 4]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 4 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 4 4 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian
      (.box (.slice (.int .i8 false)))
      (((mBox5_0 nid).bytes.drop 0).take 16) =
      .ok (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2))) := by
    have hBs : ((mBox5_0 nid).bytes.drop 0).take 16 =
         [.init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_box_slice_u8_zero]; rfl
  have hBuf : ownedHeapBufValidInMem m0 false (.int .i8 false)
      ⟨some (nid + 4), 0, .isize⟩ 2 2 = .ok () :=
    ownedBuf_int_ok (mBuf4 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB3 rfl rfl rfl rfl rfl
  have hRef : refValidInMem m0 .shared (.box (.slice (.int .i8 false)))
      (.ptr ⟨some (nid + 5), UInt64.ofNat 0, .isize⟩) = .ok () :=
    refValidInMem_box_slice_u8_ok hFindB4 rfl rfl rfl rfl hDec hBuf
  have hLoad : loadIndirectV2 m0
      (.box (.slice (.int .i8 false))) ⟨nid + 5, 0⟩ =
      .ok (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2))) :=
    loadIndirectV2_ok layoutOfTyV2_box_slice_u8
      (readBytes_ok rfl hFindB4 rfl rfl rfl) hDec
  have hReadBox : readBoxFromRef m0 false (.slice (.int .i8 false))
      ⟨some (nid + 5), UInt64.ofNat 0, .isize⟩ =
      .ok ⟨.slice (.int .i8 false), ⟨some (nid + 4), 0, .isize⟩, some 2⟩ :=
    readBoxFromRef_slice_u8_ok hRef hLoad hBuf
  have hRead : readBytes m0 ⟨nid + 4, 0⟩ (UInt64.toNat 2 * 1) 0 =
      .ok [.init 10 none, .init 9 none] := by
    rw [readBytes_ok rfl hFindB3 rfl rfl rfl]; rfl
  let m1 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
     mBuf4 nid, mBox5_0 nid,
      ⟨nid + 6, 0, .mut,
        List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩]⟩
  have hFindC : findAllocation (nid + 6)
      (m1).allocations =
      some (⟨nid + 6, 0, .mut,
      List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩) := by
    rw [findAllocation_append_nid 6]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 5 6 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 6 6 rfl)]
  have hWr : writeBytes m1 ⟨nid + 6, 0⟩ 0 [.init 10 none, .init 9 none] =
      .ok ⟨nid + 7, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
         mBuf4 nid, mBox5_0 nid,
          mClone6 nid]⟩ := by
    rw [writeBytes_ok
      (⟨nid + 6, 0, .mut,
      List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩)
      rfl hFindC rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 6 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 6 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 6 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 3 6 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 4 6 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 5 6 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 6 6 rfl)]
    rfl
  have hWr' : writeBytes
      ⟨nid + 7, (cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid,
         mBuf3_dead nid, mBuf4 nid, mBox5_0 nid]) ++
        [⟨nid + 6, 0, .mut,
        List.replicate (UInt64.toNat 2 * 1) .uninit, true⟩]⟩
      ⟨nid + 6, 0⟩ 0 [.init 10 none, .init 9 none] =
      .ok ⟨nid + 7, cm.allocations ++
        [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid, mBuf3_dead nid,
         mBuf4 nid, mBox5_0 nid,
          mClone6 nid]⟩ := by
    rw [List.append_assoc]; exact hWr
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
    (evalBoxClone_slice_u8 hReadBox rfl hRead hWr')
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_31 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b10_0 cm nid) (m_b10_6 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl
        (ChainTo.step rfl
          (ChainTo.step rfl
            (ChainTo.step rfl (ChainTo.refl _)))))))

private theorem m0_tr_32 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b10_6 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b10_7 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_1 nid, mVec2_uninit nid,
     mBuf3_dead nid, mBuf4 nid, mBox5_0 nid, mClone6 nid]⟩
  have hFindV : findAllocation (nid + 1)
      (m0).allocations = some (mVec1_1 nid) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (((mVec1_1 nid).bytes.drop 0).take 24) =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1)) := by
    have hBs : ((mVec1_1 nid).bytes.drop 0).take 24 =
         [.init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 0 (some (nid + 0))
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 1 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_vec_u8_zero]; rfl
  have hLoad : loadIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 1, 0⟩ =
      .ok (some (.vec ⟨some (nid + 0), 0, .isize⟩ 1 1)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFindV rfl rfl rfl) hDec
  have hDeinit : deinitIndirectV2 m0 (.vec (.int .i8 false)) ⟨nid + 1, 0⟩ =
      .ok ⟨nid + 7, cm.allocations ++
        [mBuf0_1 nid, mVec1_uninit nid, mVec2_uninit nid, mBuf3_dead nid,
         mBuf4 nid,
          mBox5_0 nid, mClone6 nid]⟩ := by
    refine writeUninit_ok ?_
    rw [writeBytes_ok (mVec1_1 nid) rfl hFindV rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
    rfl
  exact evalStepV2_assign_move_indirect rfl rfl rfl rfl rfl rfl rfl hLoad
    hDeinit (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_33 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b10_7 cm nid) (m_b10_8 cm nid) :=
  (ChainTo.step rfl (ChainTo.refl _))

private theorem m0_tr_34 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b10_8 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b10_9 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_uninit nid, mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
      mBox5_0 nid, mClone6 nid]⟩
  have hFindB4 : findAllocation (nid + 5)
      (m0).allocations = some (mBox5_0 nid) := by
    rw [findAllocation_append_nid 5]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
  have hDec : decodeValV2 profileV2TargetEndian
      (.box (.slice (.int .i8 false)))
      (((mBox5_0 nid).bytes.drop 0).take 16) =
      .ok (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2))) := by
    have hBs : ((mBox5_0 nid).bytes.drop 0).take 16 =
         [.init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 0 (some (nid + 4))
         , .init 2 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none
         , .init 0 none] := rfl
    rw [hBs, decodeValV2_box_slice_u8_zero]; rfl
  have hLoad : loadIndirectV2 m0
      (.box (.slice (.int .i8 false))) ⟨nid + 5, 0⟩ =
      .ok (some (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2))) :=
    loadIndirectV2_ok layoutOfTyV2_box_slice_u8
      (readBytes_ok rfl hFindB4 rfl rfl rfl) hDec
  let m1 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_uninit nid, mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
      mBox5_uninit nid, mClone6 nid]⟩
  have hDeinit : deinitIndirectV2 m0 (.box (.slice (.int .i8 false)))
      ⟨nid + 5, 0⟩ = .ok m1 := by
    refine writeUninit_ok ?_
    rw [writeBytes_ok (mBox5_0 nid) rfl hFindB4 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
    rfl
  have hFindB3 : findAllocation (nid + 4)
      (m1).allocations = some (mBuf4 nid) := by
    rw [findAllocation_append_nid 4]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 4 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 4 4 rfl)]
  have hBuf : ownedHeapBufValidInMem m1 true (.int .i8 false)
      ⟨some (nid + 4), 0, .isize⟩ 2 2 = .ok () :=
    ownedBuf_int_ok (mBuf4 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindB3 rfl rfl rfl rfl rfl
  have hRefs : refsValidInMem m1 (.box (.slice (.int .i8 false)))
      (.boxPtr ⟨some (nid + 4), 0, .isize⟩ (some 2)) = true :=
    refsValidInMem_box_slice_true hBuf
  exact evalStepV2_assign_useRetag_indirect rfl rfl rfl rfl rfl rfl rfl hLoad
    hDeinit hRefs (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_35 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b10_9 cm nid) (m_b10_10 cm nid) :=
  (ChainTo.step rfl (ChainTo.refl _))

private theorem m0_tr_36 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b10_10 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b10_11 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_uninit nid, mVec2_uninit nid, mBuf3_dead nid, mBuf4 nid,
      mBox5_uninit nid, mClone6 nid]⟩
  have hFindC : findAllocation (nid + 6)
      (m0).allocations = some (mClone6 nid) := by
    rw [findAllocation_append_nid 6]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 5 6 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 6 6 rfl)]
  have hBuf : ownedHeapBufValidInMem m0 true (.int .i8 false)
      ⟨some (nid + 6), 0, .isize⟩ 2 2 = .ok () :=
    ownedBuf_int_ok (mClone6 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFindC rfl rfl rfl rfl rfl
  have hRefs : refsValidInMem m0 (.box (.slice (.int .i8 false)))
      (.boxPtr ⟨some (nid + 6), 0, .isize⟩ (some 2)) = true :=
    refsValidInMem_box_slice_true hBuf
  exact evalStepV2_assign_useRetag_imm rfl rfl rfl rfl rfl rfl rfl rfl hRefs
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m0_tr_37 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b10_11 cm nid) (m_b10_18 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl
        (ChainTo.step rfl
          (ChainTo.step rfl
            (ChainTo.step rfl
              (ChainTo.step rfl (ChainTo.refl _))))))))

private theorem m0_tr_38 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b10_18 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b10_19 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_uninit nid, mVec2_uninit nid,
     mBuf3_dead nid, mBuf4 nid, mBox5_uninit nid, mClone6 nid]⟩
  have hFind : findAllocation (nid + 5)
      (m0).allocations = some (mBox5_uninit nid) := by
    rw [findAllocation_append_nid 5]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
  have hDealloc : deallocateStack m0 ⟨nid + 5, 0⟩ =
      .ok ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid, mVec2_uninit nid,
       mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid]⟩ := by
    rw [deallocateStack_ok (mBox5_uninit nid) rfl hFind rfl rfl]
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 2 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 3 5 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 4 5 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 5 5 rfl)]
    rfl
  exact evalStepV2_storageDead_indirect rfl rfl rfl rfl rfl rfl hDealloc

private theorem m0_tr_39 (cm : CallerMemory) (nid : Nat) :
    ChainTo (entryProgForBody Captured.program 0)
      (m_b10_19 cm nid) (m_b10_22 cm nid) :=
  (ChainTo.step rfl
    (ChainTo.step rfl
      (ChainTo.step rfl (ChainTo.refl _))))

private theorem m0_tr_40 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b10_22 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b10_23 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_uninit nid, mVec2_uninit nid,
     mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid]⟩
  have hFind : findAllocation (nid + 2)
      (m0).allocations = some (mVec2_uninit nid) := by
    rw [findAllocation_append_nid 2]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
  have hDealloc : deallocateStack m0 ⟨nid + 2, 0⟩ =
      .ok ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_uninit nid, mVec2_dead nid,
       mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid]⟩ := by
    rw [deallocateStack_ok (mVec2_uninit nid) rfl hFind rfl rfl]
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 2 rfl)]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 1 2 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 2 2 rfl)]
    rfl
  exact evalStepV2_storageDead_indirect rfl rfl rfl rfl rfl rfl hDealloc

private theorem m0_tr_41 (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 0)
      (m_b10_23 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m_b10_t cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_uninit nid, mVec2_dead nid,
     mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid]⟩
  have hFind : findAllocation (nid + 1)
      (m0).allocations = some (mVec1_uninit nid) := by
    rw [findAllocation_append_nid 1]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
  have hDealloc : deallocateStack m0 ⟨nid + 1, 0⟩ =
      .ok ⟨nid + 7, cm.allocations ++
      [mBuf0_1 nid, mVec1_dead nid, mVec2_dead nid,
       mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid]⟩ := by
    rw [deallocateStack_ok (mVec1_uninit nid) rfl hFind rfl rfl]
    rw [replaceAllocation_append_nid rfl]
    rw [replaceAllocation_cons_ne (natBeq_add_ne nid 0 1 rfl)]
    rw [replaceAllocation_cons_eq (natBeq_add_eq nid 1 1 rfl)]
    rfl
  exact evalStepV2_storageDead_indirect rfl rfl rfl rfl rfl rfl hDealloc

private theorem m0_chain (cm : CallerMemory)
    (hCM : validCallerMemory cm = true) :
    ChainStepV2 (entryProgForBody Captured.program 0)
      (m_b0_0 cm (entryMemoryWithCaller cm).nextAllocId)
      (.done (.returned ⟨.tuple
          [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
          , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
          , .vec
              ⟨some ((entryMemoryWithCaller cm).nextAllocId + 0),
                0, .isize⟩ 1 1
          , .boxPtr
              ⟨some ((entryMemoryWithCaller cm).nextAllocId + 4),
                0, .isize⟩ (some 2)
          , .boxPtr
              ⟨some ((entryMemoryWithCaller cm).nextAllocId + 6),
                0, .isize⟩ (some 2)
          ],
        ⟨cm.allocations ++
          [ mBuf0_1 (entryMemoryWithCaller cm).nextAllocId
          , mBuf4 (entryMemoryWithCaller cm).nextAllocId
          , mClone6 (entryMemoryWithCaller cm).nextAllocId ]⟩⟩)) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let mEnd : MemoryState := ⟨nid + 7, cm.allocations ++
    [mBuf0_1 nid, mVec1_dead nid, mVec2_dead nid,
     mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid]⟩
  have hLive : calleeLiveAllocations (allocIdsOf cm.allocations) []
      [mBuf0_1 nid, mVec1_dead nid, mVec2_dead nid,
       mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid] =
      [mBuf0_1 nid, mBuf4 nid, mClone6 nid] := by
    rw [calleeLive_cons_keep (a := mBuf0_1 nid) (fIds := []) rfl
      (natNotElem_callerIds cm 0) rfl]
    rw [calleeLive_cons_dead (a := mVec1_dead nid) rfl]
    rw [calleeLive_cons_dead (a := mVec2_dead nid) rfl]
    rw [calleeLive_cons_dead (a := mBuf3_dead nid) rfl]
    rw [calleeLive_cons_keep (a := mBuf4 nid) (fIds := []) rfl
      (natNotElem_callerIds cm 4) rfl]
    rw [calleeLive_cons_dead (a := mBox5_dead nid) rfl]
    rw [calleeLive_cons_keep (a := mClone6 nid) (fIds := []) rfl
      (natNotElem_callerIds cm 6) rfl]
    rfl
  have hMem : ∀ locals : List LocalSlot, frameLocalAllocIds locals = [] →
      extractReturnMemoryV2 cm mEnd locals =
        ⟨cm.allocations ++ [mBuf0_1 nid, mBuf4 nid, mClone6 nid]⟩ := by
    intro locals hL
    have h1 : extractReturnMemoryV2 cm mEnd locals =
        ⟨cm.allocations ++ calleeLiveAllocations (allocIdsOf cm.allocations)
          (frameLocalAllocIds locals)
          [mBuf0_1 nid, mVec1_dead nid, mVec2_dead nid,
           mBuf3_dead nid, mBuf4 nid, mBox5_dead nid, mClone6 nid]⟩ :=
      extractReturnMemoryV2_append hCM
    rw [h1, hL, hLive]
  have hFind0 : findAllocation (nid + 0)
      (mEnd).allocations = some (mBuf0_1 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hFind3 : findAllocation (nid + 4)
      (mEnd).allocations = some (mBuf4 nid) := by
    rw [findAllocation_append_nid 4]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 4 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 4 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 4 4 rfl)]
  have hFind5 : findAllocation (nid + 6)
      (mEnd).allocations = some (mClone6 nid) := by
    rw [findAllocation_append_nid 6]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 0 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 1 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 2 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 3 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 4 6 rfl)]
    rw [findAllocation_cons_ne (natBeq_add_ne nid 5 6 rfl)]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 6 6 rfl)]
  have hBuf0 : ownedHeapBufValidInMem mEnd true (.int .i8 false)
      ⟨some (nid + 0), 0, .isize⟩ 1 1 = .ok () :=
    ownedBuf_int_ok (mBuf0_1 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFind0 rfl rfl rfl rfl rfl
  have hBuf3 : ownedHeapBufValidInMem mEnd true (.int .i8 false)
      ⟨some (nid + 4), 0, .isize⟩ 2 2 = .ok () :=
    ownedBuf_int_ok (mBuf4 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFind3 rfl rfl rfl rfl rfl
  have hBuf5 : ownedHeapBufValidInMem mEnd true (.int .i8 false)
      ⟨some (nid + 6), 0, .isize⟩ 2 2 = .ok () :=
    ownedBuf_int_ok (mClone6 nid) layoutOfTyV2_u8
      rfl rfl rfl rfl hFind5 rfl rfl rfl rfl rfl
  have hRefs : refsValidInMem mEnd
      (.tuple [.int .isize false, .int .i8 false, .vec (.int .i8 false),
        .box (.slice (.int .i8 false)), .box (.slice (.int .i8 false))])
      (.tuple
        [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
        , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
        , .vec
            ⟨some (nid + 0),
              0, .isize⟩ 1 1
        , .boxPtr
            ⟨some (nid + 4),
              0, .isize⟩ (some 2)
        , .boxPtr
            ⟨some (nid + 6),
              0, .isize⟩ (some 2)
        ]) = true := by
    unfold refsValidInMem
    exact refsValidInMemList_cons mEnd _ _ _ _ rfl
      (refsValidInMemList_cons mEnd _ _ _ _ rfl
        (refsValidInMemList_cons mEnd _ _ _ _ (refsValidInMem_vec_true hBuf0)
          (refsValidInMemList_cons mEnd _ _ _ _
            (refsValidInMem_box_slice_true hBuf3)
            (refsValidInMemList_cons mEnd _ _ _ _
              (refsValidInMem_box_slice_true hBuf5)
              (refsValidInMemList_nil mEnd)))))
  have hRet : evalStepV2 (entryProgForBody Captured.program 0)
      (m_b10_t cm nid) =
      .done (.returned ⟨.tuple
        [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
        , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
        , .vec
            ⟨some (nid + 0),
              0, .isize⟩ 1 1
        , .boxPtr
            ⟨some (nid + 4),
              0, .isize⟩ (some 2)
        , .boxPtr
            ⟨some (nid + 6),
              0, .isize⟩ (some 2)
        ],
        ⟨cm.allocations ++ [mBuf0_1 nid, mBuf4 nid, mClone6 nid]⟩⟩) := by
    dsimp only [m_b10_t]
    refine Eq.trans
      (evalStepV2_return_imm rfl rfl rfl rfl rfl rfl rfl rfl hRefs
        (spansDisjoint3 (natBeq_add_ne nid 0 4 rfl) (natBeq_add_ne nid 0 6 rfl)
          (natBeq_add_ne nid 4 6 rfl))) ?_
    rw [hMem]
    rfl
  have hEnd : ChainStepV2 (entryProgForBody Captured.program 0) (m_b10_t cm nid)
      (.done (.returned ⟨.tuple
        [ .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
        , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
        , .vec
            ⟨some (nid + 0),
              0, .isize⟩ 1 1
        , .boxPtr
            ⟨some (nid + 4),
              0, .isize⟩ (some 2)
        , .boxPtr
            ⟨some (nid + 6),
              0, .isize⟩ (some 2)
        ],
        ⟨cm.allocations ++ [mBuf0_1 nid, mBuf4 nid, mClone6 nid]⟩⟩)) :=
    .base hRet
  have h_41 := ChainStepV2.step (m0_tr_41 cm) hEnd
  have h_40 := ChainStepV2.step (m0_tr_40 cm) h_41
  have h_39 := chainTo_chainStepV2 (m0_tr_39 cm nid) h_40
  have h_38 := ChainStepV2.step (m0_tr_38 cm) h_39
  have h_37 := chainTo_chainStepV2 (m0_tr_37 cm nid) h_38
  have h_36 := ChainStepV2.step (m0_tr_36 cm) h_37
  have h_35 := chainTo_chainStepV2 (m0_tr_35 cm nid) h_36
  have h_34 := ChainStepV2.step (m0_tr_34 cm) h_35
  have h_33 := chainTo_chainStepV2 (m0_tr_33 cm nid) h_34
  have h_32 := ChainStepV2.step (m0_tr_32 cm) h_33
  have h_31 := chainTo_chainStepV2 (m0_tr_31 cm nid) h_32
  have h_30 := ChainStepV2.step (m0_tr_30 cm) h_31
  have h_29 := ChainStepV2.step (m0_tr_29 cm) h_30
  have h_28 := chainTo_chainStepV2 (m0_tr_28 cm nid) h_29
  have h_27 := ChainStepV2.step (m0_tr_27 cm) h_28
  have h_26 := ChainStepV2.step (m0_tr_26 cm) h_27
  have h_25 := chainTo_chainStepV2 (m0_tr_25 cm nid) h_26
  have h_24 := ChainStepV2.step (m0_tr_24 cm) h_25
  have h_23 := ChainStepV2.step (m0_tr_23 cm) h_24
  have h_22 := ChainStepV2.step (m0_tr_22 cm) h_23
  have h_21 := chainTo_chainStepV2 (m0_tr_21 cm nid) h_22
  have h_20 := ChainStepV2.step (m0_tr_20 cm) h_21
  have h_19 := ChainStepV2.step (m0_tr_19 cm) h_20
  have h_18 := chainTo_chainStepV2 (m0_tr_18 cm nid) h_19
  have h_17 := ChainStepV2.step (m0_tr_17 cm) h_18
  have h_16 := chainTo_chainStepV2 (m0_tr_16 cm nid) h_17
  have h_15 := ChainStepV2.step (m0_tr_15 cm) h_16
  have h_14 := ChainStepV2.step (m0_tr_14 cm) h_15
  have h_13 := ChainStepV2.step (m0_tr_13 cm) h_14
  have h_12 := chainTo_chainStepV2 (m0_tr_12 cm nid) h_13
  have h_11 := ChainStepV2.step (m0_tr_11 cm) h_12
  have h_10 := chainTo_chainStepV2 (m0_tr_10 cm nid) h_11
  have h_9 := ChainStepV2.step (m0_tr_9 cm) h_10
  have h_8 := ChainStepV2.step (m0_tr_8 cm) h_9
  have h_7 := chainTo_chainStepV2 (m0_tr_7 cm nid) h_8
  have h_6 := ChainStepV2.step (m0_tr_6 cm) h_7
  have h_5 := chainTo_chainStepV2 (m0_tr_5 cm nid) h_6
  have h_4 := ChainStepV2.step (m0_tr_4 cm) h_5
  have h_3 := ChainStepV2.step (m0_tr_3 cm) h_4
  have h_2 := chainTo_chainStepV2 (m0_tr_2 cm nid) h_3
  have h_1 := ChainStepV2.step (m0_tr_1 cm) h_2
  have h_0 := chainTo_chainStepV2 (m0_tr_0 cm nid) h_1
  exact h_0


private theorem body0_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q ∧
    ∃ (sId bId cId : AllocId),
      (∀ a : Allocation, a ∈ q.callerMem.allocations → a.allocId < sId) ∧
      sId < bId ∧ bId < cId ∧
      BehaviorV2 (entryProgForBody Captured.program 0) q
        (TerminalOut.returned
          ⟨.tuple
            [ .scalar
                ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 2)⟩
            , .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 10)⟩
            , .vec ⟨some sId, 0, .isize⟩ 1 1
            , .boxPtr ⟨some bId, 0, .isize⟩ (some 2)
            , .boxPtr ⟨some cId, 0, .isize⟩ (some 2)
            ],
            ⟨q.callerMem.allocations ++
              [ ⟨sId, 0, .mut, [.init 9 none], true⟩
              , ⟨bId, 0, .mut, [.init 10 none, .init 9 none], true⟩
              , ⟨cId, 0, .mut, [.init 10 none, .init 9 none], true⟩
              ]⟩⟩) := by
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  have hInit : initStateV2 (entryProgForBody Captured.program 0) q =
      .ok (m_b0_0 q.callerMem
        (entryMemoryWithCaller q.callerMem).nextAllocId) := by
    rcases hValid with ⟨_, hArgs, hRefs, hSpans⟩
    have hStatic :
        BodyStaticAdmittedV2 (entryProgForBody Captured.program 0)
          Captured.body_0 = true := by
      unfold BodyStaticAdmittedV2; decide
    have hBase := initStateV2_ok_of (p := (entryProgForBody Captured.program 0))
      (body := Captured.body_0) rfl hStatic ⟨hCM, hArgs, hRefs, hSpans⟩
    have hP0 : (entryProgForBody Captured.program 0).entryDefId = 0 := rfl
    have hArgsEmpty : q.args = [] := by
      cases hQ : q.args with
      | nil => rfl
      | cons _ _ =>
        rw [hQ] at hArgs
        unfold checkArgsMatchV2 at hArgs
        cases hArgs
    rw [hBase, hP0, hArgsEmpty]; rfl
  have hSpec := spec_and_behaviorV2_of_chainStep hInit
    (m0_chain q.callerMem hCM)
  let nid := (entryMemoryWithCaller q.callerMem).nextAllocId
  exact ⟨hSpec.1, nid + 0, nid + 4, nid + 6,
    mem_lt_entryNextAllocId q.callerMem 0,
    Nat.add_lt_add_left (by decide) nid,
    Nat.add_lt_add_left (by decide) nid, hSpec.2⟩


private noncomputable def m1_b0_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 0, 0,
    [.immediate none
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate none], none, none, none⟩],
    cm, ⟨nid + 0, cm.allocations⟩⟩

private noncomputable def m1_b0_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 0, 1,
    [.immediate none
    , .immediate none
    , .dead
    , .dead
    , .dead
    , .immediate none], none, none, none⟩],
    cm, ⟨nid + 0, cm.allocations⟩⟩

private noncomputable def m1_b1_0 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 1, 0,
    [.immediate none
    , .immediate (some (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none))
    , .dead
    , .dead
    , .dead
    , .immediate none], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩⟩

private noncomputable def m1_b1_1 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 1, 1,
    [.immediate none
    , .immediate (some (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none))
    , .immediate none
    , .dead
    , .dead
    , .immediate none], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩⟩

private noncomputable def m1_b1_2 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 1, 2,
    [.immediate none
    , .immediate (some (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none))
    , .immediate none
    , .dead
    , .dead
    , .immediate (some (.ptr ⟨some (nid + 0), 0, .isize⟩))], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩⟩

private noncomputable def m1_b1_3 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 1, 3,
    [.immediate none
    , .immediate (some (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none))
    , .immediate (some (
        .scalar
          ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩))
    , .dead
    , .dead
    , .immediate (some (.ptr ⟨some (nid + 0), 0, .isize⟩))], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩⟩

private noncomputable def m1_b1_6 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 1, 6,
    [.immediate none
    , .immediate (some (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none))
    , .immediate (some (
        .scalar
          ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩))
    , .immediate (some (
        .scalar
          ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩))
    , .immediate none
    , .immediate (some (.ptr ⟨some (nid + 0), 0, .isize⟩))], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩⟩

private noncomputable def m1_b1_7 (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 1, 7,
    [.immediate none
    , .immediate none
    , .immediate (some (
        .scalar
          ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩))
    , .immediate (some (
        .scalar
          ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩))
    , .immediate (some (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none))
    , .immediate (some (.ptr ⟨some (nid + 0), 0, .isize⟩))], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩⟩

private noncomputable def m1_b1_t (cm : CallerMemory) (nid : Nat) :
    State :=
  ⟨[⟨1, 1, 12,
    [.immediate (some (
        .tuple
            [ .scalar ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩
            , .boxPtr
                ⟨some (nid + 0),
                  0, .isize⟩ none
            ]))
    , .dead
    , .dead
    , .dead
    , .dead
    , .immediate (some (.ptr ⟨some (nid + 0), 0, .isize⟩))], none, none, none⟩],
    cm, ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩⟩

private theorem m1_tr_boxNew (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 1)
      (m1_b0_t cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m1_b1_0 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let mUninit : MemoryState := ⟨nid + 1, cm.allocations ++
    [⟨nid + 0, 3, .mut, List.replicate 8 .uninit, true⟩]⟩
  have hFind0 : findAllocation (nid + 0)
      (mUninit).allocations =
      some (⟨nid + 0, 3, .mut, List.replicate 8 .uninit, true⟩) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hWr : writeBytes mUninit ⟨nid + 0, 0⟩ 3
            [.init 52 none
      , .init 18 none
      , .init 0 none
      , .init 0 none
      , .init 0 none
      , .init 0 none
      , .init 0 none
      , .init 0 none] =
      .ok ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩ := by
    rw [writeBytes_ok ⟨nid + 0, 3, .mut, List.replicate 8 .uninit, true⟩
      rfl hFind0 rfl rfl rfl rfl]
    dsimp only
    rw [replaceAllocation_append_nid rfl,
      replaceAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
    rfl
  have hCall : execCoreCallOpWithMem ⟨nid + 0, cm.allocations⟩
      (.boxNew (.int .i64 false))
      [(.int .i64 false, .scalar ⟨.i64, false,
        truncateBits .i64 (BitVec.ofNat 128 4660)⟩)]
      (.box (.int .i64 false)) =
      .ok (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none,
        ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩) :=
    evalBoxNew_u64 rfl rfl hWr
  exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl hCall
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m1_tr_boxAsRef (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 1)
      (m1_b1_1 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m1_b1_2 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩
  have hFind : findAllocation (nid + 0) m0.allocations =
      some (mBox64 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hRef : refValidInMem m0 .shared (.int .i64 false)
      (.ptr ⟨some (nid + 0), 0, .isize⟩) = .ok () := by
    unfold refValidInMem; dsimp only
    rw [ite_bool_false _ ptrGuard_u64]
    rw [layoutOfTyV2_u64]; dsimp only
    rw [hFind]; dsimp only
    have hU0 : (0 : UInt64).toNat = 0 := rfl
    rw [hU0]
    rw [ite_bool_false
      (!(mBox64 nid).live || !isInBounds (mBox64 nid) 0 8 ||
        !isAligned (mBox64 nid) 0 3) rfl]
    rw [ite_bool_false
      (Mutability.beq .shared .mut &&
        !Mutability.beq (mBox64 nid).mutability .mut) rfl]
    unfold mBox64; dsimp only [List.drop, List.take]
    rw [decodeValV2_u64_1234]
  rw [evalStepV2_stmt rfl rfl rfl rfl]
  unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2
    evalOperandToSlotV2 readPlaceV2 evalCastKindV2
  dsimp only [Captured.program, Captured.body_1,
    Trusted.MirSemantics.getElem?, m1_b1_1]
  rw [ite_bool_false (!isSupportedV2LocalTy (.box (.int .i64 false))) rfl]
  rw [ite_bool_false false rfl]
  dsimp only
  rw [ite_bool_false (!(MirTy.ref .shared (.int .i64 false)).beq
    (.ref .shared (.int .i64 false))) rfl]
  rw [ite_bool_false (!MirTy.beq (.int .i64 false) (.int .i64 false)) rfl]
  rw [ite_bool_false (isUnsizedTy (.int .i64 false)) rfl]
  dsimp only
  rw [hRef]
  dsimp only [writePlaceDestV2, checkValV2, Trusted.MirSemantics.getElem?,
    Trusted.MirSemantics.setElem?]
  rfl

private theorem m1_tr_deref (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 1)
      (m1_b1_2 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m1_b1_3 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩
  have hFind : findAllocation (nid + 0)
      (m0).allocations = some (mBox64 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hLoad : loadIndirectV2 m0 (.int .i64 false) ⟨nid + 0, 0⟩ =
      .ok (some (.scalar ⟨.i64, false,
        truncateBits .i64 (BitVec.ofNat 128 4660)⟩)) :=
    loadIndirectV2_ok layoutOfTyV2_u64
      (readBytes_ok rfl hFind rfl rfl rfl) decodeValV2_u64_1234
  exact evalStepV2_assign_copy_deref rfl rfl rfl rfl rfl (Or.inl rfl) rfl
    layoutOfTyV2_u64 rfl rfl hLoad (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m1_tr_retag (cm : CallerMemory) :
    evalStepV2 (entryProgForBody Captured.program 1)
      (m1_b1_6 cm (entryMemoryWithCaller cm).nextAllocId) =
      .step (m1_b1_7 cm (entryMemoryWithCaller cm).nextAllocId) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let m0 : MemoryState := ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩
  have hFind : findAllocation (nid + 0)
      (m0).allocations = some (mBox64 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hBuf : ownedHeapBufValidInMem m0 true (.int .i64 false)
      ⟨some (nid + 0), 0, .isize⟩ 1 1 = .ok () :=
    ownedBuf_int_ok (mBox64 nid) layoutOfTyV2_u64
      rfl rfl rfl rfl hFind rfl rfl rfl rfl rfl
  have hRefs : refsValidInMem m0 (.box (.int .i64 false))
      (.boxPtr ⟨some (nid + 0), 0, .isize⟩ none) = true :=
    refsValidInMem_box_u64_true hBuf
  exact evalStepV2_assign_useRetag_imm rfl rfl rfl rfl rfl rfl rfl rfl hRefs
    (writePlaceV2_imm_ok rfl rfl rfl)

private theorem m1_chain (cm : CallerMemory)
    (hCM : validCallerMemory cm = true) :
    ChainStepV2 (entryProgForBody Captured.program 1)
      (m1_b0_0 cm (entryMemoryWithCaller cm).nextAllocId)
      (.done (.returned ⟨.tuple
          [ .scalar ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩
          , .boxPtr
              ⟨some ((entryMemoryWithCaller cm).nextAllocId + 0),
                0, .isize⟩ none
          ],
        ⟨cm.allocations ++
          [mBox64 (entryMemoryWithCaller cm).nextAllocId]⟩⟩)) := by
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let mEnd : MemoryState := ⟨nid + 1, cm.allocations ++ [mBox64 nid]⟩
  have hMem : ∀ locals : List LocalSlot, frameLocalAllocIds locals = [] →
      extractReturnMemoryV2 cm mEnd locals =
        ⟨cm.allocations ++ [mBox64 nid]⟩ := by
    intro locals hL
    have h1 : extractReturnMemoryV2 cm mEnd locals =
        ⟨cm.allocations ++ calleeLiveAllocations (allocIdsOf cm.allocations)
          (frameLocalAllocIds locals) [mBox64 nid]⟩ :=
      extractReturnMemoryV2_append hCM
    rw [h1, hL, calleeLive_cons_keep (a := mBox64 nid) (fIds := []) rfl
      (natNotElem_callerIds cm 0) rfl]
    rfl
  have hFind : findAllocation (nid + 0)
      (mEnd).allocations = some (mBox64 nid) := by
    rw [findAllocation_append_nid 0]
    rw [findAllocation_cons_eq (natBeq_add_eq nid 0 0 rfl)]
  have hBuf : ownedHeapBufValidInMem mEnd true (.int .i64 false)
      ⟨some (nid + 0), 0, .isize⟩ 1 1 = .ok () :=
    ownedBuf_int_ok (mBox64 nid) layoutOfTyV2_u64
      rfl rfl rfl rfl hFind rfl rfl rfl rfl rfl
  have hRefs : refsValidInMem mEnd
      (.tuple [.int .i64 false, .box (.int .i64 false)])
      (.tuple
        [ .scalar ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩
        , .boxPtr
            ⟨some (nid + 0),
              0, .isize⟩ none
        ]) = true := by
    unfold refsValidInMem
    exact refsValidInMemList_cons mEnd _ _ _ _ rfl
      (refsValidInMemList_cons mEnd _ _ _ _ (refsValidInMem_box_u64_true hBuf)
        (refsValidInMemList_nil mEnd))
  have hRet : evalStepV2 (entryProgForBody Captured.program 1)
      (m1_b1_t cm nid) =
      .done (.returned ⟨.tuple
        [ .scalar ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 4660)⟩
        , .boxPtr
            ⟨some (nid + 0),
              0, .isize⟩ none
        ],
        ⟨cm.allocations ++ [mBox64 nid]⟩⟩) := by
    dsimp only [m1_b1_t]
    refine Eq.trans
      (evalStepV2_return_imm rfl rfl rfl rfl rfl rfl rfl rfl hRefs rfl) ?_
    rw [hMem]
    rfl
  have c7t : ChainTo (entryProgForBody Captured.program 1)
      (m1_b1_7 cm nid) (m1_b1_t cm nid) :=
    ChainTo.step rfl (ChainTo.step rfl (ChainTo.step rfl (ChainTo.step rfl
      (ChainTo.step rfl (ChainTo.refl _)))))
  have c36 : ChainTo (entryProgForBody Captured.program 1)
      (m1_b1_3 cm nid) (m1_b1_6 cm nid) :=
    ChainTo.step rfl (ChainTo.step rfl (ChainTo.step rfl (ChainTo.refl _)))
  have c01 : ChainTo (entryProgForBody Captured.program 1)
      (m1_b1_0 cm nid) (m1_b1_1 cm nid) :=
    ChainTo.step rfl (ChainTo.refl _)
  have c0t : ChainTo (entryProgForBody Captured.program 1)
      (m1_b0_0 cm nid) (m1_b0_t cm nid) :=
    ChainTo.step rfl (ChainTo.refl _)
  exact chainTo_chainStepV2 c0t
    (ChainStepV2.step (m1_tr_boxNew cm)
      (chainTo_chainStepV2 c01
        (ChainStepV2.step (m1_tr_boxAsRef cm)
          (ChainStepV2.step (m1_tr_deref cm)
            (chainTo_chainStepV2 c36
              (ChainStepV2.step (m1_tr_retag cm)
                (chainTo_chainStepV2 c7t (.base hRet))))))))

private theorem body1_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q ∧
    ∃ (bId : AllocId),
      (∀ a : Allocation, a ∈ q.callerMem.allocations → a.allocId < bId) ∧
      BehaviorV2 (entryProgForBody Captured.program 1) q
        (TerminalOut.returned
          ⟨.tuple
            [ .scalar
                ⟨.i64, false, truncateBits .i64 (BitVec.ofNat 128 0x1234)⟩
            , .boxPtr ⟨some bId, 0, .isize⟩ none
            ],
            ⟨q.callerMem.allocations ++
              [ ⟨bId, 3, .mut,
                  [ .init 0x34 none, .init 0x12 none, .init 0 none
                  , .init 0 none, .init 0 none, .init 0 none
                  , .init 0 none, .init 0 none ], true⟩ ]⟩⟩) := by
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  have hInit : initStateV2 (entryProgForBody Captured.program 1) q =
      .ok (m1_b0_0 q.callerMem
        (entryMemoryWithCaller q.callerMem).nextAllocId) := by
    rcases hValid with ⟨_, hArgs, hRefs, hSpans⟩
    have hStatic :
        BodyStaticAdmittedV2 (entryProgForBody Captured.program 1)
          Captured.body_1 = true := by
      unfold BodyStaticAdmittedV2; decide
    have hBase := initStateV2_ok_of (p := (entryProgForBody Captured.program 1))
      (body := Captured.body_1) rfl hStatic ⟨hCM, hArgs, hRefs, hSpans⟩
    have hP1 : (entryProgForBody Captured.program 1).entryDefId = 1 := rfl
    have hArgsEmpty : q.args = [] := by
      cases hQ : q.args with
      | nil => rfl
      | cons _ _ =>
        rw [hQ] at hArgs
        unfold checkArgsMatchV2 at hArgs
        cases hArgs
    rw [hBase, hP1, hArgsEmpty]; rfl
  have hSpec := spec_and_behaviorV2_of_chainStep hInit
    (m1_chain q.callerMem hCM)
  let nid := (entryMemoryWithCaller q.callerMem).nextAllocId
  exact ⟨hSpec.1, nid + 0, mem_lt_entryNextAllocId q.callerMem 0, hSpec.2⟩



private theorem body2_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q)
    (hSafe : Spec.vecWithCapSafety q) :
    WellFormedV2 (entryProgForBody Captured.program 2) q := by
  rcases hValid with ⟨hCM, hArgs, hRefs, hSpans⟩
  cases hQ : q.args with
  | nil =>
    unfold Spec.vecWithCapSafety at hSafe
    rw [hQ] at hSafe
    exact False.elim hSafe
  | cons a0 rest =>
    cases rest with
    | cons _ _ =>
      rw [hQ] at hArgs
      unfold checkArgsMatchV2 at hArgs
      dsimp only [Captured.body_2, List.drop, List.take] at hArgs
      cases ((Bool.and_eq_true _ _).mp hArgs).2
    | nil =>
      cases a0 with
      | scalar capSv =>
        unfold Spec.vecWithCapSafety at hSafe
        rw [hQ] at hSafe
        dsimp only at hSafe
        have hStatic :
            BodyStaticAdmittedV2 (entryProgForBody Captured.program 2)
              Captured.body_2 = true := by
          unfold BodyStaticAdmittedV2; decide
        have hInit := initStateV2_ok_of
          (p := (entryProgForBody Captured.program 2))
          (body := Captured.body_2) rfl hStatic ⟨hCM, hArgs, hRefs, hSpans⟩
        rw [hQ] at hInit
        have hWST : capSv.width = .isize ∧ capSv.signed = false ∧
            truncateBits .isize capSv.bits = capSv.bits := by
          cases hCap : capSv with
          | mk w s b =>
            have h1 : checkVal (.scalar ⟨w, s, b⟩)
                (.int .isize false) = true := by
              rw [hQ, hCap] at hArgs
              change checkVal (.scalar ⟨w, s, b⟩) (.int .isize false) &&
                decide (true = true) = true at hArgs
              exact ((Bool.and_eq_true _ _).mp hArgs).1
            unfold checkVal Val.ty? ScalarVal.wf at h1
            dsimp only at h1
            cases hWf : (truncateBits w b == b) with
            | false => rw [hWf] at h1; cases h1
            | true =>
              rw [hWf] at h1
              cases w with
              | i8 | i16 | i32 | i64 | i128 => cases h1
              | isize =>
                cases s with
                | true => cases h1
                | false => exact ⟨rfl, rfl, beq_iff_eq.mp hWf⟩
        rcases hWST with ⟨hW, hS, hTrunc⟩
        have hCapBits : capSv.bits.toNat < isizeMaxBytes := hSafe
        have hLt64 : capSv.bits.toNat < 2 ^ 64 :=
          Nat.lt_trans hCapBits (by decide)
        have hU64 : (UInt64.ofNat capSv.bits.toNat).toNat =
            capSv.bits.toNat := by
          change capSv.bits.toNat % 2 ^ 64 = capSv.bits.toNat
          exact Nat.mod_eq_of_lt hLt64
        have hChkCap :
            checkValV2 (.scalar capSv) (.int .isize false) = true := by
          unfold checkValV2 checkVal Val.ty? ScalarVal.wf
          dsimp only
          rw [hW, hS]
          have hWfEq :
              (truncateBits .isize capSv.bits == capSv.bits) = true :=
            beq_iff_eq.mpr hTrunc
          rw [hWfEq]
          rfl
        let nid := (entryMemoryWithCaller q.callerMem).nextAllocId
        let m0 := entryMemoryWithCaller q.callerMem
        let s0 : State :=
          ⟨[⟨2, 0, 0,
            [.immediate none, .immediate (some (.scalar capSv)), .dead], none, none, none⟩],
            q.callerMem, m0⟩
        let s1 : State :=
          ⟨[⟨2, 0, 1,
            [.immediate none, .immediate (some (.scalar capSv)),
              .immediate none], none, none, none⟩],
            q.callerMem, m0⟩
        let s2 : State :=
          ⟨[⟨2, 0, 2,
            [.immediate none, .immediate (some (.scalar capSv)),
              .immediate (some (.scalar capSv))], none, none, none⟩],
            q.callerMem, m0⟩
        have hInit0 :
            initStateV2 (entryProgForBody Captured.program 2) q = .ok s0 := by
          rw [hInit]; rfl
        have hs01 : evalStepV2 (entryProgForBody Captured.program 2)
            s0 = .step s1 := rfl
        have hs12 : evalStepV2 (entryProgForBody Captured.program 2)
            s1 = .step s2 := by
          rw [evalStepV2_stmt (stmt :=
            .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))) rfl rfl rfl rfl]
          unfold evalStatementV2 resolvePlaceDestV2 evalRvalueV2
            evalOperandToSlotV2 readPlaceV2
          dsimp only [Captured.body_2, placeStaticTyV2,
            Trusted.MirSemantics.getElem?]
          rw [ite_bool_false
            (!isSupportedV2LocalTy (.int .isize false)) rfl]
          rw [ite_bool_false false rfl]; dsimp only
          rw [ite_bool_false
            (!MirTy.beq (.int .isize false) (.int .isize false)) rfl]
          dsimp only
          rw [writePlaceDestV2_imm_ok hChkCap rfl rfl]; rfl
        have hs02 : ChainTo (entryProgForBody Captured.program 2) s0 s2 :=
          ChainTo.step hs01 (ChainTo.step hs12 (ChainTo.refl _))
        have hEvalArgs : evalArgOperandsV2 Captured.body_2.locals
            [.immediate none, .immediate (some (.scalar capSv)),
              .immediate (some (.scalar capSv))] m0
            [.move ⟨2, []⟩] =
            .ok ([(.int .isize false, .scalar capSv)],
              [.immediate none, .immediate (some (.scalar capSv)),
                .immediate none], m0) := by
          unfold evalArgOperandsV2 evalOperandToSlotV2 readPlaceV2
          dsimp only [Captured.body_2, Trusted.MirSemantics.getElem?]
          rw [ite_bool_false
            (!isSupportedV2LocalTy (.int .isize false)) rfl]
          rfl
        cases hZero : Nat.beq capSv.bits.toNat 0 with
        | true =>
          have hCap0 : capSv.bits.toNat = 0 := Nat.eq_of_beq_eq_true hZero
          let resVec : Val := .vec ⟨none, 1, .isize⟩
            (UInt64.ofNat capSv.bits.toNat) 0
          have hCall : execCoreCallOpWithMem m0
              (.vecWithCapacity (.int .i8 false))
              [(.int .isize false, .scalar capSv)]
              (.vec (.int .i8 false)) = .ok (resVec, m0) := by
            refine execCoreCallOpWithMem_eq_allocOutcome ?_
            unfold execAllocCoreCallOutcome evalVecWithCapacityOutcome
            try dsimp only
            rw [ite_bool_false (!MirTy.beq (.vec (.int .i8 false))
                (.vec (.int .i8 false))) rfl]
            try dsimp only
            rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false))
              rfl]
            rw [layoutOfTyV2_u8]; dsimp only
            rw [hU64, Nat.mul_one]
            rw [ite_bool_false (!Nat.blt capSv.bits.toNat isizeMaxBytes)
              (by rw [Nat.blt_eq.mpr hCapBits]; rfl)]
            rw [ite_bool_true (Nat.beq capSv.bits.toNat 0) hZero]
            rfl
          have hChkVec : checkValV2 resVec (.vec (.int .i8 false)) = true :=
            rfl
          have hStepCall : evalStepV2 (entryProgForBody Captured.program 2)
              ⟨[⟨2, 0, 2,
                [.immediate none, .immediate (some (.scalar capSv)),
                  .immediate (some (.scalar capSv))], none, none, none⟩],
                q.callerMem, m0⟩ =
              .step ⟨[⟨2, 1, 0,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .immediate none], none, none, none⟩],
                q.callerMem, m0⟩ := by
            exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl hEvalArgs hCall
              (writePlaceV2_imm_ok hChkVec rfl rfl)
          have hStepDead : ChainTo (entryProgForBody Captured.program 2)
              ⟨[⟨2, 1, 0,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .immediate none], none, none, none⟩],
                q.callerMem, m0⟩
              ⟨[⟨2, 1, 1,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .dead], none, none, none⟩],
                q.callerMem, m0⟩ :=
            ChainTo.step rfl (ChainTo.refl _)
          have hBuf : ownedHeapBufValidInMem m0 true (.int .i8 false)
              ⟨none, 1, .isize⟩ (UInt64.ofNat capSv.bits.toNat) 0 =
              .ok () := by
            have hCapU0 : UInt64.ofNat capSv.bits.toNat = 0 := by
              rw [hCap0]; rfl
            rw [hCapU0]
            exact ownedBuf_zero_ok layoutOfTyV2_u8 rfl rfl rfl
          have hRefsRet : refsValidInMem m0 (.vec (.int .i8 false)) resVec =
              true :=
            refsValidInMem_vec_true hBuf
          have hRet : evalStepV2 (entryProgForBody Captured.program 2)
              ⟨[⟨2, 1, 1,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .dead], none, none, none⟩],
                q.callerMem, m0⟩ =
              .done (.returned
                ⟨resVec, extractReturnMemoryV2 q.callerMem m0
                  [.immediate (some resVec), .immediate (some (.scalar capSv)),
                    .dead]⟩) :=
            evalStepV2_return_imm rfl rfl rfl rfl rfl rfl rfl rfl hRefsRet rfl
          have hFull := chainTo_chainStepV2 hs02
            (ChainStepV2.step hStepCall
              (chainTo_chainStepV2 hStepDead (.base hRet)))
          exact (spec_and_behaviorV2_of_chainStep hInit0 hFull).1
        | false =>
          let n := capSv.bits.toNat
          let newA : Allocation :=
            ⟨nid, 0, .mut, List.replicate n .uninit, true⟩
          let m1 : MemoryState :=
            ⟨nid + 1, q.callerMem.allocations ++ [newA]⟩
          let resVec : Val := .vec ⟨some nid, 0, .isize⟩ (UInt64.ofNat n) 0
          have hCall : execCoreCallOpWithMem m0
              (.vecWithCapacity (.int .i8 false))
              [(.int .isize false, .scalar capSv)]
              (.vec (.int .i8 false)) = .ok (resVec, m1) := by
            refine execCoreCallOpWithMem_eq_allocOutcome ?_
            unfold execAllocCoreCallOutcome evalVecWithCapacityOutcome
            try dsimp only
            rw [ite_bool_false (!MirTy.beq (.vec (.int .i8 false))
                (.vec (.int .i8 false))) rfl]
            try dsimp only
            rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false))
              rfl]
            rw [layoutOfTyV2_u8]; dsimp only
            rw [hU64, Nat.mul_one]
            rw [ite_bool_false (!Nat.blt n isizeMaxBytes)
              (by rw [Nat.blt_eq.mpr hCapBits]; rfl)]
            rw [ite_bool_false (Nat.beq n 0) hZero]
            rfl
          have hChkVec : checkValV2 resVec (.vec (.int .i8 false)) = true :=
            rfl
          have hStepCall : evalStepV2 (entryProgForBody Captured.program 2)
              ⟨[⟨2, 0, 2,
                [.immediate none, .immediate (some (.scalar capSv)),
                  .immediate (some (.scalar capSv))], none, none, none⟩],
                q.callerMem, m0⟩ =
              .step ⟨[⟨2, 1, 0,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .immediate none], none, none, none⟩],
                q.callerMem, m1⟩ := by
            exact evalStepV2_coreCall rfl rfl rfl rfl rfl rfl hEvalArgs hCall
              (writePlaceV2_imm_ok hChkVec rfl rfl)
          have hStepDead : ChainTo (entryProgForBody Captured.program 2)
              ⟨[⟨2, 1, 0,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .immediate none], none, none, none⟩],
                q.callerMem, m1⟩
              ⟨[⟨2, 1, 1,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .dead], none, none, none⟩],
                q.callerMem, m1⟩ :=
            ChainTo.step rfl (ChainTo.refl _)
          have hFindA : findAllocation nid m1.allocations = some newA := by
            rw [findAllocation_append_nid0]
            rw [findAllocation_cons_eq (Nat.beq_refl nid)]
          have hLenCap : Nat.ble 0 (UInt64.ofNat n).toNat = true := rfl
          have hBound : Nat.blt ((UInt64.ofNat n).toNat * 1) isizeMaxBytes =
              true := by
            rw [hU64, Nat.mul_one]
            exact Nat.blt_eq.mpr hCapBits
          have hCapPos : Nat.beq (UInt64.ofNat n).toNat 0 = false := by
            rw [hU64]; exact hZero
          have hInB :
              isInBounds newA 0 ((UInt64.ofNat n).toNat * 1) = true := by
            rw [hU64, Nat.mul_one]
            exact isInBounds_zero_replicate nid 0 .mut true n
          have hLenEq : Nat.beq newA.bytes.length
              ((UInt64.ofNat n).toNat * 1) = true := by
            show Nat.beq (List.replicate n AllocByte.uninit).length
              ((UInt64.ofNat n).toNat * 1) = true
            rw [List.length_replicate, hU64, Nat.mul_one]
            exact Nat.beq_refl n
          have hBuf : ownedHeapBufValidInMem m1 true (.int .i8 false)
              ⟨some nid, 0, .isize⟩ (UInt64.ofNat n) 0 = .ok () :=
            ownedBuf_int_ok newA layoutOfTyV2_u8
              rfl hLenCap hBound hCapPos hFindA rfl hInB
              (isAligned_zero newA) rfl rfl hLenEq
          have hRefsRet : refsValidInMem m1 (.vec (.int .i8 false)) resVec =
              true :=
            refsValidInMem_vec_true hBuf
          have hRet : evalStepV2 (entryProgForBody Captured.program 2)
              ⟨[⟨2, 1, 1,
                [.immediate (some resVec), .immediate (some (.scalar capSv)),
                  .dead], none, none, none⟩],
                q.callerMem, m1⟩ =
              .done (.returned
                ⟨resVec, extractReturnMemoryV2 q.callerMem m1
                  [.immediate (some resVec), .immediate (some (.scalar capSv)),
                    .dead]⟩) :=
            evalStepV2_return_imm rfl rfl rfl rfl rfl rfl rfl rfl hRefsRet
              (spansDisjoint_vec_u8 resVec)
          have hFull := chainTo_chainStepV2 hs02
            (ChainStepV2.step hStepCall
              (chainTo_chainStepV2 hStepDead (.base hRet)))
          exact (spec_and_behaviorV2_of_chainStep hInit0 hFull).1
      | _ =>
        unfold Spec.vecWithCapSafety at hSafe
        rw [hQ] at hSafe
        exact False.elim hSafe

private theorem evalStepV2_assign_boxAsRef_slice_u8 {p : Program}
    {frame : FrameState} {mem : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {dst src : LocalId}
    {pv : PtrVal} {len : UInt64} {locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.cast .boxAsRef (.copy ⟨src, []⟩)
        (.ref .shared (.slice (.int .i8 false))))))
    (hDstTy : placeStaticTyV2 body.locals ⟨dst, []⟩ =
      some (.ref .shared (.slice (.int .i8 false))))
    (hSrcTy : Trusted.MirSemantics.getElem? body.locals src =
      some (.box (.slice (.int .i8 false))))
    (hSlot : Trusted.MirSemantics.getElem? frame.locals src =
      some (.immediate (some (.boxPtr pv (some len)))))
    (hRef : refValidInMem mem .shared (.slice (.int .i8 false))
      (.slicePtr pv len) = .ok ())
    (hWp : writePlaceV2 body.locals frame.locals mem ⟨dst, []⟩
      (.ref .shared (.slice (.int .i8 false))) (.slicePtr pv len) =
      .ok (locals2, mem)) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hDstTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalOperandToSlotV2 readPlaceV2; dsimp only
  rw [hSrcTy, hSlot]; dsimp only
  rw [ite_bool_false
    (!isSupportedV2LocalTy (.box (.slice (.int .i8 false)))) rfl]
  rw [ite_bool_false false rfl]
  unfold evalCastKindV2; dsimp only
  rw [ite_bool_false (!(MirTy.ref .shared (.slice (.int .i8 false))).beq
    (.ref .shared (.slice (.int .i8 false)))) rfl]
  rw [ite_bool_false
    (!MirTy.beq (.slice (.int .i8 false)) (.slice (.int .i8 false))) rfl]
  rw [hRef]; dsimp only; rw [hWp]; rfl

private theorem execCoreCallOpWithMem_sliceLen_u8 {m : MemoryState}
    {p : PtrVal} {len : UInt64}
    (hRef : refValidInMem m .shared (.slice (.int .i8 false))
      (.slicePtr p len) = .ok ()) :
    execCoreCallOpWithMem m .sliceLen
      [(.ref .shared (.slice (.int .i8 false)), .slicePtr p len)]
      (.int .isize false) =
      .ok (.scalar
        ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 len.toNat)⟩,
        m) := by
  unfold execCoreCallOpWithMem execCoreCallOpWithMemOutcome
    execAllocCoreCallOutcome execAllocCoreCallInfallible; dsimp only
  unfold execCoreCallWithMemOutcome; dsimp only
  unfold execCoreCallOp; dsimp only
  rw [ite_bool_false (!MirTy.beq (.int .isize false) (.int .isize false)) rfl]
  rw [hRef]
  rfl

private theorem boxPointee_slice_u8_to_refValid {m : MemoryState}
    {p : PtrVal} {len : UInt64}
    (hBuf : heapBufValidInMem m false (.int .i8 false) p len len = .ok ()) :
    refValidInMem m .shared (.slice (.int .i8 false))
      (.slicePtr p len) = .ok () := by
  unfold heapBufValidInMem at hBuf
  cases hW : IntWidth.beq p.width .isize with
  | false => rw [hW] at hBuf; cases hBuf
  | true =>
    rw [hW] at hBuf
    rw [layoutOfTyV2_u8] at hBuf
    dsimp only at hBuf
    rw [ite_bool_false (!Nat.ble len.toNat len.toNat)
      (by rw [Nat.ble_eq_true_of_le (Nat.le_refl _)]; rfl)] at hBuf
    rw [ite_bool_false (Nat.beq 1 0) rfl] at hBuf
    cases hBound : Nat.blt (len.toNat * 1) isizeMaxBytes with
    | false => rw [hBound] at hBuf; cases hBuf
    | true =>
      rw [hBound] at hBuf
      cases hZ : Nat.beq len.toNat 0 with
      | true =>
        rw [hZ] at hBuf
        have hLen0 : len.toNat = 0 := Nat.eq_of_beq_eq_true hZ
        unfold zeroCapPtrValidInMem at hBuf
        unfold refValidInMem sliceFromRawPartsCheck sliceRefRawCheck
        dsimp only [intLayout]
        rw [ite_bool_false _ sliceGuard_u8, layoutOfTyV2_u8]; dsimp only
        rw [ite_bool_false (!Nat.blt (len.toNat * 1) isizeMaxBytes)
          (by rw [hBound]; rfl)]
        cases hAid : p.allocId with
        | none =>
          rw [hAid] at hBuf
          dsimp only at hBuf
          cases hOff : (Nat.beq p.offsetBytes.toNat 0 ||
              !Nat.beq (Nat.mod p.offsetBytes.toNat (Nat.pow 2 0)) 0) with
          | true => rw [hOff] at hBuf; cases hBuf
          | false =>
            dsimp only
            cases hOff0 : Nat.beq p.offsetBytes.toNat 0 with
            | true => rw [hOff0] at hOff; cases hOff
            | false =>
              cases hMod : Nat.beq (Nat.mod p.offsetBytes.toNat 1) 0 with
              | false =>
                have hM : Nat.beq
                    (Nat.mod p.offsetBytes.toNat (Nat.pow 2 0)) 0 =
                    false := hMod
                rw [hOff0, hM] at hOff; cases hOff
              | true =>
                rw [hLen0, Nat.zero_mul]
                rw [ite_bool_false (false || Nat.blt 0 0) rfl]
                rw [ite_bool_false (!true) rfl]
        | some aid =>
          rw [hAid] at hBuf
          dsimp only at hBuf
          cases hFind : findAllocation aid m.allocations with
          | none => rw [hFind] at hBuf; cases hBuf
          | some a =>
            rw [hFind] at hBuf
            dsimp only at hBuf
            cases hChk : (!a.live || !isInBounds a p.offsetBytes.toNat 0 ||
                !isAligned a p.offsetBytes.toNat 0) with
            | true => rw [hChk] at hBuf; cases hBuf
            | false =>
              dsimp only
              rw [hLen0, Nat.zero_mul]
              rw [hFind]; dsimp only
              rw [ite_bool_false
                (!a.live || !isInBounds a p.offsetBytes.toNat 0 ||
                  !isAligned a p.offsetBytes.toNat 0) hChk]
              rw [ite_bool_false
                (Mutability.beq .shared .mut &&
                  !Mutability.beq a.mutability .mut) rfl]
              dsimp only
              rw [ite_bool_false
                (!isSliceAllInit ((a.bytes.drop p.offsetBytes.toNat).take 0))
                (by rw [List.take_zero]; rfl)]
      | false =>
        rw [hZ] at hBuf
        cases hAid : p.allocId with
        | none => rw [hAid] at hBuf; cases hBuf
        | some aid =>
          rw [hAid] at hBuf
          dsimp only at hBuf
          cases hFind : findAllocation aid m.allocations with
          | none => rw [hFind] at hBuf; cases hBuf
          | some a =>
            rw [hFind] at hBuf
            dsimp only at hBuf
            cases hChk : (!a.live ||
                !isInBounds a p.offsetBytes.toNat (len.toNat * 1) ||
                !isAligned a p.offsetBytes.toNat 0) with
            | true => rw [hChk] at hBuf; cases hBuf
            | false =>
              rw [hChk] at hBuf
              rw [ite_bool_false (false && !Mutability.beq a.mutability .mut)
                rfl] at hBuf
              cases hInit : isSliceAllInit
                  ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * 1)) with
              | false => rw [hInit] at hBuf; cases hBuf
              | true =>
                unfold refValidInMem sliceFromRawPartsCheck sliceRefRawCheck
                dsimp only [intLayout]
                rw [ite_bool_false _ sliceGuard_u8, layoutOfTyV2_u8]; dsimp only
                rw [ite_bool_false (!Nat.blt (len.toNat * 1) isizeMaxBytes)
                  (by rw [hBound]; rfl)]
                rw [hAid]; dsimp only; rw [hFind]; dsimp only
                rw [ite_bool_false
                  (!a.live ||
                    !isInBounds a p.offsetBytes.toNat (len.toNat * 1) ||
                    !isAligned a p.offsetBytes.toNat 0) hChk]
                rw [ite_bool_false
                  (Mutability.beq .shared .mut &&
                    !Mutability.beq a.mutability .mut) rfl]
                dsimp only
                rw [ite_bool_false
                  (!isSliceAllInit
                    ((a.bytes.drop p.offsetBytes.toNat).take (len.toNat * 1)))
                  (by rw [hInit]; rfl)]

private theorem decodeValV2_box_slice_inv {endian : TargetEndian}
    {elem : MirTy} {bs : List AllocByte} {dv : Val}
    (h : decodeValV2 endian (.box (.slice elem)) bs = .ok (some dv)) :
    ∃ (p : PtrVal) (len : UInt64), dv = .boxPtr p (some len) := by
  delta decodeValV2 at h; dsimp only at h; delta decodeValV2._f at h
  dsimp only at h
  rw [ite_bool_true (isUnsizedTy (.slice elem)) rfl] at h
  cases hLen : !bs.length.beq 16 with
  | true => rw [hLen] at h; cases h
  | false =>
    rw [hLen] at h
    cases hP : initBytes? (List.take 8 bs) with
    | none => rw [hP] at h; cases h
    | some pRaw =>
      rw [hP] at h
      cases hProv : readPtrProv? (List.take 8 bs) with
      | none => rw [hProv] at h; cases h
      | some prov =>
        rw [hProv] at h
        cases hL : initBytes? (List.drop 8 bs) with
        | none => rw [hL] at h; cases h
        | some lRaw =>
          rw [hL] at h
          injection h with hSome
          injection hSome with hDv
          exact ⟨_, _, hDv.symm⟩

private theorem boxSliceRef_ok_elim {m : MemoryState} {bPtr : PtrVal}
    (hRefB : refValidInMem m .shared
      (.box (.slice (.int .i8 false))) (.ptr bPtr) = .ok ()) :
    ∃ (aid : AllocId) (bOff : UInt64) (boxP : PtrVal) (boxLen : UInt64),
      bPtr = ⟨some aid, bOff, bPtr.width⟩ ∧
      boxP.width = .isize ∧
      loadIndirectV2 m (.box (.slice (.int .i8 false))) ⟨aid, bOff.toNat⟩ =
        .ok (some (.boxPtr boxP (some boxLen))) ∧
      readBoxFromRef m false (.slice (.int .i8 false)) bPtr =
        .ok ⟨.slice (.int .i8 false), boxP, some boxLen⟩ ∧
      refValidInMem m .shared (.slice (.int .i8 false))
        (.slicePtr boxP boxLen) = .ok () := by
  have hRefOrig := hRefB
  cases hBP : bPtr with
  | mk bAid bOff bW =>
    rw [hBP] at hRefB
    unfold refValidInMem at hRefB
    rw [layoutOfTyV2_box_slice_u8] at hRefB
    dsimp only at hRefB
    cases bAid with
    | none =>
      cases hZ : bOff.toNat.beq 0 <;> (rw [hZ] at hRefB; cases hRefB)
    | some aid =>
      dsimp only at hRefB
      cases hFind : findAllocation aid m.allocations with
      | none => rw [hFind] at hRefB; cases hRefB
      | some a =>
        rw [hFind] at hRefB
        dsimp only at hRefB
        cases hLive : a.live with
        | false => rw [hLive] at hRefB; cases hRefB
        | true =>
          cases hInB : isInBounds a bOff.toNat 16 with
          | false => rw [hLive, hInB] at hRefB; cases hRefB
          | true =>
            cases hAlign : isAligned a bOff.toNat 3 with
            | false => rw [hLive, hInB, hAlign] at hRefB; cases hRefB
            | true =>
              have hChk : (!a.live || !isInBounds a bOff.toNat 16 ||
                  !isAligned a bOff.toNat 3) = false := by
                rw [hLive, hInB, hAlign]; rfl
              rw [hChk] at hRefB
              rw [ite_bool_false false rfl] at hRefB
              rw [ite_bool_false
                (Mutability.beq .shared .mut &&
                  !Mutability.beq a.mutability .mut)
                rfl] at hRefB
              cases hDec : decodeValV2 profileV2TargetEndian
                  (.box (.slice (.int .i8 false)))
                  ((a.bytes.drop bOff.toNat).take 16) with
              | error k => rw [hDec] at hRefB; cases hDec' : hRefB
              | ok optV =>
                cases optV with
                | none => rw [hDec] at hRefB; cases hRefB
                | some dv =>
                  let ⟨boxP, boxLen, hDv⟩ := decodeValV2_box_slice_inv hDec
                  rw [hDv] at hDec
                  rw [hDec] at hRefB
                  dsimp only at hRefB
                  have hMutF : Mutability.beq .shared .mut = false := rfl
                  rw [hMutF] at hRefB
                  rw [ite_bool_false _ ptrGuard_boxSlice] at hRefB
                  have hBoxPW : boxP.width = .isize := by
                    have hB := heap_of_owned (m := m) (isMut := false)
                      (elem := .int .i8 false) (p := boxP) (cap := boxLen)
                      (len := boxLen) hRefB
                    unfold heapBufValidInMem at hB
                    dsimp only at hB
                    cases boxP with
                    | mk pAid pOff pW =>
                      cases pW with
                      | i8 | i16 | i32 | i64 | i128 => cases hB
                      | isize => rfl
                  have hLoad : loadIndirectV2 m
                      (.box (.slice (.int .i8 false)))
                      ⟨aid, bOff.toNat⟩ =
                      .ok (some (.boxPtr boxP (some boxLen))) := by
                    unfold loadIndirectV2 readBytes
                    rw [layoutOfTyV2_box_slice_u8]; dsimp only
                    rw [hFind]; dsimp only
                    rw [ite_bool_false
                      (!a.live || !isInBounds a bOff.toNat 16 ||
                        !isAligned a bOff.toNat 3) hChk]
                    exact hDec
                  have hReadBox : readBoxFromRef m false
                      (.slice (.int .i8 false)) ⟨some aid, bOff, bW⟩ =
                      .ok ⟨.slice (.int .i8 false), boxP, some boxLen⟩ := by
                    unfold readBoxFromRef boxValidInMem
                    dsimp only
                    rw [ite_bool_false false rfl]
                    rw [hBP] at hRefOrig
                    rw [hRefOrig]; dsimp only
                    rw [hLoad]; dsimp only
                    rw [ite_bool_false
                      (!isSupportedPointeeTy (.int .i8 false)) rfl]
                    rw [hRefB]
                  exact ⟨aid, bOff, boxP, boxLen, rfl, hBoxPW, hLoad,
                    hReadBox, boxPointee_slice_u8_to_refValid
                      (heap_of_owned (m := m) (isMut := false)
                        (elem := .int .i8 false) (p := boxP)
                        (cap := boxLen) (len := boxLen) hRefB)⟩

private theorem checkArgsMatchV2_slice_boxSlice_inv {args : List Val}
    (h : checkArgsMatchV2 args
      [.ref .shared (.slice (.int .i8 false)),
       .ref .shared (.box (.slice (.int .i8 false)))] = true) :
    ∃ (sPtr bPtr : PtrVal) (sLen : UInt64),
      args = [.slicePtr sPtr sLen, .ptr bPtr] ∧
      sPtr.width = .isize ∧ bPtr.width = .isize := by
  cases args with
  | nil => cases h
  | cons a0 rest =>
    cases rest with
    | nil =>
      unfold checkArgsMatchV2 at h
      cases h0 : checkValV2 a0 (.ref .shared (.slice (.int .i8 false))) with
      | false => rw [h0] at h; cases h
      | true => rw [h0] at h; cases h
    | cons a1 rest2 =>
      cases rest2 with
      | cons _ _ =>
        unfold checkArgsMatchV2 at h
        cases h0 : checkValV2 a0 (.ref .shared (.slice (.int .i8 false))) with
        | false => rw [h0] at h; cases h
        | true =>
          rw [h0] at h
          unfold checkArgsMatchV2 at h
          cases h1 : checkValV2 a1
              (.ref .shared (.box (.slice (.int .i8 false)))) with
          | false => rw [h1] at h; cases h
          | true => rw [h1] at h; cases h
      | nil =>
        unfold checkArgsMatchV2 at h
        cases h0 : checkValV2 a0 (.ref .shared (.slice (.int .i8 false))) with
        | false => rw [h0] at h; cases h
        | true =>
          rw [h0] at h
          unfold checkArgsMatchV2 at h
          cases h1 : checkValV2 a1
              (.ref .shared (.box (.slice (.int .i8 false)))) with
          | false => rw [h1] at h; cases h
          | true =>
            unfold checkValV2 at h0 h1
            cases a0 with
            | slicePtr sPtr sLen =>
              cases a1 with
              | ptr bPtr =>
                cases sPtr with
                | mk sAid sOff sW =>
                  cases bPtr with
                  | mk bAid bOff bW =>
                    cases sW with
                    | i8 | i16 | i32 | i64 | i128 => cases h0
                    | isize =>
                      cases bW with
                      | i8 | i16 | i32 | i64 | i128 => cases h1
                      | isize =>
                        exact ⟨⟨sAid, sOff, .isize⟩, ⟨bAid, bOff, .isize⟩,
                          sLen, rfl, rfl, rfl⟩
              | scalar _ | bool _ | char _ | ordering _ | enumVal _ _ | unit
              | slicePtr _ _ | rangeTo _ | rangeFrom _ | vec _ _ _ | tuple _
              | bytes _ | range _ _ | array _ => cases h1
              | optionVal o => cases o <;> cases h1
              | boxPtr _ optL => cases optL <;> cases h1
            | scalar _ | bool _ | char _ | ordering _ | enumVal _ _ | unit
            | ptr _ | rangeTo _ | rangeFrom _ | vec _ _ _ | tuple _
            | bytes _ | range _ _ | array _ => cases h0
            | optionVal o => cases o <;> cases h0
            | boxPtr _ optL => cases optL <;> cases h0

private theorem body3_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_3 q) :
    match q.args with
    | [.slicePtr _ sLen, .ptr bPtr] =>
      ∃ (bPtrOut : PtrVal) (bLen : UInt64),
        readBoxFromRef (entryMemoryWithCaller q.callerMem) false
          (.slice (.int .i8 false)) bPtr =
          .ok ⟨.slice (.int .i8 false), bPtrOut, some bLen⟩ ∧
        WellFormedV2 (entryProgForBody Captured.program 3) q ∧
        BehaviorV2 (entryProgForBody Captured.program 3) q
          (TerminalOut.returned
            ⟨.tuple
              [ .scalar
                  ⟨.isize, false,
                    truncateBits .isize (BitVec.ofNat 128 sLen.toNat)⟩
              , .scalar
                  ⟨.isize, false,
                    truncateBits .isize (BitVec.ofNat 128 bLen.toNat)⟩
              ], q.callerMem⟩)
    | _ => False := by
  rcases hValid with ⟨hCM, hArgs, hRefs, hSpans⟩
  have hArgs' : checkArgsMatchV2 q.args
      [.ref .shared (.slice (.int .i8 false)),
       .ref .shared (.box (.slice (.int .i8 false)))] = true := hArgs
  let ⟨sPtr, bPtr, sLen, hQArgs, hSW, hBW⟩ :=
    checkArgsMatchV2_slice_boxSlice_inv hArgs'
  let m0 : MemoryState := entryMemoryWithCaller q.callerMem
  have hRefsList : refsValidInMemList m0
      [.ref .shared (.slice (.int .i8 false)),
       .ref .shared (.box (.slice (.int .i8 false)))]
      [.slicePtr sPtr sLen, .ptr bPtr] = true := by
    rw [← hQArgs]; exact hRefs
  unfold refsValidInMemList refsValidInMem at hRefsList
  have hRefS : refValidInMem m0 .shared (.slice (.int .i8 false))
      (.slicePtr sPtr sLen) = .ok () := by
    cases hR : refValidInMem m0 .shared (.slice (.int .i8 false))
        (.slicePtr sPtr sLen) with
    | error _ => rw [hR] at hRefsList; cases hRefsList
    | ok u => cases u; rfl
  have hRefB : refValidInMem m0 .shared (.box (.slice (.int .i8 false)))
      (.ptr bPtr) = .ok () := by
    rw [hRefS] at hRefsList
    dsimp only at hRefsList
    unfold refsValidInMemList refsValidInMem at hRefsList
    cases hR : refValidInMem m0 .shared (.box (.slice (.int .i8 false)))
        (.ptr bPtr) with
    | error _ => rw [hR] at hRefsList; cases hRefsList
    | ok u => cases u; rfl
  let ⟨bAid, bOff, boxP, bLen, hBPEq, hBoxPW, hLoadBox, hReadBox, hRefBoxS⟩ :=
    boxSliceRef_ok_elim hRefB
  have hStatic : BodyStaticAdmittedV2 (entryProgForBody Captured.program 3)
      Captured.body_3 = true := by
    unfold BodyStaticAdmittedV2; decide
  have hInit := initStateV2_ok_of (p := entryProgForBody Captured.program 3)
    (body := Captured.body_3) rfl hStatic ⟨hCM, hArgs, hRefs, hSpans⟩
  rw [hQArgs] at hInit
  have hInitSt :
      initLocalsLoop Captured.body_3 [.slicePtr sPtr sLen, .ptr bPtr] 0
        Captured.body_3.locals =
      [.immediate none, .immediate (some (.slicePtr sPtr sLen)),
       .immediate (some (.ptr bPtr)), .dead, .dead, .dead, .dead,
       .immediate none, .immediate none] := rfl
  rw [hInitSt] at hInit
  let sV : Option Val := some (.slicePtr sPtr sLen)
  let bV : Option Val := some (.ptr bPtr)
  let bxV : Option Val := some (.boxPtr boxP (some bLen))
  let brV : Option Val := some (.slicePtr boxP bLen)
  let sLenVal : Val :=
    .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 sLen.toNat)⟩
  let bLenVal : Val :=
    .scalar ⟨.isize, false, truncateBits .isize (BitVec.ofNat 128 bLen.toNat)⟩
  let ls_b0_0 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .dead, .dead, .dead, .dead,
     .immediate none, .immediate none]
  let ls_b0_2 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate none,
     .immediate none, .dead, .dead, .immediate none, .immediate none]
  let ls_b0_t : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate none,
     .immediate sV, .dead, .dead, .immediate none, .immediate none]
  let ls_b1_0 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate (some sLenVal),
     .immediate none, .dead, .dead, .immediate none, .immediate none]
  let ls_b1_3 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate (some sLenVal),
     .dead, .immediate none, .immediate none, .immediate none, .immediate none]
  let ls_b1_4 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate (some sLenVal),
     .dead, .immediate none, .immediate none, .immediate bxV, .immediate none]
  let ls_b1_5 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate (some sLenVal),
     .dead, .immediate none, .immediate none, .immediate bxV, .immediate brV]
  let ls_b1_t : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate (some sLenVal),
     .dead, .immediate none, .immediate brV, .immediate bxV, .immediate brV]
  let ls_b2_0 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate (some sLenVal),
     .dead, .immediate (some bLenVal), .immediate none, .immediate bxV,
     .immediate brV]
  let ls_b2_1 : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV, .immediate (some sLenVal),
     .dead, .immediate (some bLenVal), .dead, .immediate bxV, .immediate brV]
  let ls_b2_2 : List LocalSlot :=
    [.immediate (some (.tuple [sLenVal, bLenVal])), .immediate sV,
     .immediate bV, .immediate none, .dead, .immediate none, .dead,
     .immediate bxV, .immediate brV]
  let ls_b2_t : List LocalSlot :=
    [.immediate (some (.tuple [sLenVal, bLenVal])), .immediate sV,
     .immediate bV, .dead, .dead, .dead, .dead, .immediate bxV,
     .immediate brV]
  have hSLenWf : checkValV2 sLenVal (.int .isize false) = true := by
    unfold checkValV2 checkVal Val.ty?; dsimp only
    rw [scalarWf_truncateBits]; rfl
  have hBLenWf : checkValV2 bLenVal (.int .isize false) = true := by
    unfold checkValV2 checkVal Val.ty?; dsimp only
    rw [scalarWf_truncateBits]; rfl
  have hSRefWf : checkValV2 (.slicePtr sPtr sLen)
      (.ref .shared (.slice (.int .i8 false))) = true := by
    unfold checkValV2; rw [hSW]; rfl
  have hBoxWf : checkValV2 (.boxPtr boxP (some bLen))
      (.box (.slice (.int .i8 false))) = true := by
    unfold checkValV2; rw [hBoxPW]; rfl
  have hBRefWf : checkValV2 (.slicePtr boxP bLen)
      (.ref .shared (.slice (.int .i8 false))) = true := by
    unfold checkValV2; rw [hBoxPW]; rfl
  have c02 : ChainTo (entryProgForBody Captured.program 3)
      ⟨[⟨3, 0, 0, ls_b0_0, none, none, none⟩], q.callerMem, m0⟩
      ⟨[⟨3, 0, 2, ls_b0_2, none, none, none⟩], q.callerMem, m0⟩ :=
    ChainTo.step rfl (ChainTo.step rfl (ChainTo.refl _))
  have hB02 : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 0, 2, ls_b0_2, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨3, 0, 3, ls_b0_t, none, none, none⟩], q.callerMem, m0⟩ :=
    evalStepV2_assign_reborrow_slice_u8 rfl rfl rfl rfl rfl rfl hRefS
      (writePlaceV2_imm_ok hSRefWf rfl rfl)
  have hB0t : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 0, 3, ls_b0_t, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨3, 1, 0, ls_b1_0, none, none, none⟩], q.callerMem, m0⟩ :=
    evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
      (execCoreCallOpWithMem_sliceLen_u8 hRefS)
      (writePlaceV2_imm_ok hSLenWf rfl rfl)
  have c13 : ChainTo (entryProgForBody Captured.program 3)
      ⟨[⟨3, 1, 0, ls_b1_0, none, none, none⟩], q.callerMem, m0⟩
      ⟨[⟨3, 1, 3, ls_b1_3, none, none, none⟩], q.callerMem, m0⟩ :=
    ChainTo.step rfl (ChainTo.step rfl (ChainTo.step rfl (ChainTo.refl _)))
  have hB13 : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 1, 3, ls_b1_3, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨3, 1, 4, ls_b1_4, none, none, none⟩], q.callerMem, m0⟩ := by
    have hAidEq : bPtr.allocId = some bAid := by rw [hBPEq]
    have hOffEq : bPtr.offsetBytes.toNat = bOff.toNat := by rw [hBPEq]
    have hLoadBox' : loadIndirectV2 m0 (.box (.slice (.int .i8 false)))
        ⟨bAid, bPtr.offsetBytes.toNat⟩ =
        .ok (some (.boxPtr boxP (some bLen))) := by
      rw [hOffEq]; exact hLoadBox
    exact evalStepV2_assign_copy_deref rfl rfl rfl rfl rfl (Or.inl rfl) rfl
      layoutOfTyV2_box_slice_u8 rfl hAidEq hLoadBox'
      (writePlaceV2_imm_ok hBoxWf rfl rfl)
      (checkAssignCopyHazardV2_copy_deref_imm rfl rfl rfl hAidEq
        layoutOfTyV2_box_slice_u8)
  have hB14 : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 1, 4, ls_b1_4, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨3, 1, 5, ls_b1_5, none, none, none⟩], q.callerMem, m0⟩ :=
    evalStepV2_assign_boxAsRef_slice_u8 rfl rfl rfl rfl rfl rfl hRefBoxS
      (writePlaceV2_imm_ok hBRefWf rfl rfl)
  have hB15 : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 1, 5, ls_b1_5, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨3, 1, 6, ls_b1_t, none, none, none⟩], q.callerMem, m0⟩ :=
    evalStepV2_assign_reborrow_slice_u8 rfl rfl rfl rfl rfl rfl hRefBoxS
      (writePlaceV2_imm_ok hBRefWf rfl rfl)
  have hB1t : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 1, 6, ls_b1_t, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨3, 2, 0, ls_b2_0, none, none, none⟩], q.callerMem, m0⟩ :=
    evalStepV2_coreCall rfl rfl rfl rfl rfl rfl rfl
      (execCoreCallOpWithMem_sliceLen_u8 hRefBoxS)
      (writePlaceV2_imm_ok hBLenWf rfl rfl)
  let ls_b2_1m : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV,
     liveUninitSlot (.int .isize false), .dead, .immediate (some bLenVal),
     .dead, .immediate bxV, .immediate brV]
  let ls_b2_1mm : List LocalSlot :=
    [.immediate none, .immediate sV, .immediate bV,
     liveUninitSlot (.int .isize false), .dead,
     liveUninitSlot (.int .isize false), .dead, .immediate bxV,
     .immediate brV]
  have hOp3 : evalOperandToSlotV2 Captured.body_3.locals ls_b2_1 m0
      (.move ⟨3, []⟩) =
      .ok (.int .isize false, some sLenVal, ls_b2_1m, m0) := by
    unfold evalOperandToSlotV2 readPlaceV2
    dsimp only [Captured.body_3, Trusted.MirSemantics.getElem?, ls_b2_1]
    rw [ite_bool_false (!isSupportedV2LocalTy (.int .isize false)) rfl]
    rw [ite_bool_true true rfl]
    rfl
  have hOp5 : evalOperandToSlotV2 Captured.body_3.locals ls_b2_1m m0
      (.move ⟨5, []⟩) =
      .ok (.int .isize false, some bLenVal, ls_b2_1mm, m0) := by
    unfold evalOperandToSlotV2 readPlaceV2
    dsimp only [Captured.body_3, Trusted.MirSemantics.getElem?, ls_b2_1m]
    rw [ite_bool_false (!isSupportedV2LocalTy (.int .isize false)) rfl]
    rw [ite_bool_true true rfl]
    rfl
  have hArgsOk : evalArgOperandsV2 Captured.body_3.locals ls_b2_1 m0
      [.move ⟨3, []⟩, .move ⟨5, []⟩] =
      .ok ([(.int .isize false, sLenVal), (.int .isize false, bLenVal)],
        ls_b2_1mm, m0) := by
    unfold evalArgOperandsV2
    rw [hOp3]; dsimp only
    unfold evalArgOperandsV2
    rw [hOp5]; dsimp only
    unfold evalArgOperandsV2
    rfl
  have hB21 : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 2, 1, ls_b2_1, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨3, 2, 2, ls_b2_2, none, none, none⟩], q.callerMem, m0⟩ := by
    dsimp only [Captured.body_3] at hArgsOk
    rw [evalStepV2_stmt rfl rfl rfl rfl]
    unfold evalStatementV2 placeStaticTyV2 resolvePlaceDestV2 evalRvalueV2
    dsimp only [Captured.program, Captured.body_3,
      Trusted.MirSemantics.getElem?]
    rw [hArgsOk]; dsimp only
    rw [ite_bool_false _
      (by
        dsimp only [argValues]
        unfold checkValV2List; rw [hSLenWf]
        unfold checkValV2List; rw [hBLenWf]
        rfl)]
    dsimp only [argValues]
    unfold writePlaceDestV2; dsimp only
    rw [ite_bool_false _
      (by
        unfold checkValV2
        unfold checkValV2List; rw [hSLenWf]
        unfold checkValV2List; rw [hBLenWf]
        rfl)]
    rfl
  have hCM' : extractReturnMemoryV2 q.callerMem m0 ls_b2_t = q.callerMem := by
    have h0 : m0 = ⟨(entryMemoryWithCaller q.callerMem).nextAllocId,
        q.callerMem.allocations ++ []⟩ := by
      dsimp only [m0, entryMemoryWithCaller]
      rw [List.append_nil]
    rw [h0, extractReturnMemoryV2_append hCM]
    show (⟨q.callerMem.allocations ++ []⟩ : CallerMemory) = q.callerMem
    rw [List.append_nil]
  have hRet : evalStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 2, 4, ls_b2_t, none, none, none⟩], q.callerMem, m0⟩ =
      .done (.returned ⟨.tuple [sLenVal, bLenVal], q.callerMem⟩) := by
    have hRetRaw : evalStepV2 (entryProgForBody Captured.program 3)
        ⟨[⟨3, 2, 4, ls_b2_t, none, none, none⟩], q.callerMem, m0⟩ =
        .done (.returned ⟨.tuple [sLenVal, bLenVal],
          extractReturnMemoryV2 q.callerMem m0 ls_b2_t⟩) :=
      evalStepV2_return_imm
      (p := entryProgForBody Captured.program 3)
      (frame := ⟨3, 2, 4, ls_b2_t, none, none, none⟩) (mem := m0) (cm := q.callerMem)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rw [hCM'] at hRetRaw
    exact hRetRaw
  have c20 : ChainTo (entryProgForBody Captured.program 3)
      ⟨[⟨3, 2, 0, ls_b2_0, none, none, none⟩], q.callerMem, m0⟩
      ⟨[⟨3, 2, 1, ls_b2_1, none, none, none⟩], q.callerMem, m0⟩ :=
    ChainTo.step rfl (ChainTo.refl _)
  have c22t : ChainTo (entryProgForBody Captured.program 3)
      ⟨[⟨3, 2, 2, ls_b2_2, none, none, none⟩], q.callerMem, m0⟩
      ⟨[⟨3, 2, 4, ls_b2_t, none, none, none⟩], q.callerMem, m0⟩ :=
    ChainTo.step rfl (ChainTo.step rfl (ChainTo.refl _))
  have hChain : ChainStepV2 (entryProgForBody Captured.program 3)
      ⟨[⟨3, 0, 0, ls_b0_0, none, none, none⟩], q.callerMem, m0⟩
      (.done (.returned ⟨.tuple [sLenVal, bLenVal], q.callerMem⟩)) :=
    chainTo_chainStepV2 c02
      (ChainStepV2.step hB02
        (ChainStepV2.step hB0t
          (chainTo_chainStepV2 c13
            (ChainStepV2.step hB13
              (ChainStepV2.step hB14
                (ChainStepV2.step hB15
                  (ChainStepV2.step hB1t
                    (chainTo_chainStepV2 c20
                      (ChainStepV2.step hB21
                        (chainTo_chainStepV2 c22t (.base hRet)))))))))))
  have hRes := spec_and_behaviorV2_of_chainStep hInit hChain
  rw [hQArgs]
  exact ⟨boxP, bLen, hReadBox, hRes.1, hRes.2⟩

/-! ## Body 4: `push_one` -/

private theorem find_some_id {id : AllocId} :
    ∀ {L : List Allocation} {a : Allocation},
      findAllocation id L = some a → a.allocId = id
  | [], _, h => by cases h
  | x :: xs, a, h => by
    cases hEq : Nat.beq x.allocId id with
    | true =>
      rw [findAllocation_cons_eq hEq] at h
      injection h with h
      rw [← h]; exact Nat.eq_of_beq_eq_true hEq
    | false =>
      rw [findAllocation_cons_ne hEq] at h
      exact find_some_id h

private theorem find_replace_ne {id : AllocId} {x : Allocation}
    (hNe : Nat.beq x.allocId id = false) :
    ∀ L : List Allocation,
      findAllocation id (replaceAllocation x L) = findAllocation id L
  | [] => rfl
  | y :: ys => by
    cases hY : Nat.beq y.allocId x.allocId with
    | true =>
      rw [replaceAllocation_cons_eq hY]
      have hYid : Nat.beq y.allocId id = false := by
        rw [Nat.eq_of_beq_eq_true hY]; exact hNe
      rw [findAllocation_cons_ne hNe, findAllocation_cons_ne hYid]
    | false =>
      rw [replaceAllocation_cons_ne hY]
      cases hYi : Nat.beq y.allocId id with
      | true =>
        rw [findAllocation_cons_eq hYi, findAllocation_cons_eq hYi]
      | false =>
        rw [findAllocation_cons_ne hYi, findAllocation_cons_ne hYi]
        exact find_replace_ne hNe ys

private theorem find_replace_eq {x : Allocation} :
    ∀ {L : List Allocation} {a : Allocation},
      findAllocation x.allocId L = some a →
      findAllocation x.allocId (replaceAllocation x L) = some x
  | [], _, h => by cases h
  | y :: ys, a, h => by
    cases hY : Nat.beq y.allocId x.allocId with
    | true =>
      rw [replaceAllocation_cons_eq hY]
      exact findAllocation_cons_eq (Nat.beq_refl _)
    | false =>
      rw [replaceAllocation_cons_ne hY, findAllocation_cons_ne hY]
      rw [findAllocation_cons_ne hY] at h
      exact find_replace_eq h

private theorem find_append_some {id : AllocId} {R : List Allocation}
    {a : Allocation} :
    ∀ {L : List Allocation}, findAllocation id L = some a →
      findAllocation id (L ++ R) = some a
  | [], h => by cases h
  | y :: ys, h => by
    show findAllocation id (y :: (ys ++ R)) = some a
    cases hY : Nat.beq y.allocId id with
    | true =>
      rw [findAllocation_cons_eq hY] at h
      rw [findAllocation_cons_eq hY]; exact h
    | false =>
      rw [findAllocation_cons_ne hY] at h
      rw [findAllocation_cons_ne hY]; exact find_append_some h

private theorem find_append_none {id : AllocId} {R : List Allocation} :
    ∀ {L : List Allocation}, findAllocation id L = none →
      findAllocation id (L ++ R) = findAllocation id R
  | [], _ => rfl
  | y :: ys, h => by
    show findAllocation id (y :: (ys ++ R)) = findAllocation id R
    cases hY : Nat.beq y.allocId id with
    | true => rw [findAllocation_cons_eq hY] at h; cases h
    | false =>
      rw [findAllocation_cons_ne hY] at h
      rw [findAllocation_cons_ne hY]; exact find_append_none h

private theorem find_none_of_lt {id : AllocId} :
    ∀ {L : List Allocation}, (∀ a, a ∈ L → a.allocId < id) →
      findAllocation id L = none
  | [], _ => rfl
  | y :: ys, h => by
    have hNe : Nat.beq y.allocId id = false := by
      cases hEq : Nat.beq y.allocId id with
      | false => rfl
      | true =>
        exact absurd (Nat.eq_of_beq_eq_true hEq)
          (Nat.ne_of_lt (h y (.head ys)))
    rw [findAllocation_cons_ne hNe]
    exact find_none_of_lt (fun a ha => h a (.tail y ha))

private theorem mem_replace {x a : Allocation} :
    ∀ {L : List Allocation}, a ∈ replaceAllocation x L → a ∈ L ∨ a = x
  | [], h => by cases h
  | y :: ys, h => by
    cases hY : Nat.beq y.allocId x.allocId with
    | true =>
      rw [replaceAllocation_cons_eq hY] at h
      cases h with
      | head _ => exact .inr rfl
      | tail _ hIn => exact .inl (.tail y hIn)
    | false =>
      rw [replaceAllocation_cons_ne hY] at h
      cases h with
      | head _ => exact .inl (.head ys)
      | tail _ hIn =>
        cases mem_replace hIn with
        | inl h1 => exact .inl (.tail y h1)
        | inr h2 => exact .inr h2

private theorem getD_find_id {k : AllocId} {M : List Allocation}
    {y : Allocation} (hy : y.allocId = k) :
    ((findAllocation k M).getD y).allocId = k := by
  cases hF : findAllocation k M with
  | none => exact hy
  | some z => exact find_some_id hF

private theorem find_extract_some {m : MemoryState} {id : AllocId} :
    ∀ {L : List Allocation} {a : Allocation},
      findAllocation id L = some a →
      findAllocation id (extractCallerAllocations m L) =
        some ((findAllocation id m.allocations).getD a)
  | [], _, h => by cases h
  | y :: ys, a, h => by
    dsimp only [extractCallerAllocations]
    have hU := getD_find_id (M := m.allocations) (y := y) rfl
    cases hY : Nat.beq y.allocId id with
    | true =>
      rw [findAllocation_cons_eq hY] at h
      injection h with h
      subst h
      have hYeq := Nat.eq_of_beq_eq_true hY
      have hU' : Nat.beq ((findAllocation y.allocId m.allocations).getD
          y).allocId id = true := by
        rw [hU]; exact hY
      rw [findAllocation_cons_eq hU', hYeq]
    | false =>
      rw [findAllocation_cons_ne hY] at h
      have hU' : Nat.beq ((findAllocation y.allocId m.allocations).getD
          y).allocId id = false := by
        rw [hU]; exact hY
      rw [findAllocation_cons_ne hU']
      exact find_extract_some h

private theorem find_extract_none {m : MemoryState} {id : AllocId} :
    ∀ {L : List Allocation}, findAllocation id L = none →
      findAllocation id (extractCallerAllocations m L) = none
  | [], _ => rfl
  | y :: ys, h => by
    dsimp only [extractCallerAllocations]
    have hU := getD_find_id (M := m.allocations) (y := y) rfl
    cases hY : Nat.beq y.allocId id with
    | true => rw [findAllocation_cons_eq hY] at h; cases h
    | false =>
      rw [findAllocation_cons_ne hY] at h
      have hU' : Nat.beq ((findAllocation y.allocId m.allocations).getD
          y).allocId id = false := by
        rw [hU]; exact hY
      rw [findAllocation_cons_ne hU']
      exact find_extract_none h

private theorem calleeLive_ids_in (cIds fIds : List AllocId) :
    ∀ l : List Allocation, (∀ a, a ∈ l → a.allocId ∈ cIds) →
      calleeLiveAllocations cIds fIds l = []
  | [], _ => rfl
  | a :: rest, h => by
    change (if (a.live && Mutability.beq a.mutability .mut &&
        natNotElem a.allocId cIds &&
        natNotElem a.allocId fIds) = true then
        a :: calleeLiveAllocations cIds fIds rest
      else calleeLiveAllocations cIds fIds rest) = []
    rw [natNotElem_false_of_mem (h a (.head rest))]
    rw [Bool.and_false, Bool.false_and]
    exact calleeLive_ids_in cIds fIds rest (fun b hb => h b (.tail a hb))

private theorem natOfLe_leBytes :
    ∀ (n v : Nat), v < 256 ^ n → natOfLeBytes (leBytesOfNat n v) = v
  | 0, v, h => by
    have hv : v = 0 := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.zero_le v)
    rw [hv]; rfl
  | n + 1, v, h => by
    have hDiv : v / 256 < 256 ^ n :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr h
    change (BitVec.ofNat 8 (v % 256)).toNat +
      256 * natOfLeBytes (leBytesOfNat n (v / 256)) = v
    rw [BitVec.toNat_ofNat, natOfLe_leBytes n (v / 256) hDiv]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt v (by decide) :
      v % 256 < 2 ^ 8)]
    exact Nat.mod_add_div v 256

private theorem uint64_ofNat_toNat (c : UInt64) : UInt64.ofNat c.toNat = c := by
  cases c with
  | ofBitVec bv =>
    exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq
      (by
        change (BitVec.ofNat 64 bv.toNat).toNat = bv.toNat
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt bv.isLt))

private theorem uint64_toNat_lt (c : UInt64) : c.toNat < 256 ^ 8 := by
  cases c with
  | ofBitVec bv => exact bv.isLt

private theorem uint64_toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) :
    (UInt64.ofNat n).toNat = n := by
  change (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

private theorem decode_le8 (c : UInt64) :
    UInt64.ofNat (decodeUInt profileV2TargetEndian
      (encodeUInt .little 8 c.toNat)) = c := by
  change UInt64.ofNat (natOfLeBytes (leBytesOfNat 8 c.toNat)) = c
  rw [natOfLe_leBytes 8 c.toNat (uint64_toNat_lt c), uint64_ofNat_toNat]

private noncomputable def vecBytes (aid : AllocId) (cap len : UInt64) :
    List AllocByte :=
  List.replicate 8 (.init 0 (some aid)) ++
    (encodeUInt .little 8 cap.toNat).map (fun b => .init b none) ++
    (encodeUInt .little 8 len.toNat).map (fun b => .init b none)

private theorem vecBytes_length (aid : AllocId) (cap len : UInt64) :
    (vecBytes aid cap len).length = 24 := rfl

private theorem decode_vecBytes (aid : AllocId) (cap len : UInt64) :
    decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (vecBytes aid cap len) =
      .ok (some (.vec ⟨some aid, 0, .isize⟩ cap len)) := by
  refine (decodeValV2_vec_u8_zero aid
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :
    decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      (vecBytes aid cap len) = _).trans ?_
  show Except.ok (some (Val.vec ⟨some aid, 0, .isize⟩
    (UInt64.ofNat (decodeUInt profileV2TargetEndian
      (encodeUInt .little 8 cap.toNat)))
    (UInt64.ofNat (decodeUInt profileV2TargetEndian
      (encodeUInt .little 8 len.toNat))))) = _
  rw [decode_le8 cap, decode_le8 len]

private theorem take_drop_splice {A E D : List AllocByte} {off : Nat}
    (hA : A.length = off) :
    ((A ++ E ++ D).drop off).take E.length = E := by
  rw [List.append_assoc, List.drop_left' hA, List.take_left' rfl]

private theorem length_take_of_le {l : List AllocByte} {n : Nat}
    (h : n ≤ l.length) : (l.take n).length = n := by
  rw [List.length_take, Nat.min_eq_left h]

/-! ## `push_one` (body 4): `Vec<u8>` Handle Lemmas -/

private theorem or3_false :
    ∀ {a b c : Bool}, (!a || !b || !c) = false →
      a = true ∧ b = true ∧ c = true
  | true, true, true, _ => ⟨rfl, rfl, rfl⟩
  | false, _, _, h => by cases h
  | true, false, _, h => by cases h
  | true, true, false, h => by cases h

private theorem not_false_eq : ∀ {a : Bool}, (!a) = false → a = true
  | true, _ => rfl
  | false, h => by cases h

private theorem refValid_vec_u8_gen {m : MemoryState} {p : PtrVal}
    {vaid : AllocId} {h : Allocation} {bufPtr : PtrVal} {cap len : UInt64}
    (hP : p.allocId = some vaid)
    (hFind : findAllocation vaid m.allocations = some h)
    (hLive : h.live = true)
    (hInB : isInBounds h p.offsetBytes.toNat 24 = true)
    (hAl : isAligned h p.offsetBytes.toNat 3 = true)
    (hMut : h.mutability = .mut)
    (hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      ((h.bytes.drop p.offsetBytes.toNat).take 24) =
      .ok (some (.vec bufPtr cap len)))
    (hBuf : ownedHeapBufValidInMem m true (.int .i8 false) bufPtr cap len =
      .ok ()) :
    refValidInMem m .mut (.vec (.int .i8 false)) (.ptr p) = .ok () := by
  unfold refValidInMem
  rw [layoutOfTyV2_vec_u8]; dsimp only
  rw [hP]; dsimp only; rw [hFind]; dsimp only
  rw [ite_bool_false
    (!h.live || !isInBounds h p.offsetBytes.toNat 24 ||
      !isAligned h p.offsetBytes.toNat 3)
    (by rw [hLive, hInB, hAl]; rfl)]
  rw [ite_bool_false
    (Mutability.beq .mut .mut && !Mutability.beq h.mutability .mut)
    (by rw [hMut]; rfl)]
  rw [hDec]; exact hBuf

private theorem readVecFromRef_gen {m : MemoryState} {p : PtrVal}
    {vaid : AllocId} {h : Allocation} {bufPtr : PtrVal} {cap len : UInt64}
    (hP : p.allocId = some vaid)
    (hFind : findAllocation vaid m.allocations = some h)
    (hLive : h.live = true)
    (hInB : isInBounds h p.offsetBytes.toNat 24 = true)
    (hAl : isAligned h p.offsetBytes.toNat 3 = true)
    (hMut : h.mutability = .mut)
    (hDec : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      ((h.bytes.drop p.offsetBytes.toNat).take 24) =
      .ok (some (.vec bufPtr cap len)))
    (hBuf : ownedHeapBufValidInMem m true (.int .i8 false) bufPtr cap len =
      .ok ()) :
    readVecFromRef m true (.int .i8 false) p =
      .ok ⟨.int .i8 false, bufPtr, cap, len⟩ := by
  have hRef : refValidInMem m (if true then .mut else .shared)
      (.vec (.int .i8 false)) (.ptr p) = .ok () :=
    refValid_vec_u8_gen hP hFind hLive hInB hAl hMut hDec hBuf
  have hLoad : loadIndirectV2 m (.vec (.int .i8 false))
      ⟨vaid, p.offsetBytes.toNat⟩ = .ok (some (.vec bufPtr cap len)) :=
    loadIndirectV2_ok layoutOfTyV2_vec_u8
      (readBytes_ok rfl hFind hLive hInB hAl) hDec
  unfold readVecFromRef
  rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false)) rfl]
  dsimp only
  rw [hRef]; dsimp only; rw [hP]; dsimp only; rw [hLoad]
  dsimp only [vecValidInMem]
  rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false)) rfl]
  rw [hBuf]

private theorem writeVecToRef_gen {m : MemoryState} {p : PtrVal}
    {vaid : AllocId} {h : Allocation} {X : AllocId} {cap len : UInt64}
    (hP : p.allocId = some vaid)
    (hFind : findAllocation vaid m.allocations = some h)
    (hLive : h.live = true)
    (hInB : isInBounds h p.offsetBytes.toNat 24 = true)
    (hAl : isAligned h p.offsetBytes.toNat 3 = true)
    (hMut : h.mutability = .mut) :
    writeVecToRef m p ⟨.int .i8 false, ⟨some X, 0, .isize⟩, cap, len⟩ =
      .ok ⟨m.nextAllocId, replaceAllocation
        ⟨h.allocId, h.alignLog2, h.mutability,
          h.bytes.take p.offsetBytes.toNat ++ vecBytes X cap len ++
            h.bytes.drop (p.offsetBytes.toNat + 24), h.live⟩
        m.allocations⟩ := by
  unfold writeVecToRef
  rw [hP]; dsimp only [VecModel.toVal]
  exact storeIndirectV2_ok layoutOfTyV2_vec_u8 (encodeValV2_vec_u8 X cap len)
    (writeBytes_ok h rfl hFind hLive hInB hAl hMut)

private theorem readVec_inv {m : MemoryState} {p : PtrVal} {v : VecModel}
    (hR : readVecFromRef m true (.int .i8 false) p = .ok v) :
    ∃ (vaid : AllocId) (h : Allocation),
      p.allocId = some vaid ∧
      findAllocation vaid m.allocations = some h ∧
      h.live = true ∧
      isInBounds h p.offsetBytes.toNat 24 = true ∧
      isAligned h p.offsetBytes.toNat 3 = true ∧
      h.mutability = .mut ∧
      v = ⟨.int .i8 false, v.ptr, v.cap, v.len⟩ ∧
      decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
        ((h.bytes.drop p.offsetBytes.toNat).take 24) =
        .ok (some (.vec v.ptr v.cap v.len)) ∧
      ownedHeapBufValidInMem m true (.int .i8 false) v.ptr v.cap v.len =
        .ok () := by
  unfold readVecFromRef at hR
  rw [ite_bool_false (!isSupportedPointeeTy (.int .i8 false)) rfl] at hR
  dsimp only at hR
  cases hRef : refValidInMem m .mut (.vec (.int .i8 false)) (.ptr p) with
  | error k =>
    have hRef' : refValidInMem m (if true = true then .mut else .shared)
        (.vec (.int .i8 false)) (.ptr p) = .error k := hRef
    rw [hRef'] at hR; cases hR
  | ok u =>
    have hRef' : refValidInMem m (if true = true then .mut else .shared)
        (.vec (.int .i8 false)) (.ptr p) = .ok u := hRef
    rw [hRef'] at hR; dsimp only at hR
    cases hP : p.allocId with
    | none => rw [hP] at hR; cases hR
    | some vaid =>
      rw [hP] at hR; dsimp only at hR
      unfold loadIndirectV2 at hR
      rw [layoutOfTyV2_vec_u8] at hR; dsimp only at hR
      unfold readBytes at hR
      cases hF : findAllocation vaid m.allocations with
      | none => rw [hF] at hR; cases hR
      | some h =>
        rw [hF] at hR; dsimp only at hR
        rw [ite_bool_false (Nat.beq 24 0) rfl] at hR
        cases hC : (!h.live || !isInBounds h p.offsetBytes.toNat 24 ||
            !isAligned h p.offsetBytes.toNat 3) with
        | true => rw [ite_bool_true _ hC] at hR; cases hR
        | false =>
          rw [ite_bool_false _ hC] at hR; dsimp only at hR
          let ⟨hLive, hInB, hAl⟩ := or3_false hC
          have hMut : h.mutability = .mut := by
            unfold refValidInMem at hRef
            rw [layoutOfTyV2_vec_u8] at hRef; dsimp only at hRef
            rw [hP] at hRef; dsimp only at hRef; rw [hF] at hRef
            dsimp only at hRef
            rw [ite_bool_false _ hC] at hRef
            cases hM : h.mutability with
            | shared => rw [hM] at hRef; cases hRef
            | _ => rfl
          cases hD : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
              ((h.bytes.drop p.offsetBytes.toNat).take 24) with
          | error k => rw [hD] at hR; cases hR
          | ok od =>
            rw [hD] at hR
            cases od with
            | none => cases hR
            | some d =>
              cases d with
              | vec bp c l =>
                dsimp only [vecValidInMem] at hR
                rw [ite_bool_false
                  (!isSupportedPointeeTy (.int .i8 false)) rfl] at hR
                cases hO : ownedHeapBufValidInMem m true (.int .i8 false)
                    bp c l with
                | error k => rw [hO] at hR; cases hR
                | ok u2 =>
                  rw [hO] at hR
                  injection hR with hV
                  subst hV
                  exact ⟨vaid, h, rfl, hF, hLive, hInB, hAl, hMut, rfl, hD,
                    hO⟩
              | scalar _ | bool _ | char _ | ordering _ | enumVal _ _
              | unit | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _
              | boxPtr _ _ | tuple _ | bytes _ | range _ _ | optionVal _ | array _ => cases hR

private theorem owned_u8_inv {m : MemoryState} {isMut : Bool} {bp : PtrVal}
    {cap len : UInt64}
    (hO : ownedHeapBufValidInMem m isMut (.int .i8 false) bp cap len = .ok ())
    (hCap : Nat.beq cap.toNat 0 = false) :
    ∃ (baid : AllocId) (b : Allocation),
      bp = ⟨some baid, 0, .isize⟩ ∧
      findAllocation baid m.allocations = some b ∧
      b.live = true ∧
      b.bytes.length = cap.toNat ∧
      b.alignLog2 = 0 ∧
      (isMut && !Mutability.beq b.mutability .mut) = false ∧
      len.toNat ≤ cap.toNat ∧
      cap.toNat < isizeMaxBytes ∧
      isSliceAllInit (b.bytes.take len.toNat) = true := by
  unfold ownedHeapBufValidInMem at hO
  cases hH : heapBufValidInMem m isMut (.int .i8 false) bp cap len with
  | error k => rw [hH] at hO; cases hO
  | ok u =>
    rw [hH] at hO; dsimp only at hO
    rw [layoutOfTyV2_u8] at hO; dsimp only at hO
    rw [ite_bool_false (Nat.beq 1 0 || Nat.beq cap.toNat 0)
      (by rw [hCap]; rfl)] at hO
    cases hA : bp.allocId with
    | none => rw [hA] at hO; cases hO
    | some baid =>
      rw [hA] at hO; dsimp only at hO
      cases hF : findAllocation baid m.allocations with
      | none => rw [hF] at hO; cases hO
      | some b =>
        rw [hF] at hO; dsimp only at hO
        cases hC : (!Nat.beq bp.offsetBytes.toNat 0 ||
            !Nat.beq b.bytes.length (cap.toNat * 1) ||
            !Nat.beq b.alignLog2 0) with
        | true => rw [ite_bool_true _ hC] at hO; cases hO
        | false =>
          let ⟨hOff, hLen, hAl⟩ := or3_false hC
          unfold heapBufValidInMem at hH
          cases hW : IntWidth.beq bp.width .isize with
          | false =>
            rw [ite_bool_true (!IntWidth.beq bp.width .isize)
              (by rw [hW]; rfl)] at hH
            cases hH
          | true =>
            rw [ite_bool_false (!IntWidth.beq bp.width .isize)
              (by rw [hW]; rfl)] at hH
            rw [layoutOfTyV2_u8] at hH; dsimp only at hH
            cases hLC : Nat.ble len.toNat cap.toNat with
            | false =>
              rw [ite_bool_true (!Nat.ble len.toNat cap.toNat)
                (by rw [hLC]; rfl)] at hH
              cases hH
            | true =>
              rw [ite_bool_false (!Nat.ble len.toNat cap.toNat)
                (by rw [hLC]; rfl)] at hH
              cases hB : Nat.blt (cap.toNat * 1) isizeMaxBytes with
              | false =>
                rw [ite_bool_true (!Nat.blt (cap.toNat * 1) isizeMaxBytes)
                  (by rw [hB]; rfl)] at hH
                cases hH
              | true =>
                rw [ite_bool_false (!Nat.blt (cap.toNat * 1) isizeMaxBytes)
                  (by rw [hB]; rfl)] at hH
                rw [ite_bool_false (Nat.beq 1 0) rfl] at hH
                rw [ite_bool_false (Nat.beq cap.toNat 0) hCap] at hH
                rw [hA] at hH; dsimp only at hH; rw [hF] at hH
                dsimp only at hH
                have hOff0 : bp.offsetBytes.toNat = 0 :=
                  Nat.eq_of_beq_eq_true hOff
                rw [hOff0] at hH
                cases hC2 : (!b.live || !isInBounds b 0 (cap.toNat * 1) ||
                    !isAligned b 0 0) with
                | true => rw [ite_bool_true _ hC2] at hH; cases hH
                | false =>
                  rw [ite_bool_false _ hC2] at hH
                  let ⟨hLive, _, _⟩ := or3_false hC2
                  cases hM : (isMut && !Mutability.beq b.mutability .mut) with
                  | true => rw [ite_bool_true _ hM] at hH; cases hH
                  | false =>
                    rw [ite_bool_false _ hM] at hH
                    cases hI : isSliceAllInit
                        ((b.bytes.drop 0).take (len.toNat * 1)) with
                    | false =>
                      rw [ite_bool_true _ (by rw [hI]; rfl)] at hH; cases hH
                    | true =>
                      have hPtr : bp = ⟨some baid, 0, .isize⟩ := by
                        cases bp with
                        | mk a o w =>
                          dsimp only at hA hOff0 hW
                          subst hA
                          have hO0 : o = 0 := by
                            cases o with
                            | ofBitVec bv =>
                              exact congrArg UInt64.ofBitVec
                                (BitVec.eq_of_toNat_eq hOff0)
                          subst hO0
                          cases w with
                          | isize => rfl
                          | i8 | i16 | i32 | i64 | i128 => cases hW
                      refine ⟨baid, b, hPtr, hF, hLive, ?_,
                        Nat.eq_of_beq_eq_true hAl, hM,
                        Nat.le_of_ble_eq_true hLC, ?_, ?_⟩
                      · rw [Nat.eq_of_beq_eq_true hLen, Nat.mul_one]
                      · have h1 := Nat.le_of_ble_eq_true hB
                        rw [Nat.mul_one] at h1; exact h1
                      · rw [Nat.mul_one] at hI; exact hI

private theorem readBytes_zero_off_eq {m : MemoryState} {aid : AllocId}
    {b : Allocation} {n : Nat} {old : List AllocByte}
    (hFind : findAllocation aid m.allocations = some b)
    (h : readBytes m ⟨aid, 0⟩ n 0 = .ok old) :
    old = b.bytes.take n := by
  unfold readBytes at h
  rw [hFind] at h; dsimp only at h
  cases hN : Nat.beq n 0 with
  | true =>
    have hn := Nat.eq_of_beq_eq_true hN
    subst hn
    rw [ite_bool_true _ hN] at h
    cases hA : (!isAligned b 0 0) with
    | true => rw [ite_bool_true _ hA] at h; cases h
    | false =>
      rw [ite_bool_false _ hA] at h
      injection h with h
      rw [← h]; rfl
  | false =>
    rw [ite_bool_false _ hN] at h
    cases hC : (!b.live || !isInBounds b 0 n || !isAligned b 0 0) with
    | true => rw [ite_bool_true _ hC] at h; cases h
    | false =>
      rw [ite_bool_false _ hC] at h
      injection h with h
      rw [← h]; rfl

/-! ## `push_one` (body 4): `Vec::push` Evaluation -/

private theorem nat_ble_succ_self (n : Nat) : Nat.ble (n + 1) n = false := by
  cases h : Nat.ble (n + 1) n with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true h) (Nat.lt_irrefl n)

private theorem nat_ble_self_succ (n : Nat) : Nat.ble n (n + 1) = true :=
  Nat.ble_eq.mpr (Nat.le_succ n)

private theorem push_val_enc :
    encodeValV2 profileV2TargetEndian (.int .i8 false)
      (.scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 1)⟩) =
      .ok [.init 1 none] := rfl

private theorem push_val_chk :
    checkValV2 (.scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 1)⟩)
      (.int .i8 false) = true := rfl

private theorem evalVecPush_inPlace {m m1 m2 : MemoryState} {p : PtrVal}
    {bufAid : AllocId} {cap curLen : UInt64} {val : Val}
    {valBytes : List AllocByte}
    (hRead : readVecFromRef m true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap, curLen⟩)
    (hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) val =
      .ok valBytes)
    (hVal : checkValV2 val (.int .i8 false) = true)
    (hCap : Nat.ble (curLen.toNat + 1) cap.toNat = true)
    (hWrBuf : writeBytes m ⟨bufAid, curLen.toNat⟩ 0 valBytes = .ok m1)
    (hWrVec : writeVecToRef m1 p
      ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap,
        UInt64.ofNat (curLen.toNat + 1)⟩ = .ok m2) :
    execCoreCallOpWithMem m .vecPush
      [(.ref .mut (.vec (.int .i8 false)), .ptr p), (.int .i8 false, val)]
      .unit = .ok (.unit, m2) := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  refine execCoreCallOpWithMem_eq_allocOutcome ?_
  unfold execAllocCoreCallOutcome evalVecPushOutcome
  try dsimp only
  rw [ite_bool_false (!MirTy.unit.beq .unit ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  try dsimp only
  rw [ite_bool_false (!checkValV2 val (.int .i8 false)) (by rw [hVal]; rfl)]
  rw [hRead, layoutOfTyV2_u8, hEnc]
  dsimp only [ensureVecCapacityOutcome]
  rw [ite_bool_false (!Nat.ble curLen.toNat (curLen.toNat + 1))
    (by rw [nat_ble_self_succ]; rfl)]
  rw [ite_bool_true (Nat.ble (curLen.toNat + 1) cap.toNat) hCap]
  dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [hZ0, Nat.zero_add, Nat.mul_one, hWrBuf]; dsimp only; rw [hWrVec]
  rfl

private theorem evalVecPush_growEmpty {m m3 m4 : MemoryState} {p : PtrVal}
    {ptr0 : PtrVal} {val : Val} {valBytes : List AllocByte}
    (hRead : readVecFromRef m true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ptr0, 0, 0⟩)
    (hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) val =
      .ok valBytes)
    (hVal : checkValV2 val (.int .i8 false) = true)
    (hWrBuf : writeBytes
      ⟨m.nextAllocId + 1, m.allocations ++
        [⟨m.nextAllocId, 0, .mut, List.replicate 8 .uninit, true⟩]⟩
      ⟨m.nextAllocId, 0⟩ 0 valBytes = .ok m3)
    (hWrVec : writeVecToRef m3 p
      ⟨.int .i8 false, ⟨some m.nextAllocId, 0, .isize⟩, 8, 1⟩ = .ok m4) :
    execCoreCallOpWithMem m .vecPush
      [(.ref .mut (.vec (.int .i8 false)), .ptr p), (.int .i8 false, val)]
      .unit = .ok (.unit, m4) := by
  have hGrow : vecGrowCap 1 0 1 = some 8 := rfl
  have hL0 : (UInt64.toNat 0) = 0 := rfl
  have hL1 : UInt64.ofNat (0 + 1) = (1 : UInt64) := rfl
  have hC8 : UInt64.ofNat 8 = (8 : UInt64) := rfl
  refine execCoreCallOpWithMem_eq_allocOutcome ?_
  unfold execAllocCoreCallOutcome evalVecPushOutcome
  try dsimp only
  rw [ite_bool_false (!MirTy.unit.beq .unit ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  try dsimp only
  rw [ite_bool_false (!checkValV2 val (.int .i8 false)) (by rw [hVal]; rfl)]
  rw [hRead, layoutOfTyV2_u8, hEnc]
  dsimp only [ensureVecCapacityOutcome, allocHeapBuffer,
    MemoryState.reserveAllocId]
  rw [hL0]
  rw [ite_bool_false (!Nat.ble 0 (0 + 1)) rfl]
  rw [ite_bool_false (Nat.ble (0 + 1) 0) rfl]
  rw [hGrow]; dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [ite_bool_true (Nat.beq (0 * 1) 0) rfl]
  rw [ite_bool_true (Nat.beq 0 0) rfl]
  dsimp only
  rw [ite_bool_true (Nat.beq (0 * 1) 0) rfl]
  dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [hL0, Nat.zero_mul, Nat.zero_add, hWrBuf]; dsimp only
  rw [hC8, hL1, hWrVec]
  rfl

private theorem evalVecPush_growCopy {m m1 m3 m4 m5 : MemoryState}
    {p : PtrVal} {bufAid : AllocId} {cap : UInt64} {newCap : Nat}
    {val : Val} {valBytes oldBytes : List AllocByte}
    (hRead : readVecFromRef m true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ⟨some bufAid, 0, .isize⟩, cap, cap⟩)
    (hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) val =
      .ok valBytes)
    (hVal : checkValV2 val (.int .i8 false) = true)
    (hCapNz : Nat.beq cap.toNat 0 = false)
    (hGrow : vecGrowCap 1 cap.toNat (cap.toNat + 1) = some newCap)
    (hReadOld : readBytes m ⟨bufAid, 0⟩ cap.toNat 0 = .ok oldBytes)
    (hRetire : deallocateStack m ⟨bufAid, 0⟩ = .ok m1)
    (hWrOld : writeBytes
      ⟨m1.nextAllocId + 1, m1.allocations ++
        [⟨m1.nextAllocId, 0, .mut, List.replicate (newCap * 1) .uninit,
          true⟩]⟩
      ⟨m1.nextAllocId, 0⟩ 0 oldBytes = .ok m3)
    (hWrBuf : writeBytes m3 ⟨m1.nextAllocId, cap.toNat⟩ 0 valBytes = .ok m4)
    (hWrVec : writeVecToRef m4 p
      ⟨.int .i8 false, ⟨some m1.nextAllocId, 0, .isize⟩,
        UInt64.ofNat newCap, UInt64.ofNat (cap.toNat + 1)⟩ = .ok m5) :
    execCoreCallOpWithMem m .vecPush
      [(.ref .mut (.vec (.int .i8 false)), .ptr p), (.int .i8 false, val)]
      .unit = .ok (.unit, m5) := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  have hNz1 : Nat.beq (cap.toNat * 1) 0 = false := by
    rw [Nat.mul_one]; exact hCapNz
  refine execCoreCallOpWithMem_eq_allocOutcome ?_
  unfold execAllocCoreCallOutcome evalVecPushOutcome
  try dsimp only
  rw [ite_bool_false (!MirTy.unit.beq .unit ||
      !MirTy.beq (.int .i8 false) (.int .i8 false)) rfl]
  try dsimp only
  rw [ite_bool_false (!checkValV2 val (.int .i8 false)) (by rw [hVal]; rfl)]
  rw [hRead, layoutOfTyV2_u8, hEnc]
  dsimp only [ensureVecCapacityOutcome]
  rw [ite_bool_false (!Nat.ble cap.toNat (cap.toNat + 1))
    (by rw [nat_ble_self_succ]; rfl)]
  rw [ite_bool_false (Nat.ble (cap.toNat + 1) cap.toNat)
    (nat_ble_succ_self _)]
  rw [hGrow]; dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [ite_bool_false (Nat.beq (cap.toNat * 1) 0) hNz1]
  rw [hZ0, Nat.mul_one, hReadOld]; dsimp only
  rw [ite_bool_false (Nat.beq cap.toNat 0) hCapNz]
  dsimp only [retireHeapBuffer]
  rw [hZ0, hRetire]; dsimp only [allocHeapBuffer, MemoryState.reserveAllocId]
  rw [ite_bool_false (Nat.beq cap.toNat 0) hCapNz]
  rw [hWrOld]; dsimp only
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [hZ0, Nat.zero_add, Nat.mul_one, hWrBuf]; dsimp only; rw [hWrVec]
  rfl

/-! ## `push_one` (body 4): List, Arithmetic, and Inversion Lemmas -/

private theorem find_some_mem {id : AllocId} :
    ∀ {L : List Allocation} {a : Allocation},
      findAllocation id L = some a → a ∈ L
  | [], _, h => by cases h
  | x :: xs, a, h => by
    cases hEq : Nat.beq x.allocId id with
    | true =>
      rw [findAllocation_cons_eq hEq] at h
      injection h with h; rw [← h]; exact .head xs
    | false =>
      rw [findAllocation_cons_ne hEq] at h
      exact .tail x (find_some_mem h)

private theorem replace_append_found {x : Allocation} {R : List Allocation} :
    ∀ {L : List Allocation} {a : Allocation},
      findAllocation x.allocId L = some a →
      replaceAllocation x (L ++ R) = replaceAllocation x L ++ R
  | [], _, h => by cases h
  | y :: ys, a, h => by
    show replaceAllocation x (y :: (ys ++ R)) = _
    cases hY : Nat.beq y.allocId x.allocId with
    | true =>
      rw [replaceAllocation_cons_eq hY, replaceAllocation_cons_eq hY]; rfl
    | false =>
      rw [replaceAllocation_cons_ne hY, replaceAllocation_cons_ne hY]
      rw [findAllocation_cons_ne hY] at h
      exact congrArg (y :: ·) (replace_append_found h)

private theorem ids_replace_sub {x : Allocation} {L : List Allocation}
    {S : List AllocId} (hL : ∀ a, a ∈ L → a.allocId ∈ S)
    (hx : x.allocId ∈ S) :
    ∀ a, a ∈ replaceAllocation x L → a.allocId ∈ S := by
  intro a ha
  cases mem_replace ha with
  | inl h => exact hL a h
  | inr h => rw [h]; exact hx

private theorem lt_of_mem_replace {x : Allocation} {L : List Allocation}
    {n : Nat} (hL : ∀ a, a ∈ L → a.allocId < n) (hx : x.allocId < n) :
    ∀ a, a ∈ replaceAllocation x L → a.allocId < n := by
  intro a ha
  cases mem_replace ha with
  | inl h => exact hL a h
  | inr h => rw [h]; exact hx

private theorem splice_length {A E : List AllocByte} {n : Nat}
    (h : n + E.length ≤ A.length) :
    (A.take n ++ E ++ A.drop (n + E.length)).length = A.length := by
  have hn : n ≤ A.length :=
    Nat.le_trans (Nat.le_add_right n E.length) h
  rw [List.length_append, List.length_append, length_take_of_le hn,
    List.length_drop]
  exact Nat.add_sub_of_le h

private theorem take_splice_succ {A D : List AllocByte} {x : AllocByte}
    {n : Nat} (h : n ≤ A.length) :
    (A.take n ++ [x] ++ D).take (n + 1) = A.take n ++ [x] := by
  apply List.take_left'
  rw [List.length_append, length_take_of_le h]; rfl

private theorem isSliceAllInit_append :
    ∀ (A B : List AllocByte),
      isSliceAllInit (A ++ B) = (isSliceAllInit A && isSliceAllInit B)
  | [], _ => rfl
  | .uninit :: _, _ => rfl
  | .init _ _ :: rest, B => isSliceAllInit_append rest B

private theorem blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq.mpr h

private theorem nat_max_lt {a b n : Nat} (ha : a < n) (hb : b < n) :
    Nat.max a b < n := by
  have h := Nat.max_le.mpr ⟨ha, hb⟩
  rw [Nat.succ_max_succ] at h
  exact h

private theorem isize_lt_u64 : isizeMaxBytes < Nat.pow 2 64 := by decide

private theorem uint64_eq_of_toNat_eq {a b : UInt64}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofBitVec x =>
    cases b with
    | ofBitVec y => exact congrArg UInt64.ofBitVec (BitVec.eq_of_toNat_eq h)

private theorem growCap_ok {c : Nat} (hc : 1 ≤ c)
    (h : c * 2 < isizeMaxBytes) :
    vecGrowCap 1 c (c + 1) = some (Nat.max (c * 2) (Nat.max (c + 1) 8)) := by
  have hc1 : c + 1 ≤ c * 2 := by
    rw [Nat.mul_two]; exact Nat.add_le_add_left hc c
  have hMin : c + 1 < isizeMaxBytes := Nat.lt_of_le_of_lt hc1 h
  have h8 : 8 < isizeMaxBytes := by decide
  have hMax : Nat.max (c * 2) (Nat.max (c + 1) 8) < isizeMaxBytes :=
    nat_max_lt h (nat_max_lt hMin h8)
  unfold vecGrowCap
  dsimp only
  rw [ite_bool_false (!Nat.blt (c + 1) (Nat.pow 2 64))
    (by rw [blt_of_lt (Nat.lt_trans hMin isize_lt_u64)]; rfl)]
  rw [ite_bool_false (Nat.beq 1 0) rfl]
  rw [ite_bool_false (!Nat.blt ((c + 1) * 1) isizeMaxBytes)
    (by rw [Nat.mul_one, blt_of_lt hMin]; rfl)]
  rw [ite_bool_true (Nat.beq 1 1) rfl]
  rw [ite_bool_true
    (Nat.blt (Nat.max (c * 2) (Nat.max (c + 1) 8) * 1) isizeMaxBytes &&
      Nat.blt (Nat.max (c * 2) (Nat.max (c + 1) 8)) (Nat.pow 2 64))
    (by
      rw [Nat.mul_one, blt_of_lt hMax,
        blt_of_lt (Nat.lt_trans hMax isize_lt_u64)]; rfl)]

private theorem decodeVec_inv {bs : List AllocByte} {d : Val}
    (h : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false)) bs =
      .ok (some d)) :
    ∃ (bp : PtrVal) (c l : UInt64), d = .vec bp c l := by
  delta decodeValV2 at h; dsimp only at h; delta decodeValV2._f at h
  dsimp only at h
  cases hL : Nat.beq bs.length 24 with
  | false =>
    rw [ite_bool_true (!Nat.beq bs.length 24) (by rw [hL]; rfl)] at h
    cases h
  | true =>
    rw [ite_bool_false (!Nat.beq bs.length 24) (by rw [hL]; rfl)] at h
    cases h1 : initBytes? (bs.take 8) with
    | none => rw [h1] at h; cases h
    | some pRaw =>
      rw [h1] at h
      cases h2 : readPtrProv? (bs.take 8) with
      | none => rw [h2] at h; cases h
      | some prov =>
        rw [h2] at h
        cases h3 : initBytes? ((bs.drop 8).take 8) with
        | none => rw [h3] at h; cases h
        | some cRaw =>
          rw [h3] at h
          cases h4 : initBytes? (bs.drop 16) with
          | none => rw [h4] at h; cases h
          | some lRaw =>
            rw [h4] at h
            injection h with h
            injection h with h
            exact ⟨_, _, _, h.symm⟩

private theorem readVec_of_refValid {m : MemoryState} {p : PtrVal}
    (hRef : refValidInMem m .mut (.vec (.int .i8 false)) (.ptr p) = .ok ()) :
    ∃ v : VecModel, readVecFromRef m true (.int .i8 false) p = .ok v := by
  unfold refValidInMem at hRef
  rw [layoutOfTyV2_vec_u8] at hRef; dsimp only at hRef
  cases hP : p.allocId with
  | none =>
    rw [hP] at hRef; dsimp only at hRef
    rw [ite_bool_true (Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 24)
      (Bool.or_true _)] at hRef
    cases hRef
  | some vaid =>
    rw [hP] at hRef; dsimp only at hRef
    cases hF : findAllocation vaid m.allocations with
    | none => rw [hF] at hRef; cases hRef
    | some h =>
      rw [hF] at hRef; dsimp only at hRef
      cases hC : (!h.live || !isInBounds h p.offsetBytes.toNat 24 ||
          !isAligned h p.offsetBytes.toNat 3) with
      | true => rw [ite_bool_true _ hC] at hRef; cases hRef
      | false =>
        rw [ite_bool_false _ hC] at hRef
        let ⟨hLive, hInB, hAl⟩ := or3_false hC
        cases hM : h.mutability with
        | shared => rw [hM] at hRef; cases hRef
        | _ =>
          rw [hM] at hRef
          rw [ite_bool_false (Mutability.beq .mut .mut &&
            !Mutability.beq .mut .mut) rfl] at hRef
          cases hD : decodeValV2 profileV2TargetEndian
              (.vec (.int .i8 false))
              ((h.bytes.drop p.offsetBytes.toNat).take 24) with
          | error k => rw [hD] at hRef; cases hRef
          | ok od =>
            rw [hD] at hRef
            cases od with
            | none => cases hRef
            | some d =>
              let ⟨bp, c, l, hd⟩ := decodeVec_inv hD
              subst hd
              exact ⟨_, readVecFromRef_gen hP hF hLive hInB hAl hM hD hRef⟩

private theorem owned_len_le {m : MemoryState} {isMut : Bool} {bp : PtrVal}
    {cap len : UInt64}
    (hO : ownedHeapBufValidInMem m isMut (.int .i8 false) bp cap len =
      .ok ()) :
    len.toNat ≤ cap.toNat := by
  unfold ownedHeapBufValidInMem at hO
  cases hH : heapBufValidInMem m isMut (.int .i8 false) bp cap len with
  | error k => rw [hH] at hO; cases hO
  | ok u =>
    unfold heapBufValidInMem at hH
    cases hW : IntWidth.beq bp.width .isize with
    | false =>
      rw [ite_bool_true (!IntWidth.beq bp.width .isize)
        (by rw [hW]; rfl)] at hH
      cases hH
    | true =>
      rw [ite_bool_false (!IntWidth.beq bp.width .isize)
        (by rw [hW]; rfl)] at hH
      rw [layoutOfTyV2_u8] at hH; dsimp only at hH
      cases hLC : Nat.ble len.toNat cap.toNat with
      | false =>
        rw [ite_bool_true (!Nat.ble len.toNat cap.toNat)
          (by rw [hLC]; rfl)] at hH
        cases hH
      | true => exact Nat.le_of_ble_eq_true hLC

private theorem handle_ne_buf {L : List Allocation} {vaid baid : AllocId}
    {h b : Allocation} {off : Nat}
    (hFH : findAllocation vaid L = some h)
    (hAl : isAligned h off 3 = true)
    (hFB : findAllocation baid L = some b) (hAlB : b.alignLog2 = 0) :
    Nat.beq baid vaid = false := by
  cases hEq : Nat.beq baid vaid with
  | false => rfl
  | true =>
    rw [Nat.eq_of_beq_eq_true hEq, hFH] at hFB
    injection hFB with hHB
    unfold isAligned at hAl
    rw [hHB, hAlB] at hAl
    cases hAl

private theorem readBytes_zero_ok {m : MemoryState} {pl : MemPlace}
    {al : Nat} {old : List AllocByte}
    (h : readBytes m pl 0 al = .ok old) : old = [] := by
  unfold readBytes at h
  cases hF : findAllocation pl.allocId m.allocations with
  | none => rw [hF] at h; cases h
  | some a =>
    rw [hF] at h; dsimp only at h
    rw [ite_bool_true (Nat.beq 0 0) rfl] at h
    cases hA : (!isAligned a pl.offset al) with
    | true => rw [ite_bool_true _ hA] at h; cases h
    | false =>
      rw [ite_bool_false _ hA] at h
      injection h with h; exact h.symm

private theorem old_eq_take {m : MemoryState} {baid aid : AllocId}
    {b : Allocation} {n : Nat} {old : List AllocByte}
    (hFB : findAllocation baid m.allocations = some b)
    (hAid : n = 0 ∨ some baid = some aid)
    (h : readBytes m ⟨aid, 0⟩ n 0 = .ok old) :
    old = b.bytes.take n := by
  cases hAid with
  | inl h0 =>
    subst h0
    unfold readBytes at h
    cases hF : findAllocation aid m.allocations with
    | none => rw [hF] at h; cases h
    | some a =>
      rw [hF] at h; dsimp only at h
      rw [ite_bool_true (Nat.beq 0 0) rfl] at h
      cases hA : (!isAligned a 0 0) with
      | true => rw [ite_bool_true _ hA] at h; cases h
      | false =>
        rw [ite_bool_false _ hA] at h
        injection h with h
        rw [← h]; rfl
  | inr hA =>
    injection hA with hA
    subst hA
    exact readBytes_zero_off_eq hFB h

/-! ## `push_one` (body 4): The Three `push` Cases -/

private noncomputable def pushArgs (p : PtrVal) : List (MirTy × Val) :=
  [(.ref .mut (.vec (.int .i8 false)), .ptr p),
   (.int .i8 false,
    .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 1)⟩)]

private noncomputable def outMem (cm : CallerMemory) (m2 : MemoryState) :
    MemoryState :=
  entryMemoryWithCaller (extractReturnMemoryV2 cm m2 [])

private def PushPost (cm : CallerMemory) (p : PtrVal) (m2 : MemoryState) :
    Prop :=
  ∀ (v : VecModel) (aid : AllocId) (old : List AllocByte),
    readVecFromRef (entryMemoryWithCaller cm) true
      (.int .i8 false) p = .ok v →
    (v.len.toNat = 0 ∨ v.ptr.allocId = some aid) →
    readBytes (entryMemoryWithCaller cm)
      ⟨aid, v.ptr.offsetBytes.toNat⟩ v.len.toNat 0 = .ok old →
    ∃ (v' : VecModel) (aid' : AllocId),
      readVecFromRef (outMem cm m2) true (.int .i8 false) p = .ok v' ∧
      v'.len.toNat = v.len.toNat + 1 ∧
      v'.ptr.allocId = some aid' ∧
      readBytes (outMem cm m2)
        ⟨aid', v'.ptr.offsetBytes.toNat⟩ (v.len.toNat + 1) 0 =
        .ok (old ++ [.init 1 none])

private theorem outMem_allocs (cm : CallerMemory) (m2 : MemoryState) :
    (outMem cm m2).allocations =
      extractCallerAllocations m2 cm.allocations ++
        calleeLiveAllocations (allocIdsOf cm.allocations) [] m2.allocations :=
  rfl

private theorem nat_beq_symm_false {a b : Nat} (h : Nat.beq a b = false) :
    Nat.beq b a = false := by
  cases hE : Nat.beq b a with
  | false => rfl
  | true => rw [Nat.eq_of_beq_eq_true hE, Nat.beq_refl] at h; cases h

private theorem nat_beq_zero_of_pos {n : Nat} (h : 1 ≤ n) :
    Nat.beq n 0 = false := by
  cases n with
  | zero => cases h
  | succ k => rfl

private theorem push_inplace_case (cm : CallerMemory) (p : PtrVal)
    {vaid baid : AllocId} {h b : Allocation} {cap len : UInt64}
    (hP : p.allocId = some vaid)
    (hFH : findAllocation vaid cm.allocations = some h)
    (hLive : h.live = true)
    (hInB : isInBounds h p.offsetBytes.toNat 24 = true)
    (hAl : isAligned h p.offsetBytes.toNat 3 = true)
    (hMutH : h.mutability = .mut)
    (hR0 : readVecFromRef (entryMemoryWithCaller cm) true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ⟨some baid, 0, .isize⟩, cap, len⟩)
    (hFB : findAllocation baid cm.allocations = some b)
    (hLiveB : b.live = true) (hLenB : b.bytes.length = cap.toNat)
    (hAlB : b.alignLog2 = 0) (hMutB : b.mutability = .mut)
    (hInit : isSliceAllInit (b.bytes.take len.toNat) = true)
    (hCapB : cap.toNat < isizeMaxBytes)
    (hc : Nat.ble (len.toNat + 1) cap.toNat = true) :
    ∃ m2 : MemoryState,
      execCoreCallOpWithMem (entryMemoryWithCaller cm) .vecPush
        (pushArgs p) .unit = .ok (.unit, m2) ∧ PushPost cm p m2 := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  have hle : len.toNat + 1 ≤ cap.toNat := Nat.le_of_ble_eq_true hc
  have hlenB : len.toNat ≤ b.bytes.length := by
    rw [hLenB]; exact Nat.le_trans (Nat.le_succ _) hle
  have hNe := handle_ne_buf hFH hAl hFB hAlB
  have hBid : b.allocId = baid := find_some_id hFB
  have hHid : h.allocId = vaid := find_some_id hFH
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let L := cm.allocations
  let x : AllocByte := .init 1 none
  let b1 : Allocation := ⟨b.allocId, b.alignLog2, b.mutability,
    b.bytes.take len.toNat ++ [x] ++ b.bytes.drop (len.toNat + [x].length),
    b.live⟩
  have hWrBuf : writeBytes (entryMemoryWithCaller cm) ⟨baid, len.toNat⟩ 0
      [x] = .ok ⟨nid, replaceAllocation b1 L⟩ :=
    writeBytes_ok b rfl hFB hLiveB
      (by unfold isInBounds; rw [hLenB]; exact hc)
      (isAligned_align0 b len.toNat (by rw [hAlB]; rfl)) hMutB
  have hNeB1 : Nat.beq b1.allocId vaid = false := by
    show Nat.beq b.allocId vaid = false
    rw [hBid]; exact hNe
  have hFH1 : findAllocation vaid (replaceAllocation b1 L) = some h := by
    rw [find_replace_ne hNeB1]; exact hFH
  let E := vecBytes baid cap (UInt64.ofNat (len.toNat + 1))
  let off := p.offsetBytes.toNat
  let h1 : Allocation := ⟨h.allocId, h.alignLog2, h.mutability,
    h.bytes.take off ++ E ++ h.bytes.drop (off + 24), h.live⟩
  have hWrVec : writeVecToRef ⟨nid, replaceAllocation b1 L⟩ p
      ⟨.int .i8 false, ⟨some baid, 0, .isize⟩, cap,
        UInt64.ofNat (len.toNat + 1)⟩ =
      .ok ⟨nid, replaceAllocation h1 (replaceAllocation b1 L)⟩ :=
    writeVecToRef_gen hP hFH1 hLive hInB hAl hMutH
  let m2 : MemoryState := ⟨nid, replaceAllocation h1 (replaceAllocation b1 L)⟩
  refine ⟨m2, evalVecPush_inPlace hR0 push_val_enc push_val_chk hc hWrBuf
    hWrVec, ?_⟩
  intro v aid old hRv hAid hOld
  rw [hR0] at hRv; injection hRv with hv; subst hv
  have hOldEq : old = b.bytes.take len.toNat := old_eq_take hFB hAid hOld
  -- Lookups in the returned memory.
  have hFHh : findAllocation h.allocId L = some h := by rw [hHid]; exact hFH
  have hFBb : findAllocation b.allocId L = some b := by rw [hBid]; exact hFB
  have hF2h : findAllocation vaid m2.allocations = some h1 := by
    rw [← hHid]
    exact find_replace_eq (x := h1) (by rw [hHid]; exact hFH1)
  have hF2b : findAllocation baid m2.allocations = some b1 := by
    show findAllocation baid
      (replaceAllocation h1 (replaceAllocation b1 L)) = some b1
    have hNeH1 : Nat.beq h1.allocId baid = false := by
      show Nat.beq h.allocId baid = false
      rw [hHid]; exact nat_beq_symm_false hNe
    rw [find_replace_ne hNeH1, ← hBid]
    exact find_replace_eq (x := b1) hFBb
  have hIds : ∀ a, a ∈ m2.allocations → a.allocId ∈ allocIdsOf L :=
    ids_replace_sub
      (ids_replace_sub (fun a ha => allocId_mem_allocIdsOf ha)
        (allocId_mem_allocIdsOf (find_some_mem hFB) :
          b.allocId ∈ allocIdsOf L))
      (allocId_mem_allocIdsOf (find_some_mem hFH) :
        h.allocId ∈ allocIdsOf L)
  have hOM : (outMem cm m2).allocations = extractCallerAllocations m2 L := by
    rw [outMem_allocs, calleeLive_ids_in _ _ _ hIds, List.append_nil]
  have hFOh : findAllocation vaid (outMem cm m2).allocations = some h1 := by
    rw [hOM, find_extract_some hFH, hF2h]; rfl
  have hFOb : findAllocation baid (outMem cm m2).allocations = some b1 := by
    rw [hOM, find_extract_some hFB, hF2b]; rfl
  -- The rewritten handle.
  have hOff24 : off + 24 ≤ h.bytes.length := Nat.le_of_ble_eq_true hInB
  have hOffLe : off ≤ h.bytes.length :=
    Nat.le_trans (Nat.le_add_right off 24) hOff24
  have hLenH1 : h1.bytes.length = h.bytes.length :=
    (splice_length (E := E) hOff24 : _)
  have hInB1 : isInBounds h1 off 24 = true := by
    unfold isInBounds; rw [hLenH1]; exact hInB
  have hDec1 : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      ((h1.bytes.drop off).take 24) =
      .ok (some (.vec ⟨some baid, 0, .isize⟩ cap
        (UInt64.ofNat (len.toNat + 1)))) := by
    have hs : (h1.bytes.drop off).take 24 = E :=
      take_drop_splice (E := E) (D := h.bytes.drop (off + 24))
        (length_take_of_le hOffLe)
    rw [hs]; exact decode_vecBytes _ _ _
  -- The written buffer.
  have hlen1 : (UInt64.ofNat (len.toNat + 1)).toNat = len.toNat + 1 :=
    uint64_toNat_ofNat_of_lt
      (Nat.lt_of_le_of_lt hle (Nat.lt_trans hCapB isize_lt_u64))
  have hLenB1 : b1.bytes.length = b.bytes.length :=
    splice_length (E := [x]) (by rw [hLenB]; exact hle)
  have hAl0B1 : Nat.ble 0 b1.alignLog2 = true := by
    show Nat.ble 0 b.alignLog2 = true
    rw [hAlB]; rfl
  have hMutB1 : (true && !Mutability.beq b1.mutability .mut) = false := by
    show (true && !Mutability.beq b.mutability .mut) = false
    rw [hMutB]; rfl
  have hAlEqB1 : Nat.beq b1.alignLog2 0 = true := by
    show Nat.beq b.alignLog2 0 = true
    rw [hAlB]; rfl
  have hTake1 : b1.bytes.take (len.toNat + 1) =
      b.bytes.take len.toNat ++ [x] :=
    take_splice_succ hlenB
  have hOwned1 : ownedHeapBufValidInMem (outMem cm m2) true (.int .i8 false)
      ⟨some baid, 0, .isize⟩ cap (UInt64.ofNat (len.toNat + 1)) = .ok () :=
    ownedBuf_int_ok b1 layoutOfTyV2_u8 rfl
      (by rw [hlen1]; exact hc)
      (by rw [Nat.mul_one]; exact blt_of_lt hCapB)
      (nat_beq_zero_of_pos (Nat.le_trans (Nat.le_add_left 1 _) hle))
      hFOb hLiveB
      (by
        unfold isInBounds
        rw [hZ0, Nat.zero_add, hLenB1, hLenB, Nat.mul_one]
        exact Nat.ble_eq.mpr (Nat.le_refl _))
      (isAligned_align0 b1 _ hAl0B1) hMutB1
      (by
        rw [hlen1, Nat.mul_one]
        show isSliceAllInit (b1.bytes.take (len.toNat + 1)) = true
        rw [hTake1, isSliceAllInit_append, hInit]; rfl)
      (by rw [hLenB1, hLenB, Nat.mul_one]; exact Nat.beq_refl _)
      hAlEqB1
  have hReadOM : readVecFromRef (outMem cm m2) true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ⟨some baid, 0, .isize⟩, cap,
        UInt64.ofNat (len.toNat + 1)⟩ :=
    readVecFromRef_gen hP hFOh hLive hInB1 hAl hMutH hDec1 hOwned1
  have hBytesOM : readBytes (outMem cm m2) ⟨baid, UInt64.toNat 0⟩
      (len.toNat + 1) 0 = .ok (old ++ [x]) := by
    rw [readBytes_ok (a := b1) rfl hFOb hLiveB
      (by
        unfold isInBounds
        rw [hZ0, Nat.zero_add, hLenB1, hLenB]; exact hc)
      (isAligned_align0 b1 _ hAl0B1)]
    rw [hOldEq]
    exact congrArg Except.ok hTake1
  exact ⟨_, baid, hReadOM, hlen1, rfl, hBytesOM⟩

private theorem replace_singleton_same {a' y : Allocation}
    (h : a'.allocId = y.allocId) : replaceAllocation a' [y] = [a'] := by
  rw [replaceAllocation_cons_eq (by rw [h]; exact Nat.beq_refl _)]

private theorem push_growEmpty_case (cm : CallerMemory) (p : PtrVal)
    {vaid : AllocId} {h : Allocation} {bp : PtrVal}
    (hP : p.allocId = some vaid)
    (hFH : findAllocation vaid cm.allocations = some h)
    (hLive : h.live = true)
    (hInB : isInBounds h p.offsetBytes.toNat 24 = true)
    (hAl : isAligned h p.offsetBytes.toNat 3 = true)
    (hMutH : h.mutability = .mut)
    (hR0 : readVecFromRef (entryMemoryWithCaller cm) true (.int .i8 false) p =
      .ok ⟨.int .i8 false, bp, 0, 0⟩) :
    ∃ m2 : MemoryState,
      execCoreCallOpWithMem (entryMemoryWithCaller cm) .vecPush
        (pushArgs p) .unit = .ok (.unit, m2) ∧ PushPost cm p m2 := by
  have hHid : h.allocId = vaid := find_some_id hFH
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let L := cm.allocations
  have hLt : ∀ a, a ∈ L → a.allocId < nid :=
    fun a ha => mem_lt_entryNextAllocId cm 0 a ha
  let x : AllocByte := .init 1 none
  let nb0 : Allocation := ⟨nid, 0, .mut, List.replicate 8 .uninit, true⟩
  let nb1 : Allocation := ⟨nid, 0, .mut,
    (List.replicate 8 .uninit).take 0 ++ [x] ++
      (List.replicate 8 .uninit).drop (0 + [x].length), true⟩
  have hF0 : findAllocation nid (L ++ [nb0]) = some nb0 := by
    rw [find_append_none (find_none_of_lt hLt)]
    exact findAllocation_cons_eq (Nat.beq_refl _)
  have hWrBuf : writeBytes ⟨nid + 1, L ++ [nb0]⟩ ⟨nid, 0⟩ 0 [x] =
      .ok ⟨nid + 1, L ++ [nb1]⟩ := by
    rw [writeBytes_ok nb0 rfl hF0 rfl rfl rfl rfl]
    rw [replaceAllocation_append_of_lt (fun a ha => hLt a ha)]
    show (Except.ok ⟨nid + 1, L ++ replaceAllocation nb1 [nb0]⟩ :
      Except FaultKind MemoryState) = _
    rw [replace_singleton_same (a' := nb1) (y := nb0) rfl]
  have hFHh : findAllocation h.allocId L = some h := by rw [hHid]; exact hFH
  let off := p.offsetBytes.toNat
  let E := vecBytes nid 8 1
  let h1 : Allocation := ⟨h.allocId, h.alignLog2, h.mutability,
    h.bytes.take off ++ E ++ h.bytes.drop (off + 24), h.live⟩
  have hWrVec : writeVecToRef ⟨nid + 1, L ++ [nb1]⟩ p
      ⟨.int .i8 false, ⟨some nid, 0, .isize⟩, 8, 1⟩ =
      .ok ⟨nid + 1, replaceAllocation h1 (L ++ [nb1])⟩ :=
    writeVecToRef_gen hP (find_append_some hFH) hLive hInB hAl hMutH
  let m2 : MemoryState := ⟨nid + 1, replaceAllocation h1 (L ++ [nb1])⟩
  refine ⟨m2, evalVecPush_growEmpty hR0 push_val_enc push_val_chk hWrBuf
    hWrVec, ?_⟩
  intro v aid old hRv _ hOld
  rw [hR0] at hRv; injection hRv with hv; subst hv
  have hOldEq : old = [] := readBytes_zero_ok (by exact hOld)
  have hM2 : m2.allocations = replaceAllocation h1 L ++ [nb1] :=
    replace_append_found (x := h1) hFHh
  have hIds : ∀ a, a ∈ replaceAllocation h1 L → a.allocId ∈ allocIdsOf L :=
    ids_replace_sub (fun a ha => allocId_mem_allocIdsOf ha)
      (allocId_mem_allocIdsOf (find_some_mem hFH) :
        h.allocId ∈ allocIdsOf L)
  have hOM : (outMem cm m2).allocations =
      extractCallerAllocations m2 L ++ [nb1] := by
    rw [outMem_allocs, hM2, calleeLive_append, calleeLive_ids_in _ _ _ hIds,
      calleeLive_cons_keep rfl (natNotElem_callerIds cm 0) rfl]
    rfl
  have hF2h : findAllocation vaid m2.allocations = some h1 := by
    rw [hM2, ← hHid]
    exact find_append_some (find_replace_eq (x := h1) hFHh)
  have hFOh : findAllocation vaid (outMem cm m2).allocations = some h1 := by
    rw [hOM]
    exact find_append_some (by rw [find_extract_some hFH, hF2h]; rfl)
  have hFOn : findAllocation nid (outMem cm m2).allocations = some nb1 := by
    rw [hOM, find_append_none (find_extract_none (find_none_of_lt hLt))]
    exact findAllocation_cons_eq (Nat.beq_refl _)
  have hOff24 : off + 24 ≤ h.bytes.length := Nat.le_of_ble_eq_true hInB
  have hOffLe : off ≤ h.bytes.length :=
    Nat.le_trans (Nat.le_add_right off 24) hOff24
  have hLenH1 : h1.bytes.length = h.bytes.length :=
    (splice_length (E := E) hOff24 : _)
  have hInB1 : isInBounds h1 off 24 = true := by
    unfold isInBounds; rw [hLenH1]; exact hInB
  have hDec1 : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      ((h1.bytes.drop off).take 24) =
      .ok (some (.vec ⟨some nid, 0, .isize⟩ 8 1)) := by
    have hs : (h1.bytes.drop off).take 24 = E :=
      take_drop_splice (E := E) (D := h.bytes.drop (off + 24))
        (length_take_of_le hOffLe)
    rw [hs]; exact decode_vecBytes _ _ _
  have hOwned1 : ownedHeapBufValidInMem (outMem cm m2) true (.int .i8 false)
      ⟨some nid, 0, .isize⟩ 8 1 = .ok () :=
    ownedBuf_int_ok nb1 layoutOfTyV2_u8 rfl rfl rfl rfl hFOn rfl rfl rfl rfl
      rfl
  have hReadOM : readVecFromRef (outMem cm m2) true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ⟨some nid, 0, .isize⟩, 8, 1⟩ :=
    readVecFromRef_gen hP hFOh hLive hInB1 hAl hMutH hDec1 hOwned1
  have hBytesOM : readBytes (outMem cm m2) ⟨nid, UInt64.toNat 0⟩
      (UInt64.toNat 0 + 1) 0 = .ok (old ++ [x]) := by
    rw [readBytes_ok (a := nb1) rfl hFOn rfl rfl rfl, hOldEq]; rfl
  exact ⟨_, nid, hReadOM, rfl, rfl, hBytesOM⟩

private theorem push_growCopy_case (cm : CallerMemory) (p : PtrVal)
    {vaid baid : AllocId} {h b : Allocation} {cap : UInt64}
    (hP : p.allocId = some vaid)
    (hFH : findAllocation vaid cm.allocations = some h)
    (hLive : h.live = true)
    (hInB : isInBounds h p.offsetBytes.toNat 24 = true)
    (hAl : isAligned h p.offsetBytes.toNat 3 = true)
    (hMutH : h.mutability = .mut)
    (hR0 : readVecFromRef (entryMemoryWithCaller cm) true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ⟨some baid, 0, .isize⟩, cap, cap⟩)
    (hFB : findAllocation baid cm.allocations = some b)
    (hLiveB : b.live = true) (hLenB : b.bytes.length = cap.toNat)
    (hAlB : b.alignLog2 = 0) (hMutB : b.mutability = .mut)
    (hInit : isSliceAllInit (b.bytes.take cap.toNat) = true)
    (hCapNz : Nat.beq cap.toNat 0 = false)
    (hSafe : cap.toNat * 2 < isizeMaxBytes) :
    ∃ m2 : MemoryState,
      execCoreCallOpWithMem (entryMemoryWithCaller cm) .vecPush
        (pushArgs p) .unit = .ok (.unit, m2) ∧ PushPost cm p m2 := by
  have hZ0 : UInt64.toNat 0 = 0 := rfl
  have hc1 : 1 ≤ cap.toNat := by
    cases hC : cap.toNat with
    | zero => rw [hC] at hCapNz; cases hCapNz
    | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
  let c := cap.toNat
  let newCap := Nat.max (c * 2) (Nat.max (c + 1) 8)
  have hGrow : vecGrowCap 1 c (c + 1) = some newCap := growCap_ok hc1 hSafe
  have hc2 : c + 1 ≤ c * 2 := by
    rw [Nat.mul_two]; exact Nat.add_le_add_left hc1 c
  have hNewGe : c + 1 ≤ newCap :=
    Nat.le_trans (Nat.le_max_left (c + 1) 8) (Nat.le_max_right (c * 2) _)
  have hNewLt : newCap < isizeMaxBytes :=
    nat_max_lt hSafe (nat_max_lt (Nat.lt_of_le_of_lt hc2 hSafe) (by decide))
  have hNe := handle_ne_buf hFH hAl hFB hAlB
  have hBid : b.allocId = baid := find_some_id hFB
  have hHid : h.allocId = vaid := find_some_id hFH
  let nid := (entryMemoryWithCaller cm).nextAllocId
  let L := cm.allocations
  have hLt : ∀ a, a ∈ L → a.allocId < nid :=
    fun a ha => mem_lt_entryNextAllocId cm 0 a ha
  have hBLt : baid < nid := by rw [← hBid]; exact hLt b (find_some_mem hFB)
  let x : AllocByte := .init 1 none
  -- Read the old elements, then retire the old buffer.
  let oldBytes := (b.bytes.drop 0).take c
  have hOldLen : oldBytes.length = c :=
    length_take_of_le (by
      show c ≤ b.bytes.length
      rw [hLenB]; exact Nat.le_refl _)
  have hReadOld : readBytes (entryMemoryWithCaller cm) ⟨baid, 0⟩ c 0 =
      .ok oldBytes :=
    readBytes_ok hCapNz hFB hLiveB
      (by unfold isInBounds; rw [Nat.zero_add, hLenB]
          exact Nat.ble_eq.mpr (Nat.le_refl _))
      (isAligned_align0 b 0 (by rw [hAlB]; rfl))
  let bD : Allocation := ⟨b.allocId, b.alignLog2, b.mutability, b.bytes, false⟩
  have hRetire : deallocateStack (entryMemoryWithCaller cm) ⟨baid, 0⟩ =
      .ok ⟨nid, replaceAllocation bD L⟩ :=
    deallocateStack_ok b rfl hFB hLiveB hMutB
  let R := replaceAllocation bD L
  have hRLt : ∀ a, a ∈ R → a.allocId < nid :=
    lt_of_mem_replace hLt (by show b.allocId < nid; rw [hBid]; exact hBLt)
  -- Allocate the new buffer and copy the old elements.
  let rep := List.replicate (newCap * 1) AllocByte.uninit
  let nb0 : Allocation := ⟨nid, 0, .mut, rep, true⟩
  let nb1 : Allocation := ⟨nid, 0, .mut,
    rep.take 0 ++ oldBytes ++ rep.drop (0 + oldBytes.length), true⟩
  have hF0 : findAllocation nid (R ++ [nb0]) = some nb0 := by
    rw [find_append_none (find_none_of_lt hRLt)]
    exact findAllocation_cons_eq (Nat.beq_refl _)
  have hRepLen : rep.length = newCap * 1 := List.length_replicate
  have hWrOld : writeBytes ⟨nid + 1, R ++ [nb0]⟩ ⟨nid, 0⟩ 0 oldBytes =
      .ok ⟨nid + 1, R ++ [nb1]⟩ := by
    rw [writeBytes_ok nb0 (by rw [hOldLen]; exact hCapNz) hF0 rfl
      (by
        unfold isInBounds
        show Nat.ble (0 + oldBytes.length) rep.length = true
        rw [hOldLen, Nat.zero_add, hRepLen, Nat.mul_one]
        exact Nat.ble_eq.mpr (Nat.le_trans (Nat.le_succ c) hNewGe))
      rfl rfl]
    rw [replaceAllocation_append_of_lt (fun a ha => hRLt a ha)]
    show (Except.ok ⟨nid + 1, R ++ replaceAllocation nb1 [nb0]⟩ :
      Except FaultKind MemoryState) = _
    rw [replace_singleton_same (a' := nb1) (y := nb0) rfl]
  have hNb1Len : nb1.bytes.length = newCap * 1 := by
    have h1 := splice_length (A := rep) (E := oldBytes) (n := 0)
      (by rw [hOldLen, Nat.zero_add, hRepLen, Nat.mul_one]
          exact Nat.le_trans (Nat.le_succ c) hNewGe)
    rw [hRepLen] at h1; exact h1
  have hNb1Take : nb1.bytes.take c = oldBytes := by
    show (rep.take 0 ++ oldBytes ++ rep.drop (0 + oldBytes.length)).take c =
      oldBytes
    exact List.take_left' hOldLen
  -- Write the pushed element.
  let nb2 : Allocation := ⟨nid, 0, .mut,
    nb1.bytes.take c ++ [x] ++ nb1.bytes.drop (c + [x].length), true⟩
  have hF1 : findAllocation nid (R ++ [nb1]) = some nb1 := by
    rw [find_append_none (find_none_of_lt hRLt)]
    exact findAllocation_cons_eq (Nat.beq_refl _)
  have hCLe : c + 1 ≤ nb1.bytes.length := by
    rw [hNb1Len, Nat.mul_one]; exact hNewGe
  have hWrBuf : writeBytes ⟨nid + 1, R ++ [nb1]⟩ ⟨nid, c⟩ 0 [x] =
      .ok ⟨nid + 1, R ++ [nb2]⟩ := by
    rw [writeBytes_ok nb1 rfl hF1 rfl
      (by unfold isInBounds; exact Nat.ble_eq.mpr hCLe)
      (isAligned_align0 nb1 c rfl) rfl]
    rw [replaceAllocation_append_of_lt (fun a ha => hRLt a ha)]
    show (Except.ok ⟨nid + 1, R ++ replaceAllocation nb2 [nb1]⟩ :
      Except FaultKind MemoryState) = _
    rw [replace_singleton_same (a' := nb2) (y := nb1) rfl]
  -- Rewrite the handle.
  have hNeBD : Nat.beq bD.allocId vaid = false := by
    show Nat.beq b.allocId vaid = false
    rw [hBid]; exact hNe
  have hFHR : findAllocation vaid R = some h := by
    rw [find_replace_ne hNeBD]; exact hFH
  have hFHh : findAllocation h.allocId R = some h := by
    rw [hHid]; exact hFHR
  let off := p.offsetBytes.toNat
  let E := vecBytes nid (UInt64.ofNat newCap) (UInt64.ofNat (c + 1))
  let h1 : Allocation := ⟨h.allocId, h.alignLog2, h.mutability,
    h.bytes.take off ++ E ++ h.bytes.drop (off + 24), h.live⟩
  have hWrVec : writeVecToRef ⟨nid + 1, R ++ [nb2]⟩ p
      ⟨.int .i8 false, ⟨some nid, 0, .isize⟩, UInt64.ofNat newCap,
        UInt64.ofNat (c + 1)⟩ =
      .ok ⟨nid + 1, replaceAllocation h1 (R ++ [nb2])⟩ :=
    writeVecToRef_gen hP (find_append_some hFHR) hLive hInB hAl hMutH
  let m2 : MemoryState := ⟨nid + 1, replaceAllocation h1 (R ++ [nb2])⟩
  refine ⟨m2, evalVecPush_growCopy hR0 push_val_enc push_val_chk hCapNz
    hGrow hReadOld hRetire hWrOld hWrBuf hWrVec, ?_⟩
  intro v aid old hRv hAid hOld
  rw [hR0] at hRv; injection hRv with hv; subst hv
  have hOldEq : old = b.bytes.take c := old_eq_take hFB hAid hOld
  -- Lookups in the returned memory.
  have hM2 : m2.allocations = replaceAllocation h1 R ++ [nb2] :=
    replace_append_found (x := h1) hFHh
  have hBDin : bD.allocId ∈ allocIdsOf L :=
    (allocId_mem_allocIdsOf (find_some_mem hFB) : b.allocId ∈ allocIdsOf L)
  have hIds : ∀ a, a ∈ replaceAllocation h1 R → a.allocId ∈ allocIdsOf L :=
    ids_replace_sub
      (ids_replace_sub (fun a ha => allocId_mem_allocIdsOf ha) hBDin)
      (allocId_mem_allocIdsOf (find_some_mem hFH) :
        h.allocId ∈ allocIdsOf L)
  have hOM : (outMem cm m2).allocations =
      extractCallerAllocations m2 L ++ [nb2] := by
    rw [outMem_allocs, hM2, calleeLive_append, calleeLive_ids_in _ _ _ hIds,
      calleeLive_cons_keep rfl (natNotElem_callerIds cm 0) rfl]
    rfl
  have hF2h : findAllocation vaid m2.allocations = some h1 := by
    rw [hM2, ← hHid]
    exact find_append_some (find_replace_eq (x := h1) hFHh)
  have hFOh : findAllocation vaid (outMem cm m2).allocations = some h1 := by
    rw [hOM]
    exact find_append_some (by rw [find_extract_some hFH, hF2h]; rfl)
  have hFOn : findAllocation nid (outMem cm m2).allocations = some nb2 := by
    rw [hOM, find_append_none (find_extract_none (find_none_of_lt hLt))]
    exact findAllocation_cons_eq (Nat.beq_refl _)
  -- The rewritten handle.
  have hOff24 : off + 24 ≤ h.bytes.length := Nat.le_of_ble_eq_true hInB
  have hOffLe : off ≤ h.bytes.length :=
    Nat.le_trans (Nat.le_add_right off 24) hOff24
  have hLenH1 : h1.bytes.length = h.bytes.length :=
    (splice_length (E := E) hOff24 : _)
  have hInB1 : isInBounds h1 off 24 = true := by
    unfold isInBounds; rw [hLenH1]; exact hInB
  have hDec1 : decodeValV2 profileV2TargetEndian (.vec (.int .i8 false))
      ((h1.bytes.drop off).take 24) =
      .ok (some (.vec ⟨some nid, 0, .isize⟩ (UInt64.ofNat newCap)
        (UInt64.ofNat (c + 1)))) := by
    have hs : (h1.bytes.drop off).take 24 = E :=
      take_drop_splice (E := E) (D := h.bytes.drop (off + 24))
        (length_take_of_le hOffLe)
    rw [hs]; exact decode_vecBytes _ _ _
  -- The new buffer.
  have hNewLt64 : newCap < 2 ^ 64 := Nat.lt_trans hNewLt isize_lt_u64
  have hNewTo : (UInt64.ofNat newCap).toNat = newCap :=
    uint64_toNat_ofNat_of_lt hNewLt64
  have hLen1 : (UInt64.ofNat (c + 1)).toNat = c + 1 :=
    uint64_toNat_ofNat_of_lt (Nat.lt_of_le_of_lt hNewGe hNewLt64)
  have hNb2Len : nb2.bytes.length = newCap * 1 := by
    have h1 := splice_length (A := nb1.bytes) (E := [x]) (n := c) hCLe
    rw [hNb1Len] at h1; exact h1
  have hNb2Take : nb2.bytes.take (c + 1) = oldBytes ++ [x] := by
    have h1 := take_splice_succ (A := nb1.bytes) (x := x)
      (D := nb1.bytes.drop (c + [x].length))
      (Nat.le_trans (Nat.le_succ c) hCLe)
    have h2 : nb2.bytes.take (c + 1) = nb1.bytes.take c ++ [x] := h1
    rw [h2, hNb1Take]
  have hOwned1 : ownedHeapBufValidInMem (outMem cm m2) true (.int .i8 false)
      ⟨some nid, 0, .isize⟩ (UInt64.ofNat newCap) (UInt64.ofNat (c + 1)) =
      .ok () :=
    ownedBuf_int_ok nb2 layoutOfTyV2_u8 rfl
      (by rw [hLen1, hNewTo]; exact Nat.ble_eq.mpr hNewGe)
      (by rw [hNewTo, Nat.mul_one]; exact blt_of_lt hNewLt)
      (by rw [hNewTo]
          exact nat_beq_zero_of_pos (Nat.le_trans (Nat.le_add_left 1 c)
            hNewGe))
      hFOn rfl
      (by
        unfold isInBounds
        rw [hZ0, Nat.zero_add, hNb2Len, hNewTo]
        exact Nat.ble_eq.mpr (Nat.le_refl _))
      rfl rfl
      (by
        rw [hLen1, Nat.mul_one]
        show isSliceAllInit (nb2.bytes.take (c + 1)) = true
        rw [hNb2Take, isSliceAllInit_append]
        show (isSliceAllInit (b.bytes.take c) && true) = true
        rw [hInit]; rfl)
      (by rw [hNb2Len, hNewTo]; exact Nat.beq_refl _)
      rfl
  have hReadOM : readVecFromRef (outMem cm m2) true (.int .i8 false) p =
      .ok ⟨.int .i8 false, ⟨some nid, 0, .isize⟩, UInt64.ofNat newCap,
        UInt64.ofNat (c + 1)⟩ :=
    readVecFromRef_gen hP hFOh hLive hInB1 hAl hMutH hDec1 hOwned1
  have hBytesOM : readBytes (outMem cm m2) ⟨nid, UInt64.toNat 0⟩
      (c + 1) 0 = .ok (old ++ [x]) := by
    rw [readBytes_ok (a := nb2) rfl hFOn rfl
      (by
        unfold isInBounds
        rw [hZ0, Nat.zero_add, hNb2Len, Nat.mul_one]
        exact Nat.ble_eq.mpr hNewGe)
      rfl]
    rw [hOldEq]
    exact congrArg Except.ok hNb2Take
  exact ⟨_, nid, hReadOM, hLen1, rfl, hBytesOM⟩

private theorem mut_of_owned_flag {b : Allocation}
    (h : (true && !Mutability.beq b.mutability .mut) = false) :
    b.mutability = .mut := by
  cases hM : b.mutability with
  | shared => rw [hM] at h; cases h
  | _ => rfl

/-- `Vec::push(v, 1)` on a valid caller `&mut Vec<u8>` that cannot overflow
its capacity succeeds, and the returned memory holds the pushed `Vec`. -/
private theorem push_spec (cm : CallerMemory) (p : PtrVal)
    (_hCM : validCallerMemory cm = true)
    (hRef : refValidInMem (entryMemoryWithCaller cm) .mut
      (.vec (.int .i8 false)) (.ptr p) = .ok ())
    (hSafe : ∀ v : VecModel, readVecFromRef (entryMemoryWithCaller cm) true
      (.int .i8 false) p = .ok v → v.cap.toNat * 2 < isizeMaxBytes) :
    ∃ m2 : MemoryState,
      execCoreCallOpWithMem (entryMemoryWithCaller cm) .vecPush
        [(.ref .mut (.vec (.int .i8 false)), .ptr p),
         (.int .i8 false,
          .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 1)⟩)]
        .unit = .ok (.unit, m2) ∧
      ∀ (v : VecModel) (aid : AllocId) (old : List AllocByte),
        readVecFromRef (entryMemoryWithCaller cm) true
          (.int .i8 false) p = .ok v →
        (v.len.toNat = 0 ∨ v.ptr.allocId = some aid) →
        readBytes (entryMemoryWithCaller cm)
          ⟨aid, v.ptr.offsetBytes.toNat⟩ v.len.toNat 0 = .ok old →
        ∃ (v' : VecModel) (aid' : AllocId),
          readVecFromRef (entryMemoryWithCaller
              (extractReturnMemoryV2 cm m2 [])) true
            (.int .i8 false) p = .ok v' ∧
          v'.len.toNat = v.len.toNat + 1 ∧
          v'.ptr.allocId = some aid' ∧
          readBytes (entryMemoryWithCaller (extractReturnMemoryV2 cm m2 []))
            ⟨aid', v'.ptr.offsetBytes.toNat⟩ (v.len.toNat + 1) 0 =
            .ok (old ++ [.init 1 none]) := by
  let ⟨v0, hR0⟩ := readVec_of_refValid hRef
  let ⟨vaid, h, hP, hFH, hLive, hInB, hAl, hMutH, hv0, _, hO0⟩ :=
    readVec_inv hR0
  have hSafe0 := hSafe v0 hR0
  have hLC := owned_len_le hO0
  cases v0 with
  | mk e bp cap len =>
    injection hv0 with he
    subst he
    dsimp only at hSafe0 hLC hO0
    cases hc : Nat.ble (len.toNat + 1) cap.toNat with
    | true =>
      have hle := Nat.le_of_ble_eq_true hc
      let ⟨baid, b, hbp, hFB, hLiveB, hLenB, hAlB, hMutB, _, hCapB, hInit⟩ :=
        owned_u8_inv hO0
          (nat_beq_zero_of_pos (Nat.le_trans (Nat.le_add_left 1 _) hle))
      subst hbp
      exact push_inplace_case cm p hP hFH hLive hInB hAl hMutH hR0 hFB hLiveB
        hLenB hAlB (mut_of_owned_flag hMutB) hInit hCapB hc
    | false =>
      have hNot : ¬ (len.toNat + 1 ≤ cap.toNat) := by
        intro hle; rw [Nat.ble_eq.mpr hle] at hc; cases hc
      have hlc : len.toNat = cap.toNat :=
        Nat.le_antisymm hLC (Nat.le_of_lt_succ (Nat.not_le.mp hNot))
      have hlenEq : len = cap := uint64_eq_of_toNat_eq hlc
      subst hlenEq
      cases hz : Nat.beq len.toNat 0 with
      | true =>
        have hz0 : len = 0 := uint64_eq_of_toNat_eq (Nat.eq_of_beq_eq_true hz)
        subst hz0
        exact push_growEmpty_case cm p hP hFH hLive hInB hAl hMutH hR0
      | false =>
        let ⟨baid, b, hbp, hFB, hLiveB, hLenB, hAlB, hMutB, _, _, hInit⟩ :=
          owned_u8_inv hO0 hz
        subst hbp
        exact push_growCopy_case cm p hP hFH hLive hInB hAl hMutH hR0 hFB
          hLiveB hLenB hAlB (mut_of_owned_flag hMutB) hInit hz hSafe0

/-- A program whose initial state chains to `.done o₀` has no other terminal
behavior. -/
private theorem behaviorV2_det {p : Program} {q : Query} {s₀ : State}
    {o₀ o : TerminalOut}
    (hInit : initStateV2 p q = .ok s₀)
    (hChain : ChainStepV2 p s₀ (.done o₀))
    (hB : BehaviorV2 p q o) : o = o₀ := by
  unfold BehaviorV2 ReachesResultV2 at hB
  rw [hInit] at hB
  let ⟨s, hReach, _, _, hEval⟩ := hB
  have hEval' : evalStepV2 p s = .done o := hEval
  cases reachesV2_chainStepV2 rfl hChain hReach with
  | base hDone =>
    rw [hDone] at hEval'
    injection hEval' with h
    exact h.symm
  | step hStep _ => rw [hStep] at hEval'; cases hEval'

private theorem checkArgsMatchV2_refMutVec_inv {args : List Val}
    (h : checkArgsMatchV2 args [.ref .mut (.vec (.int .i8 false))] = true) :
    ∃ p : PtrVal, args = [.ptr p] ∧ p.width = .isize := by
  cases args with
  | nil => cases h
  | cons a0 rest =>
    cases rest with
    | cons _ _ =>
      unfold checkArgsMatchV2 at h
      cases h0 : checkValV2 a0 (.ref .mut (.vec (.int .i8 false))) with
      | false => rw [h0] at h; cases h
      | true => rw [h0] at h; cases h
    | nil =>
      unfold checkArgsMatchV2 at h
      cases h0 : checkValV2 a0 (.ref .mut (.vec (.int .i8 false))) with
      | false => rw [h0] at h; cases h
      | true =>
        unfold checkValV2 at h0
        cases a0 with
        | ptr p =>
          cases p with
          | mk pAid pOff pW =>
            cases pW with
            | i8 | i16 | i32 | i64 | i128 => cases h0
            | isize => exact ⟨⟨pAid, pOff, .isize⟩, rfl, rfl⟩
        | scalar _ | bool _ | char _ | ordering _ | enumVal _ _ | unit
        | slicePtr _ _ | rangeTo _ | rangeFrom _ | vec _ _ _ | tuple _
        | bytes _ | range _ _ | array _ => cases h0
        | optionVal o => cases o <;> cases h0
        | boxPtr _ optL => cases optL <;> cases h0

private theorem evalStepV2_assign_reborrow_vec_mut {p : Program}
    {frame : FrameState} {mem : MemoryState} {cm : CallerMemory}
    {body : Body} {bb : BasicBlock} {dst src : LocalId}
    {pv : PtrVal} {locals2 : List LocalSlot}
    (hB : Trusted.MirSemantics.getElem? p.bodies frame.defId = some body)
    (hBB :
      Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx =
      some (.assign ⟨dst, []⟩ (.ref .mut ⟨src, [.deref]⟩)))
    (hDstTy : placeStaticTyV2 body.locals ⟨dst, []⟩ =
      some (.ref .mut (.vec (.int .i8 false))))
    (hSrcTy : Trusted.MirSemantics.getElem? body.locals src =
      some (.ref .mut (.vec (.int .i8 false))))
    (hSlot : Trusted.MirSemantics.getElem? frame.locals src =
      some (.immediate (some (.ptr pv))))
    (hRef : refValidInMem mem .mut (.vec (.int .i8 false)) (.ptr pv) =
      .ok ())
    (hWp : writePlaceV2 body.locals frame.locals mem ⟨dst, []⟩
      (.ref .mut (.vec (.int .i8 false))) (.ptr pv) =
      .ok (locals2, mem)) :
    evalStepV2 p ⟨[frame], cm, mem⟩ =
      .step ⟨[{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 }],
        cm, mem⟩ := by
  rw [writePlaceV2_local] at hWp
  rw [evalStepV2_stmt rfl hB hBB hSt]
  unfold evalStatementV2; dsimp only; rw [hDstTy]; dsimp only
  unfold resolvePlaceDestV2; dsimp only
  unfold evalRvalueV2 evalRefRvalueV2; dsimp only
  rw [hSrcTy, hSlot]; dsimp only
  rw [ite_bool_false (Mutability.beq .mut .shared &&
      Mutability.beq .mut .mut) rfl]
  rw [ite_bool_false (!MirTy.beq (.ref .mut (.vec (.int .i8 false)))
      (.ref .mut (.vec (.int .i8 false)))) rfl]
  rw [hRef]; dsimp only; rw [hWp]; rfl

private theorem body4_ok (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_4 q)
    (hSafe : Spec.pushOneSafety q) :
    WellFormedV2 (entryProgForBody Captured.program 4) q ∧
    ∀ (out : Out),
      BehaviorV2 (entryProgForBody Captured.program 4) q
        (TerminalOut.returned out) →
      match q.args with
      | [.ptr selfPtr] =>
        ∀ (v : VecModel) (aid : AllocId) (old : List AllocByte),
          readVecFromRef (entryMemoryWithCaller q.callerMem) true
            (.int .i8 false) selfPtr = .ok v →
          (v.len.toNat = 0 ∨ v.ptr.allocId = some aid) →
          readBytes (entryMemoryWithCaller q.callerMem)
            ⟨aid, v.ptr.offsetBytes.toNat⟩ v.len.toNat 0 = .ok old →
          ∃ (v' : VecModel) (aid' : AllocId),
            readVecFromRef (entryMemoryWithCaller out.callerMem) true
              (.int .i8 false) selfPtr = .ok v' ∧
            v'.len.toNat = v.len.toNat + 1 ∧
            v'.ptr.allocId = some aid' ∧
            readBytes (entryMemoryWithCaller out.callerMem)
              ⟨aid', v'.ptr.offsetBytes.toNat⟩ (v.len.toNat + 1) 0 =
              .ok (old ++ [.init 1 none])
      | _ => False := by
  rcases hValid with ⟨hCM, hArgs, hRefs, hSpans⟩
  have hArgs' : checkArgsMatchV2 q.args
      [.ref .mut (.vec (.int .i8 false))] = true := hArgs
  let ⟨p, hQArgs, hPW⟩ := checkArgsMatchV2_refMutVec_inv hArgs'
  let m0 : MemoryState := entryMemoryWithCaller q.callerMem
  have hRefsList : refsValidInMemList m0
      [.ref .mut (.vec (.int .i8 false))] [.ptr p] = true := by
    rw [← hQArgs]; exact hRefs
  unfold refsValidInMemList refsValidInMem at hRefsList
  have hRef : refValidInMem m0 .mut (.vec (.int .i8 false)) (.ptr p) =
      .ok () := by
    cases hR : refValidInMem m0 .mut (.vec (.int .i8 false)) (.ptr p) with
    | error _ => rw [hR] at hRefsList; cases hRefsList
    | ok u => cases u; rfl
  have hSafe' : ∀ v : VecModel,
      readVecFromRef m0 true (.int .i8 false) p = .ok v →
      v.cap.toNat * 2 < isizeMaxBytes := by
    unfold Spec.pushOneSafety at hSafe
    rw [hQArgs] at hSafe
    exact hSafe
  let ⟨m2, hCall, hPost⟩ := push_spec q.callerMem p hCM hRef hSafe'
  have hStatic : BodyStaticAdmittedV2 (entryProgForBody Captured.program 4)
      Captured.body_4 = true := by
    unfold BodyStaticAdmittedV2; decide
  have hInit := initStateV2_ok_of (p := entryProgForBody Captured.program 4)
    (body := Captured.body_4) rfl hStatic ⟨hCM, hArgs, hRefs, hSpans⟩
  rw [hQArgs] at hInit
  let pV : Option Val := some (.ptr p)
  let oneV : Val :=
    .scalar ⟨.i8, false, truncateBits .i8 (BitVec.ofNat 128 1)⟩
  let ls0 : List LocalSlot :=
    [.immediate (some .unit), .immediate pV, .dead, .dead]
  let ls2 : List LocalSlot :=
    [.immediate (some .unit), .immediate pV, .immediate (some .unit),
     .immediate none]
  let ls3 : List LocalSlot :=
    [.immediate (some .unit), .immediate pV, .immediate (some .unit),
     .immediate pV]
  let ls4 : List LocalSlot :=
    [.immediate (some .unit), .immediate pV, .immediate (some .unit),
     .immediate none]
  let ls7 : List LocalSlot :=
    [.immediate (some .unit), .immediate pV, .dead, .dead]
  have hInitSt :
      initLocalsLoop Captured.body_4 [.ptr p] 0 Captured.body_4.locals =
        ls0 := rfl
  rw [hInitSt] at hInit
  have hInit0 : initStateV2 (entryProgForBody Captured.program 4) q =
      .ok ⟨[⟨4, 0, 0, ls0, none, none, none⟩], q.callerMem, m0⟩ := hInit
  have c02 : ChainTo (entryProgForBody Captured.program 4)
      ⟨[⟨4, 0, 0, ls0, none, none, none⟩], q.callerMem, m0⟩
      ⟨[⟨4, 0, 2, ls2, none, none, none⟩], q.callerMem, m0⟩ :=
    ChainTo.step rfl (ChainTo.step rfl (ChainTo.refl _))
  have hChkP : checkValV2 (.ptr p) (.ref .mut (.vec (.int .i8 false))) =
      true := by
    unfold checkValV2; rw [hPW]; rfl
  have hB02 : evalStepV2 (entryProgForBody Captured.program 4)
      ⟨[⟨4, 0, 2, ls2, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨4, 0, 3, ls3, none, none, none⟩], q.callerMem, m0⟩ :=
    evalStepV2_assign_reborrow_vec_mut rfl rfl rfl rfl rfl rfl hRef
      (writePlaceV2_imm_ok hChkP rfl rfl)
  have hEvalArgs : evalArgOperandsV2 Captured.body_4.locals ls3 m0
      [.move ⟨3, []⟩,
       .constant ⟨.int .i8 false, .scalar (BitVec.ofNat 128 1)⟩] =
      .ok ([(.ref .mut (.vec (.int .i8 false)), .ptr p),
        (.int .i8 false, oneV)], ls4, m0) := rfl
  have hB0t : evalStepV2 (entryProgForBody Captured.program 4)
      ⟨[⟨4, 0, 3, ls3, none, none, none⟩], q.callerMem, m0⟩ =
      .step ⟨[⟨4, 1, 0,
        [.immediate (some .unit), .immediate pV, .immediate (some .unit),
         .immediate none], none, none, none⟩], q.callerMem, m2⟩ :=
    evalStepV2_coreCall rfl rfl rfl rfl rfl rfl hEvalArgs hCall
      (writePlaceV2_imm_ok rfl rfl rfl)
  have c1t : ChainTo (entryProgForBody Captured.program 4)
      ⟨[⟨4, 1, 0,
        [.immediate (some .unit), .immediate pV, .immediate (some .unit),
         .immediate none], none, none, none⟩], q.callerMem, m2⟩
      ⟨[⟨4, 1, 3, ls7, none, none, none⟩], q.callerMem, m2⟩ :=
    ChainTo.step rfl (ChainTo.step rfl (ChainTo.step rfl (ChainTo.refl _)))
  have hRet : evalStepV2 (entryProgForBody Captured.program 4)
      ⟨[⟨4, 1, 3, ls7, none, none, none⟩], q.callerMem, m2⟩ =
      .done (.returned ⟨.unit, extractReturnMemoryV2 q.callerMem m2 []⟩) :=
    evalStepV2_return_imm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hChain : ChainStepV2 (entryProgForBody Captured.program 4)
      ⟨[⟨4, 0, 0, ls0, none, none, none⟩], q.callerMem, m0⟩
      (.done (.returned ⟨.unit, extractReturnMemoryV2 q.callerMem m2 []⟩)) :=
    chainTo_chainStepV2 c02
      (ChainStepV2.step hB02
        (ChainStepV2.step hB0t
          (chainTo_chainStepV2 c1t (.base hRet))))
  have hRes := spec_and_behaviorV2_of_chainStep hInit0 hChain
  refine ⟨hRes.1, ?_⟩
  intro out hB
  have hO := behaviorV2_det hInit0 hChain hB
  injection hO with hOut
  subst hOut
  rw [hQArgs]
  exact hPost

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      cases hBody
      refine ⟨rfl, by unfold BodyStaticAdmittedV2; decide, ?_⟩
      intro q hValid _
      exact (body0_ok q hValid).1
    | succ d1 =>
      cases d1 with
      | zero =>
        cases hBody
        refine ⟨rfl, by unfold BodyStaticAdmittedV2; decide, ?_⟩
        intro q hValid _
        exact (body1_ok q hValid).1
      | succ d2 =>
        cases d2 with
        | zero =>
          cases hBody
          refine ⟨rfl, by unfold BodyStaticAdmittedV2; decide, ?_⟩
          intro q hValid hSafe
          exact body2_ok q hValid (hSafe rfl)
        | succ d3 =>
          cases d3 with
          | zero =>
            cases hBody
            refine ⟨rfl, by unfold BodyStaticAdmittedV2; decide, ?_⟩
            intro q hValid _
            let ⟨_, _, _, hQ, _, _⟩ :=
              checkArgsMatchV2_slice_boxSlice_inv hValid.2.1
            have h3 := body3_ok q hValid
            rw [hQ] at h3
            dsimp only at h3
            rcases h3 with ⟨_, _, _, hWf, _⟩
            exact hWf
          | succ d4 =>
            cases d4 with
            | zero =>
              cases hBody
              refine ⟨rfl, by unfold BodyStaticAdmittedV2; decide, ?_⟩
              intro q hValid hSafe
              exact (body4_ok q hValid (hSafe rfl)).1
            | succ _ =>
              cases hBody
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hValid
      exact (body0_ok q hValid).2
    · intro q hValid
      exact (body1_ok q hValid).2
    · intro q hValid hSafe
      exact body2_ok q hValid hSafe
    · intro q hValid
      exact body3_ok q hValid
    · intro q hValid hSafe
      exact body4_ok q hValid hSafe


end Proof
