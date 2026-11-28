-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Char.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Ops
import Trusted.MirSemantics.Enum
import Trusted.MirSemantics.State
import Trusted.MirSemantics.Step
import Trusted.MirSemantics.Boundary
import Anneal.MiniRust.Syntax
import Anneal.MiniRust.Memory
import Anneal.MiniRust.Machine
import Anneal.MiniRust.Translate
import Anneal.MiniRust.Relation
import Anneal.MiniRust.OpSim

namespace Anneal.MiniRust

open Trusted.MirAst
open Trusted.MirSemantics

/-!
# Initialization, Single-Step, and Trace Simulation (`Anneal.MiniRust.StepSim`)

Proves:
1. Entry initialization (`init_stateRel`): for any admitted `(p, q)`, both
   `initState p q` and `initMrMachine p q` succeed, and MiniRust steps through
   `initBlock` to a state coupled by `StateRel exact p s₀ m₁`.
2. Frame storage/memory/teardown lemmas (`storageDeadFrame_sim`,
   `storageLiveFrame_sim`, `deallocateAllLocals_spec`, `writePlace_sim`).
3. Single-step lockstep simulation (`evalStep_sim_core`) covering all admitted
   statements (`.nop`, `.storageLive`, `.storageDead`, `.assign`) and
   terminators (`.goto`, `.return_`, `.unreachable`, `.switchInt`).
4. Multi-step forward simulation (`MiniRustAdmitted`) and exact bidirectional
   outcome/fault/divergence equivalence (`MiniRustExactAdmitted`), purely
   constructively (no `Classical.choice`).
-/

/-! ## List and `initLocalsLoop` / `checkArgsMatch` Helper Lemmas -/

theorem listGet?_drop {α : Type} (xs : List α) (k i : Nat) :
    listGet? (xs.drop k) i = listGet? xs (k + i) := by
  induction xs generalizing k i with
  | nil =>
    cases k with
    | zero => rfl
    | succ _ => rfl
  | cons x xs ih =>
    cases k with
    | zero => rw [Nat.zero_add]; rfl
    | succ k' =>
      dsimp only [List.drop]
      rw [Nat.succ_add]
      exact ih k' i

theorem listGet?_take_of_lt {α : Type} (xs : List α) (n i : Nat) (h : i < n) :
    listGet? (xs.take n) i = listGet? xs i := by
  induction xs generalizing n i with
  | nil =>
    cases n with
    | zero => cases h
    | succ _ => rfl
  | cons x xs ih =>
    cases n with
    | zero => cases h
    | succ n' =>
      cases i with
      | zero => rfl
      | succ i' =>
        dsimp only [List.take, listGet?]
        exact ih n' i' (Nat.lt_of_succ_lt_succ h)

theorem checkArgsMatch_length (args : List Val) (tys : List MirTy)
    (h : checkArgsMatch args tys = true) :
    args.length = tys.length := by
  induction args generalizing tys with
  | nil =>
    cases tys with
    | nil => rfl
    | cons _ _ => cases h
  | cons v vs ih =>
    cases tys with
    | nil => cases h
    | cons t ts =>
      dsimp only [checkArgsMatch] at h
      cases hc : checkVal v t with
      | false => rw [hc] at h; cases h
      | true =>
        rw [hc] at h
        dsimp only [List.length]
        exact congrArg Nat.succ (ih ts h)

theorem checkArgsMatch_getElem? (args : List Val) (tys : List MirTy)
    (h : checkArgsMatch args tys = true) (i : Nat) (v : Val) (ty : MirTy)
    (hv : listGet? args i = some v) (ht : listGet? tys i = some ty) :
    checkVal v ty = true := by
  induction args generalizing tys i with
  | nil => cases hv
  | cons a as ih =>
    cases tys with
    | nil => cases h
    | cons t ts =>
      dsimp only [checkArgsMatch] at h
      cases hc : checkVal a t with
      | false => rw [hc] at h; cases h
      | true =>
        rw [hc] at h
        cases i with
        | zero =>
          dsimp only [listGet?] at hv ht
          injection hv with hva; subst hva
          injection ht with htt; subst htt
          exact hc
        | succ k => exact ih ts h k hv ht

theorem list_length_take_of_le {α : Type} (xs : List α) (n : Nat) (h : n ≤ xs.length) :
    (xs.take n).length = n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ _ => cases h
  | cons _ xs ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp only [List.take, List.length]
      exact congrArg Nat.succ (ih k (Nat.le_of_succ_le_succ h))

theorem initLocalsLoop_length (body : Body) (args : List Val) (start : Nat)
    (tys : List MirTy) :
    (initLocalsLoop body args start tys).length = tys.length := by
  induction tys generalizing start with
  | nil => rfl
  | cons _ _ ih =>
    dsimp only [initLocalsLoop, List.length]
    exact congrArg Nat.succ (ih (start + 1))

theorem initLocalsLoop_getElem? (body : Body) (args : List Val) (start : Nat)
    (tys : List MirTy) (offset : Nat) (ty : MirTy)
    (h : listGet? tys offset = some ty) :
    listGet? (initLocalsLoop body args start tys) offset =
      some (let idx := start + offset
        if Nat.beq idx 0 then
          liveUninitSlot ty
        else if Nat.ble idx body.argumentCount then
          match Trusted.MirSemantics.getElem? args (idx - 1) with
          | some v => .immediate (some v)
          | none => .dead
        else if hasStorageAnnotation body idx then
          .dead
        else
          liveUninitSlot ty) := by
  induction tys generalizing start offset with
  | nil => cases h
  | cons t ts ih =>
    cases offset with
    | zero =>
      dsimp only [listGet?] at h
      injection h with ht; subst ht
      dsimp only [initLocalsLoop, listGet?]
      rw [Nat.add_zero]
      rfl
    | succ k =>
      dsimp only [listGet?] at h
      dsimp only [initLocalsLoop, listGet?]
      have hrec := ih (start + 1) k h
      have hidx : start + 1 + k = start + Nat.succ k := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [hidx] at hrec
      exact hrec

theorem alwaysLiveTempsAux_spec (body : Body) :
    ∀ (start : Nat) (tys : List MirTy),
      (∀ k, k ∈ alwaysLiveTempsAux body start tys →
        start ≤ k ∧ k < start + tys.length ∧
        body.argumentCount < k ∧ hasStorageAnnotation body k = false) ∧
      natListPairwiseNe (alwaysLiveTempsAux body start tys) = true ∧
      (∀ offset, offset < tys.length →
        body.argumentCount < start + offset →
        hasStorageAnnotation body (start + offset) = false →
        (start + offset) ∈ alwaysLiveTempsAux body start tys) := by
  intro start tys
  induction tys generalizing start with
  | nil =>
    refine ⟨fun _ h => (by cases h), rfl, fun _ hlt _ _ => (by cases hlt)⟩
  | cons t ts ih =>
    cases ih (start + 1) with
    | intro hmem hrest =>
      cases hrest with
      | intro hpw hcomp =>
        dsimp only [alwaysLiveTempsAux]
        have hlenEq : start + (t :: ts).length = start + 1 + ts.length := by
          dsimp only [List.length]; rw [Nat.add_assoc, Nat.add_comm 1 ts.length]
        cases hc : Nat.blt body.argumentCount start && !hasStorageAnnotation body start with
        | false =>
          rw [if_false_eq_true]
          refine ⟨fun k hk => ?_, hpw, fun offset hlt hgt hno => ?_⟩
          · cases hmem k hk with
            | intro hge h1 =>
              refine ⟨Nat.le_trans (Nat.le_succ _) hge, ?_, h1.2⟩
              rw [hlenEq]; exact h1.1
          · cases offset with
            | zero =>
              rw [Nat.add_zero] at hgt hno
              rw [nat_blt_eq_true_of_lt hgt, hno] at hc; cases hc
            | succ k =>
              have hidx : start + Nat.succ k = start + 1 + k := by
                rw [Nat.add_assoc, Nat.add_comm 1 k]
              rw [hidx] at hgt hno; rw [hidx]
              exact hcomp k (Nat.lt_of_succ_lt_succ hlt) hgt hno
        | true =>
          rw [if_true_eq_true]
          have hgtStart : body.argumentCount < start := by
            cases h1 : Nat.blt body.argumentCount start with
            | false => rw [h1] at hc; cases hc
            | true => exact nat_lt_of_blt_eq_true h1
          have hnoStart : hasStorageAnnotation body start = false := by
            cases h2 : hasStorageAnnotation body start with
            | false => rfl
            | true => rw [h2, Bool.not_true, Bool.and_false] at hc; cases hc
          have hnotElem : natNotElem start (alwaysLiveTempsAux body (start + 1) ts) = true := by
            have hgen : ∀ (xs : List Nat),
                (∀ k, k ∈ xs → start + 1 ≤ k) → natNotElem start xs = true := by
              intro xs
              induction xs with
              | nil => intro _; rfl
              | cons y ys ihy =>
                intro hall
                dsimp only [natNotElem]
                have hgeY : start + 1 ≤ y := hall y (List.Mem.head _)
                have hneY : Nat.beq start y = false := by
                  cases hb : Nat.beq start y with
                  | false => rfl
                  | true =>
                    have heq := Nat.eq_of_beq_eq_true hb; subst heq
                    exact False.elim (Nat.not_lt_of_ge hgeY (Nat.lt_succ_self start))
                rw [hneY]
                exact ihy (fun k hk => hall k (List.Mem.tail _ hk))
            exact hgen _ (fun k hk => (hmem k hk).1)
          refine ⟨fun k hk => ?_, ?_, fun offset hlt hgt hno => ?_⟩
          · cases hk with
            | head =>
              refine ⟨Nat.le_refl _, ?_, hgtStart, hnoStart⟩
              rw [hlenEq]
              exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
            | tail _ htl =>
              cases hmem k htl with
              | intro hge h1 =>
                refine ⟨Nat.le_trans (Nat.le_succ _) hge, ?_, h1.2⟩
                rw [hlenEq]; exact h1.1
          · dsimp only [natListPairwiseNe]; rw [hnotElem, hpw]; rfl
          · cases offset with
            | zero => rw [Nat.add_zero]; exact List.Mem.head _
            | succ k =>
              have hidx : start + Nat.succ k = start + 1 + k := by
                rw [Nat.add_assoc, Nat.add_comm 1 k]
              rw [hidx] at hgt hno; rw [hidx]
              exact List.Mem.tail _ (hcomp k (Nat.lt_of_succ_lt_succ hlt) hgt hno)

/-! ## Core Frame-Level Storage, Teardown, and WritePlace Lemmas -/

/-- Deallocate all locals in `lmap` when every entry is live in `mem` with an
`AllocId` distinct from `callerRetId` and pairwise distinct across `lmap`. -/
theorem deallocateAllLocals_spec (func : MrFunction) (retTy : MrType)
    (callerRetPtr : ThinPtr) (callerRetId : AllocId) (callerRetData : List AbstractByte) :
    ∀ (lmap : LocalMap) (mem : MrMemory),
      LocalMapNoDup lmap →
      AllocLiveAt mem retTy callerRetPtr callerRetId callerRetData →
      (∀ k ptr, localMapGet? k lmap = some ptr →
        ∃ ty id data,
          listGet? func.locals k = some ty ∧
          AllocLiveAt mem ty ptr id data ∧
          id ≠ callerRetId ∧
          ∀ j ptr' id',
            k ≠ j →
            localMapGet? j lmap = some ptr' →
            ptr'.allocId = some id' →
            id ≠ id') →
      ∃ mem',
        deallocateAllLocals func mem lmap = .ok mem' ∧
        AllocLiveAt mem' retTy callerRetPtr callerRetId callerRetData := by
  intro lmap
  induction lmap with
  | nil =>
    intro mem _ hret _
    exact ⟨mem, rfl, hret⟩
  | cons entry rest ih =>
    cases entry with
    | mk k ptr =>
      intro mem hnd hret hall
      cases hnd with
      | intro hfresh hndRest =>
        have hgetK : localMapGet? k ((k, ptr) :: rest) = some ptr := by
          dsimp only [localMapGet?]; rw [Nat.beq_refl, if_true_eq_true]
        cases hall k ptr hgetK with
        | intro ty h1 => cases h1 with | intro id h2 => cases h2 with
          | intro data h3 =>
            cases h3 with
            | intro hlocK h4 => cases h4 with
              | intro hliveK h5 => cases h5 with
                | intro hneCaller hdisjK =>
                  dsimp only [deallocateAllLocals]
                  rw [hlocK]; dsimp only
                  cases allocLiveAt_deallocate mem ty ptr id data hliveK with
                  | intro mem1 hdealloc =>
                    rw [hdealloc.1]; dsimp only
                    have hret1 : AllocLiveAt mem1 retTy callerRetPtr callerRetId callerRetData :=
                      hdealloc.2 retTy callerRetPtr callerRetId callerRetData
                        (fun h => hneCaller h.symm) hret
                    apply ih mem1 hndRest hret1
                    intro j ptrJ hgetJ
                    have hneKJ : k ≠ j := by
                      intro heq; subst heq; rw [hfresh] at hgetJ; cases hgetJ
                    have hgetJCons : localMapGet? j ((k, ptr) :: rest) = some ptrJ := by
                      dsimp only [localMapGet?]
                      have hneB : Nat.beq k j = false := by
                        cases hb : Nat.beq k j with
                        | false => rfl
                        | true => exact False.elim (hneKJ (Nat.eq_of_beq_eq_true hb))
                      rw [hneB, if_false_eq_true]; exact hgetJ
                    cases hall j ptrJ hgetJCons with
                    | intro tyJ hJ1 => cases hJ1 with | intro idJ hJ2 => cases hJ2 with
                      | intro dataJ hJ3 =>
                        have hneId : id ≠ idJ := hdisjK j ptrJ idJ hneKJ hgetJCons hJ3.2.1.1
                        refine ⟨tyJ, idJ, dataJ, hJ3.1,
                          hdealloc.2 tyJ ptrJ idJ dataJ (fun h => hneId h.symm) hJ3.2.1,
                          hJ3.2.2.1, fun j' ptrJ' idJ' hneJJ' hgetJ' hpidJ' => ?_⟩
                        have hneKJ' : k ≠ j' := by
                          intro heq; subst heq; rw [hfresh] at hgetJ'; cases hgetJ'
                        have hgetJ'Cons : localMapGet? j' ((k, ptr) :: rest) = some ptrJ' := by
                          dsimp only [localMapGet?]
                          have hneB : Nat.beq k j' = false := by
                            cases hb : Nat.beq k j' with
                            | false => rfl
                            | true => exact False.elim (hneKJ' (Nat.eq_of_beq_eq_true hb))
                          rw [hneB, if_false_eq_true]; exact hgetJ'
                        exact hJ3.2.2.2 j' ptrJ' idJ' hneJJ' hgetJ'Cons hpidJ'

/-- Helper: `storageDeadFrame` preserves `LocalMapNoDup`, `callerRetPtr`,
all other live locals' `SlotRel`, and pairwise `AllocId` disjointness. -/
theorem storageDeadFrame_sim (exact : Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mrFrame : StackFrame) (mrMem : MrMemory)
    (retMirTy : MirTy) (callerRetPtr : ThinPtr) (callerRetId : AllocId)
    (callerRetData : List AbstractByte)
    (id : LocalId) (localTy : MirTy) (oldSlot : LocalSlot)
    (hfnLoc : mrFrame.func.locals = bodyLocals.map translateTy)
    (hgetTy : Trusted.MirSemantics.getElem? bodyLocals id = some localTy)
    (hgetOld : Trusted.MirSemantics.getElem? locals id = some oldSlot)
    (hrel : FrameSlotsRel exact bodyLocals locals mrFrame.locals mrMem)
    (hnd : LocalMapNoDup mrFrame.locals)
    (hcaller : AllocLiveAt mrMem (translateTy retMirTy) callerRetPtr callerRetId callerRetData)
    (hbounds : ∀ k ptr, localMapGet? k mrFrame.locals = some ptr →
      k < bodyLocals.length ∧
      ∃ optV, Trusted.MirSemantics.getElem? locals k = some (.immediate optV))
    (hdisj : ∀ i ptr aid,
      localMapGet? i mrFrame.locals = some ptr →
      ptr.allocId = some aid →
      aid ≠ callerRetId ∧
      ∀ j ptr' aid', i ≠ j → localMapGet? j mrFrame.locals = some ptr' →
        ptr'.allocId = some aid' → aid ≠ aid') :
    ∃ (mrFrame' : StackFrame) (mrMem' : MrMemory) (locals' : List LocalSlot),
      setElem? locals id .dead = some locals' ∧
      storageDeadFrame mrFrame mrMem id = .ok (mrFrame', mrMem') ∧
      mrFrame'.func = mrFrame.func ∧
      mrFrame'.nextBlock = mrFrame.nextBlock ∧
      mrFrame'.nextStmt = mrFrame.nextStmt ∧
      mrFrame'.stackPopAction = mrFrame.stackPopAction ∧
      localMapGet? id mrFrame'.locals = none ∧
      LocalMapNoDup mrFrame'.locals ∧
      AllocLiveAt mrMem' (translateTy retMirTy) callerRetPtr callerRetId callerRetData ∧
      FrameSlotsRel exact bodyLocals locals' mrFrame'.locals mrMem' ∧
      (∀ k ptr, localMapGet? k mrFrame'.locals = some ptr →
        k < bodyLocals.length ∧
        ∃ optV, Trusted.MirSemantics.getElem? locals' k = some (.immediate optV)) ∧
      (∀ i ptr aid,
        localMapGet? i mrFrame'.locals = some ptr →
        ptr.allocId = some aid →
        aid ≠ callerRetId ∧
        ∀ j ptr' aid', i ≠ j → localMapGet? j mrFrame'.locals = some ptr' →
          ptr'.allocId = some aid' → aid ≠ aid') := by
  have hmrLoc : listGet? mrFrame.func.locals id = some (translateTy localTy) := by
    rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hgetTy]; rfl
  cases setElem?_some_of_getElem?_some locals id .dead oldSlot hgetOld with
  | intro locals' hset =>
    cases localMapRemove_spec id mrFrame.locals hnd with
    | intro hrm1 hrm2 =>
      cases hrm2 with
      | intro hrmNone hrm3 =>
        cases hrm3 with
        | intro hrmOther hnd' =>
          have hsrOld := hrel.2 id localTy oldSlot hgetTy hgetOld
          dsimp only [storageDeadFrame]
          rw [hmrLoc]
          cases hrmEq : localMapRemove id mrFrame.locals with
          | mk oldPtr localsMap' =>
            rw [hrmEq] at hrm1 hrmNone hrmOther hnd'
            dsimp only at hrm1 hrmNone hrmOther hnd'
            cases oldSlot with
            | indirect _ | partialTuple _ => cases hsrOld
            | dead =>
              dsimp only [SlotRel] at hsrOld
              have holdNone : oldPtr = none := Eq.trans hrm1 hsrOld
              subst holdNone
              refine ⟨{ mrFrame with locals := localsMap' }, mrMem, locals', hset.1, rfl,
                rfl, rfl, rfl, rfl, hrmNone, hnd', hcaller, ?_, ?_, ?_⟩
              · refine ⟨Eq.trans hset.2 hrel.1, fun i tyI slotI htyI hslotI => ?_⟩
                cases hieq : Nat.beq id i with
                | true =>
                  have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                  rw [getElem?_setElem?_eq _ _ _ _ hset.1] at hslotI
                  injection hslotI with hsDead; subst hsDead
                  exact hrmNone
                | false =>
                  have hne : id ≠ i := by
                    intro heq; subst heq; rw [Nat.beq_refl] at hieq; cases hieq
                  rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne] at hslotI
                  rw [hrmOther i (fun h => hne h.symm)]
                  exact hrel.2 i tyI slotI htyI hslotI
              · intro k ptr hgetK
                have hne : k ≠ id := by
                  intro heq; subst heq; rw [hrmNone] at hgetK; cases hgetK
                rw [hrmOther k hne] at hgetK
                cases hbounds k ptr hgetK with
                | intro hlt hex =>
                  refine ⟨hlt, ?_⟩
                  rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 (fun h => hne h.symm)]
                  exact hex
              · intro i ptr aid hgetI hpidI
                have hneI : i ≠ id := by
                  intro heq; subst heq; rw [hrmNone] at hgetI; cases hgetI
                rw [hrmOther i hneI] at hgetI
                cases hdisj i ptr aid hgetI hpidI with
                | intro hneC hdisjI =>
                  refine ⟨hneC, fun j ptr' aid' hneIJ hgetJ hpidJ => ?_⟩
                  have hneJ : j ≠ id := by
                    intro heq; subst heq; rw [hrmNone] at hgetJ; cases hgetJ
                  rw [hrmOther j hneJ] at hgetJ
                  exact hdisjI j ptr' aid' hneIJ hgetJ hpidJ
            | immediate optV =>
              cases hsrOld with
              | intro ptr h1 => cases h1 with | intro aid h2 => cases h2 with
                | intro data h3 => cases h3 with | intro hmap h4 => cases h4 with
                  | intro hlive _ =>
                    have holdSome : oldPtr = some ptr := Eq.trans hrm1 hmap
                    subst holdSome
                    cases allocLiveAt_deallocate mrMem (translateTy localTy) ptr aid data hlive with
                    | intro mrMem' hdealloc =>
                      dsimp only
                      rw [hdealloc.1]
                      have hneCaller : aid ≠ callerRetId := (hdisj id ptr aid hmap hlive.1).1
                      have hcaller' := hdealloc.2 (translateTy retMirTy) callerRetPtr callerRetId
                        callerRetData (fun h => hneCaller h.symm) hcaller
                      refine ⟨{ mrFrame with locals := localsMap' }, mrMem', locals', hset.1, rfl,
                        rfl, rfl, rfl, rfl, hrmNone, hnd', hcaller', ?_, ?_, ?_⟩
                      · refine ⟨Eq.trans hset.2 hrel.1, fun i tyI slotI htyI hslotI => ?_⟩
                        cases hieq : Nat.beq id i with
                        | true =>
                          have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                          rw [getElem?_setElem?_eq _ _ _ _ hset.1] at hslotI
                          injection hslotI with hsDead; subst hsDead
                          exact hrmNone
                        | false =>
                          have hne : id ≠ i := by
                            intro heq; subst heq; rw [Nat.beq_refl] at hieq; cases hieq
                          rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne] at hslotI
                          rw [hrmOther i (fun h => hne h.symm)]
                          have hsrI := hrel.2 i tyI slotI htyI hslotI
                          cases slotI with
                          | dead => exact hsrI
                          | indirect _ | partialTuple _ => cases hsrI
                          | immediate optVI =>
                            cases hsrI with
                            | intro ptrI hI1 => cases hI1 with | intro aidI hI2 => cases hI2 with
                              | intro dataI hI3 => cases hI3 with | intro hmapI hI4 => cases hI4 with
                                | intro hliveI hvalI =>
                                  have hneAid : aid ≠ aidI :=
                                    (hdisj id ptr aid hmap hlive.1).2 i ptrI aidI hne hmapI hliveI.1
                                  exact ⟨ptrI, aidI, dataI, hmapI,
                                    hdealloc.2 (translateTy tyI) ptrI aidI dataI
                                      (fun h => hneAid h.symm) hliveI, hvalI⟩
                      · intro k ptrK hgetK
                        have hne : k ≠ id := by
                          intro heq; subst heq; rw [hrmNone] at hgetK; cases hgetK
                        rw [hrmOther k hne] at hgetK
                        cases hbounds k ptrK hgetK with
                        | intro hlt hex =>
                          refine ⟨hlt, ?_⟩
                          rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 (fun h => hne h.symm)]
                          exact hex
                      · intro i ptrI aidI hgetI hpidI
                        have hneI : i ≠ id := by
                          intro heq; subst heq; rw [hrmNone] at hgetI; cases hgetI
                        rw [hrmOther i hneI] at hgetI
                        cases hdisj i ptrI aidI hgetI hpidI with
                        | intro hneC hdisjI =>
                          refine ⟨hneC, fun j ptrJ aidJ hneIJ hgetJ hpidJ => ?_⟩
                          have hneJ : j ≠ id := by
                            intro heq; subst heq; rw [hrmNone] at hgetJ; cases hgetJ
                          rw [hrmOther j hneJ] at hgetJ
                          exact hdisjI j ptrJ aidJ hneIJ hgetJ hpidJ

/-- Helper: `storageLiveFrame` allocates fresh uninitialized storage for `id`
(deallocating any existing live allocation first) and keeps all invariants. -/
theorem storageLiveFrame_sim (exact : Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (mrFrame : StackFrame) (mrMem : MrMemory)
    (retMirTy : MirTy) (callerRetPtr : ThinPtr) (callerRetId : AllocId)
    (callerRetData : List AbstractByte)
    (id : LocalId) (localTy : MirTy) (oldSlot : LocalSlot)
    (hfnLoc : mrFrame.func.locals = bodyLocals.map translateTy)
    (hsupp : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (hgetTy : Trusted.MirSemantics.getElem? bodyLocals id = some localTy)
    (hgetOld : Trusted.MirSemantics.getElem? locals id = some oldSlot)
    (hrel : FrameSlotsRel exact bodyLocals locals mrFrame.locals mrMem)
    (hnd : LocalMapNoDup mrFrame.locals)
    (hcaller : AllocLiveAt mrMem (translateTy retMirTy) callerRetPtr callerRetId callerRetData)
    (hbounds : ∀ k ptr, localMapGet? k mrFrame.locals = some ptr →
      k < bodyLocals.length ∧
      ∃ optV, Trusted.MirSemantics.getElem? locals k = some (.immediate optV))
    (hdisj : ∀ i ptr aid,
      localMapGet? i mrFrame.locals = some ptr →
      ptr.allocId = some aid →
      aid ≠ callerRetId ∧
      ∀ j ptr' aid', i ≠ j → localMapGet? j mrFrame.locals = some ptr' →
        ptr'.allocId = some aid' → aid ≠ aid') :
    ∃ (mrFrame' : StackFrame) (mrMem' : MrMemory) (locals' : List LocalSlot),
      setElem? locals id (liveUninitSlot localTy) = some locals' ∧
      storageLiveFrame mrFrame mrMem id = .ok (mrFrame', mrMem') ∧
      mrFrame'.func = mrFrame.func ∧
      mrFrame'.nextBlock = mrFrame.nextBlock ∧
      mrFrame'.nextStmt = mrFrame.nextStmt ∧
      mrFrame'.stackPopAction = mrFrame.stackPopAction ∧
      LocalMapNoDup mrFrame'.locals ∧
      AllocLiveAt mrMem' (translateTy retMirTy) callerRetPtr callerRetId callerRetData ∧
      FrameSlotsRel exact bodyLocals locals' mrFrame'.locals mrMem' ∧
      (∀ k ptr, localMapGet? k mrFrame'.locals = some ptr →
        k < bodyLocals.length ∧
        ∃ optV, Trusted.MirSemantics.getElem? locals' k = some (.immediate optV)) ∧
      (∀ i ptr aid,
        localMapGet? i mrFrame'.locals = some ptr →
        ptr.allocId = some aid →
        aid ≠ callerRetId ∧
        ∀ j ptr' aid', i ≠ j → localMapGet? j mrFrame'.locals = some ptr' →
          ptr'.allocId = some aid' → aid ≠ aid') := by
  have hmrLoc : listGet? mrFrame.func.locals id = some (translateTy localTy) := by
    rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hgetTy]; rfl
  have htySupp : isSupportedScalarOrUnitTy localTy = true := by
    rw [getElem?_eq_listGet?] at hgetTy
    exact listGet?_all isSupportedScalarOrUnitTy bodyLocals id localTy hsupp hgetTy
  have hvalidAlign := translateTy_validSize_and_alignPos localTy htySupp
  cases setElem?_some_of_getElem?_some locals id (liveUninitSlot localTy) oldSlot hgetOld with
  | intro locals' hset =>
    cases storageDeadFrame_sim exact bodyLocals locals mrFrame mrMem retMirTy
        callerRetPtr callerRetId callerRetData id localTy oldSlot
        hfnLoc hgetTy hgetOld hrel hnd hcaller hbounds hdisj with
    | intro mrF1 h1 => cases h1 with | intro mrM1 h2 => cases h2 with
      | intro localsDead h3 =>
        cases h3 with
        | intro hsetDead h4 => cases h4 with
          | intro hdeadOk h5 => cases h5 with
            | intro hfunc1 h6 => cases h6 with
              | intro hblk1 h7 => cases h7 with
                | intro hstmt1 h8 => cases h8 with
                  | intro hpop1 h9 => cases h9 with
                    | intro hnone1 h10 => cases h10 with
                      | intro hnd1 h11 => cases h11 with
                        | intro hcaller1 h12 => cases h12 with
                          | intro hrel1 h13 => cases h13 with
                            | intro hbounds1 hdisj1 =>
                              cases allocLiveAt_allocate mrM1 (translateTy localTy)
                                  hvalidAlign.1 hvalidAlign.2 with
                              | intro mrM2 hA1 => cases hA1 with
                                | intro newPtr hA2 => cases hA2 with
                                  | intro hallocOk hA3 => cases hA3 with
                                    | intro hliveNew hpresAlloc =>
                                      have hcaller2 := hpresAlloc (translateTy retMirTy) callerRetPtr
                                        callerRetId callerRetData hcaller1
                                      cases localMapInsert_spec id newPtr mrF1.locals hnd1 with
                                      | intro hgetNew hIns1 => cases hIns1 with
                                        | intro hgetOther hnd2 =>
                                          have hltId : id < bodyLocals.length := by
                                            rw [getElem?_eq_listGet?] at hgetTy
                                            exact listGet?_lt_length bodyLocals id localTy hgetTy
                                          dsimp only [storageLiveFrame]
                                          rw [hmrLoc]; dsimp only
                                          rw [hdeadOk]; dsimp only
                                          rw [hallocOk]
                                          refine ⟨{ mrF1 with locals := localMapInsert id newPtr mrF1.locals },
                                            mrM2, locals', hset.1, rfl,
                                            hfunc1, hblk1, hstmt1, hpop1, hnd2, hcaller2.2,
                                            ?_, ?_, ?_⟩
                                          · refine ⟨Eq.trans hset.2 hrel.1, fun i tyI slotI htyI hslotI => ?_⟩
                                            cases hieq : Nat.beq id i with
                                            | true =>
                                              have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                                              rw [hgetTy] at htyI; injection htyI with hte; subst hte
                                              rw [getElem?_setElem?_eq _ _ _ _ hset.1] at hslotI
                                              injection hslotI with hsl; subst hsl
                                              rw [hgetNew]
                                              exact liveUninitSlot_slotRel exact mrM2 localTy newPtr
                                                mrM1.allocations.length htySupp hliveNew
                                            | false =>
                                              have hne : id ≠ i := by
                                                intro heq; subst heq; rw [Nat.beq_refl] at hieq; cases hieq
                                              rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne] at hslotI
                                              rw [hgetOther i (fun h => hne h.symm)]
                                              have hslotDead : Trusted.MirSemantics.getElem? localsDead i = some slotI := by
                                                rw [getElem?_setElem?_ne _ _ _ _ _ hsetDead hne]; exact hslotI
                                              have hsrI := hrel1.2 i tyI slotI htyI hslotDead
                                              cases slotI with
                                              | dead => exact hsrI
                                              | indirect _ | partialTuple _ => cases hsrI
                                              | immediate optVI =>
                                                cases hsrI with
                                                | intro ptrI hI1 => cases hI1 with | intro aidI hI2 => cases hI2 with
                                                  | intro dataI hI3 => cases hI3 with | intro hmapI hI4 => cases hI4 with
                                                    | intro hliveI hvalI =>
                                                      exact ⟨ptrI, aidI, dataI, hmapI,
                                                        (hpresAlloc (translateTy tyI) ptrI aidI dataI hliveI).2, hvalI⟩
                                          · intro k ptrK hgetK
                                            cases hkeq : Nat.beq id k with
                                            | true =>
                                              have heq := Nat.eq_of_beq_eq_true hkeq; subst heq
                                              refine ⟨hltId, ?_⟩
                                              rw [getElem?_setElem?_eq _ _ _ _ hset.1]
                                              cases liveUninitSlot_isImmediate localTy with
                                              | intro ov hov => exact ⟨ov, congrArg some hov⟩
                                            | false =>
                                              have hne : id ≠ k := by
                                                intro heq; subst heq; rw [Nat.beq_refl] at hkeq; cases hkeq
                                              rw [hgetOther k (fun h => hne h.symm)] at hgetK
                                              cases hbounds1 k ptrK hgetK with
                                              | intro hltK hexK =>
                                                rw [getElem?_setElem?_ne _ _ _ _ _ hsetDead hne] at hexK
                                                rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne]
                                                exact ⟨hltK, hexK⟩
                                          · intro i ptrI aidI hgetI hpidI
                                            have hfreshAid : ∀ k ptrK aidK,
                                                localMapGet? k mrF1.locals = some ptrK →
                                                ptrK.allocId = some aidK →
                                                aidK ≠ mrM1.allocations.length := by
                                              intro k ptrK aidK hgetK hpidK
                                              cases hbounds1 k ptrK hgetK with
                                              | intro hltK hexK =>
                                                cases listGet?_some_of_lt bodyLocals k hltK with
                                                | intro tyK htyK =>
                                                  have htyK' : Trusted.MirSemantics.getElem? bodyLocals k = some tyK := by
                                                    rw [getElem?_eq_listGet?]; exact htyK
                                                  cases hexK with
                                                  | intro ovK hovK =>
                                                    have hsrK := hrel1.2 k tyK (.immediate ovK) htyK' hovK
                                                    cases hsrK with
                                                    | intro ptrK' hK1 => cases hK1 with | intro aidK' hK2 => cases hK2 with
                                                      | intro dataK' hK3 =>
                                                        rw [hgetK] at hK3
                                                        injection hK3.1 with hpeq; subst hpeq
                                                        have hliveK := hK3.2.1
                                                        rw [hliveK.1] at hpidK; injection hpidK with haeq; subst haeq
                                                        exact (hpresAlloc (translateTy tyK) ptrK aidK' dataK' hliveK).1
                                            cases hieq : Nat.beq id i with
                                            | true =>
                                              have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                                              rw [hgetNew] at hgetI; injection hgetI with hpeq; subst hpeq
                                              rw [hliveNew.1] at hpidI; injection hpidI with haeq; subst haeq
                                              refine ⟨fun h => hcaller2.1 h.symm, fun j ptrJ aidJ hneIJ hgetJ hpidJ => ?_⟩
                                              rw [hgetOther j (fun h => hneIJ h.symm)] at hgetJ
                                              exact fun h => hfreshAid j ptrJ aidJ hgetJ hpidJ h.symm
                                            | false =>
                                              have hneI : id ≠ i := by
                                                intro heq; subst heq; rw [Nat.beq_refl] at hieq; cases hieq
                                              rw [hgetOther i (fun h => hneI h.symm)] at hgetI
                                              cases hdisj1 i ptrI aidI hgetI hpidI with
                                              | intro hneC hdisjI =>
                                                refine ⟨hneC, fun j ptrJ aidJ hneIJ hgetJ hpidJ => ?_⟩
                                                cases hjeq : Nat.beq id j with
                                                | true =>
                                                  have heq := Nat.eq_of_beq_eq_true hjeq; subst heq
                                                  rw [hgetNew] at hgetJ; injection hgetJ with hpeq; subst hpeq
                                                  rw [hliveNew.1] at hpidJ; injection hpidJ with haeq; subst haeq
                                                  exact hfreshAid i ptrI aidI hgetI hpidI
                                                | false =>
                                                  have hneJ : id ≠ j := by
                                                    intro heq; subst heq; rw [Nat.beq_refl] at hjeq; cases hjeq
                                                  rw [hgetOther j (fun h => hneJ h.symm)] at hgetJ
                                                  exact hdisjI j ptrJ aidJ hneIJ hgetJ hpidJ

/-- Helper: storing a well-formed value `val` of type `dstTy` to a live local
`dstId` succeeds in both Anneal (`writePlace`) and MiniRust (`typedStore`) and
preserves all frame invariants. -/
theorem writePlace_live_sim (exact : Bool) (bodyLocals : List MirTy)
    (locals : List LocalSlot) (memS : MemoryState) (mrFrame : StackFrame) (mrMem : MrMemory)
    (retMirTy : MirTy) (callerRetPtr : ThinPtr) (callerRetId : AllocId)
    (callerRetData : List AbstractByte)
    (dstId : LocalId) (dstTy : MirTy) (optOld : Option Val) (val : Val)
    (hsupp : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (hgetTy : Trusted.MirSemantics.getElem? bodyLocals dstId = some dstTy)
    (hgetOld : Trusted.MirSemantics.getElem? locals dstId = some (.immediate optOld))
    (hcv : checkVal val dstTy = true)
    (hrel : FrameSlotsRel exact bodyLocals locals mrFrame.locals mrMem)
    (hcaller : AllocLiveAt mrMem (translateTy retMirTy) callerRetPtr callerRetId callerRetData)
    (hbounds : ∀ k ptr, localMapGet? k mrFrame.locals = some ptr →
      k < bodyLocals.length ∧
      ∃ optV, Trusted.MirSemantics.getElem? locals k = some (.immediate optV))
    (hdisj : ∀ i ptr aid,
      localMapGet? i mrFrame.locals = some ptr →
      ptr.allocId = some aid →
      aid ≠ callerRetId ∧
      ∀ j ptr' aid', i ≠ j → localMapGet? j mrFrame.locals = some ptr' →
        ptr'.allocId = some aid' → aid ≠ aid') :
    ∃ (locals' : List LocalSlot) (ptr : ThinPtr) (mrMem' : MrMemory),
      writePlace locals memS dstId dstTy val = .ok (locals', memS) ∧
      localMapGet? dstId mrFrame.locals = some ptr ∧
      typedStore mrMem ptr (translateVal val) (translateTy dstTy) ⟨1⟩ = .ok mrMem' ∧
      AllocLiveAt mrMem' (translateTy retMirTy) callerRetPtr callerRetId callerRetData ∧
      FrameSlotsRel exact bodyLocals locals' mrFrame.locals mrMem' ∧
      (∀ k ptrK, localMapGet? k mrFrame.locals = some ptrK →
        k < bodyLocals.length ∧
        ∃ optV, Trusted.MirSemantics.getElem? locals' k = some (.immediate optV)) := by
  have htySupp : isSupportedScalarOrUnitTy dstTy = true := by
    rw [getElem?_eq_listGet?] at hgetTy
    exact listGet?_all isSupportedScalarOrUnitTy bodyLocals dstId dstTy hsupp hgetTy
  cases setElem?_some_of_getElem?_some locals dstId (.immediate (some val)) (.immediate optOld) hgetOld with
  | intro locals' hset =>
    have hsrDst := hrel.2 dstId dstTy (.immediate optOld) hgetTy hgetOld
    cases hsrDst with
    | intro ptr h1 => cases h1 with | intro aid h2 => cases h2 with
      | intro data h3 => cases h3 with | intro hmap h4 => cases h4 with
        | intro hlive _ =>
          cases mrEncode_mrDecode_roundtrip dstTy val htySupp hcv with
          | intro newBytes hrt =>
            cases allocLiveAt_store mrMem (translateTy dstTy) ptr aid data newBytes ⟨1⟩
                hlive (align_one_isAligned ptr.addr) hrt.2.1 with
            | intro mrMem' hst =>
              have hneCaller : aid ≠ callerRetId := (hdisj dstId ptr aid hmap hlive.1).1
              have hcaller' := hst.2.2 (translateTy retMirTy) callerRetPtr callerRetId
                callerRetData (fun h => hneCaller h.symm) hcaller
              refine ⟨locals', ptr, mrMem', ?_, hmap, ?_, hcaller', ?_, ?_⟩
              · dsimp only [writePlace]; rw [hcv, if_not_true, hgetOld, hset.1]
              · dsimp only [typedStore, liftMemRes]; rw [hrt.1]; dsimp only; rw [hst.1]
              · refine ⟨Eq.trans hset.2 hrel.1, fun i tyI slotI htyI hslotI => ?_⟩
                cases hieq : Nat.beq dstId i with
                | true =>
                  have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                  rw [hgetTy] at htyI; injection htyI with hte; subst hte
                  rw [getElem?_setElem?_eq _ _ _ _ hset.1] at hslotI
                  injection hslotI with hsl; subst hsl
                  exact ⟨ptr, aid, newBytes, hmap, hst.2.1, hcv, hrt.2.2⟩
                | false =>
                  have hne : dstId ≠ i := by
                    intro heq; subst heq; rw [Nat.beq_refl] at hieq; cases hieq
                  rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne] at hslotI
                  have hsrI := hrel.2 i tyI slotI htyI hslotI
                  cases slotI with
                  | dead => exact hsrI
                  | indirect _ | partialTuple _ => cases hsrI
                  | immediate optVI =>
                    cases hsrI with
                    | intro ptrI hI1 => cases hI1 with | intro aidI hI2 => cases hI2 with
                      | intro dataI hI3 => cases hI3 with | intro hmapI hI4 => cases hI4 with
                        | intro hliveI hvalI =>
                          have hneAid : aid ≠ aidI :=
                            (hdisj dstId ptr aid hmap hlive.1).2 i ptrI aidI hne hmapI hliveI.1
                          exact ⟨ptrI, aidI, dataI, hmapI,
                            hst.2.2 (translateTy tyI) ptrI aidI dataI
                              (fun h => hneAid h.symm) hliveI, hvalI⟩
              · intro k ptrK hgetK
                cases hbounds k ptrK hgetK with
                | intro hltK hexK =>
                  refine ⟨hltK, ?_⟩
                  cases hkeq : Nat.beq dstId k with
                  | true =>
                    have heq := Nat.eq_of_beq_eq_true hkeq; subst heq
                    rw [getElem?_setElem?_eq _ _ _ _ hset.1]
                    exact ⟨some val, rfl⟩
                  | false =>
                    have hne : dstId ≠ k := by
                      intro heq; subst heq; rw [Nat.beq_refl] at hkeq; cases hkeq
                    rw [getElem?_setElem?_ne _ _ _ _ _ hset.1 hne]
                    exact hexK

/-! ## Entry Initialization Simulation (`init_stateRel`) -/

/-- Helper: `initMrArgsLoop` allocates and stores arguments
`start .. start + vs.length - 1`. -/
theorem initMrArgsLoop_spec (body : Body) (retMirTy : MirTy)
    (callerRetPtr : ThinPtr) (callerRetId : AllocId) (callerRetData : List AbstractByte)
    (hsupp : body.locals.all isSupportedScalarOrUnitTy = true) :
    ∀ (vs : List Val) (start : Nat) (frame : StackFrame) (mem : MrMemory),
      frame.func = translateBody body →
      1 ≤ start →
      start + vs.length ≤ body.locals.length →
      checkArgsMatch vs ((body.locals.drop start).take vs.length) = true →
      LocalMapNoDup frame.locals →
      AllocLiveAt mem (translateTy retMirTy) callerRetPtr callerRetId callerRetData →
      (∀ k ptr, localMapGet? k frame.locals = some ptr → k < start) →
      (∀ k ty ptr, k < start →
        listGet? body.locals k = some ty →
        localMapGet? k frame.locals = some ptr →
        ∃ id data, AllocLiveAt mem (translateTy ty) ptr id data) →
      (∀ i ptr aid,
        localMapGet? i frame.locals = some ptr →
        ptr.allocId = some aid →
        aid ≠ callerRetId ∧
        ∀ j ptr' aid', i ≠ j → localMapGet? j frame.locals = some ptr' →
          ptr'.allocId = some aid' → aid ≠ aid') →
      ∃ (frame' : StackFrame) (mem' : MrMemory),
        initMrArgsLoop frame mem start vs = .ok (frame', mem') ∧
        frame'.func = frame.func ∧
        frame'.nextBlock = frame.nextBlock ∧
        frame'.nextStmt = frame.nextStmt ∧
        frame'.stackPopAction = frame.stackPopAction ∧
        LocalMapNoDup frame'.locals ∧
        AllocLiveAt mem' (translateTy retMirTy) callerRetPtr callerRetId callerRetData ∧
        (∀ k ptr, localMapGet? k frame'.locals = some ptr → k < start + vs.length) ∧
        (∀ k, k < start → localMapGet? k frame'.locals = localMapGet? k frame.locals) ∧
        (∀ k ty ptr id data, k < start →
          listGet? body.locals k = some ty →
          localMapGet? k frame.locals = some ptr →
          AllocLiveAt mem (translateTy ty) ptr id data →
          AllocLiveAt mem' (translateTy ty) ptr id data) ∧
        (∀ off v ty,
          listGet? vs off = some v →
          listGet? body.locals (start + off) = some ty →
          ∃ ptr id data,
            localMapGet? (start + off) frame'.locals = some ptr ∧
            AllocLiveAt mem' (translateTy ty) ptr id data ∧
            checkVal v ty = true ∧
            mrDecode (translateTy ty) data = some (translateVal v)) ∧
        (∀ i ptr aid,
          localMapGet? i frame'.locals = some ptr →
          ptr.allocId = some aid →
          aid ≠ callerRetId ∧
          ∀ j ptr' aid', i ≠ j → localMapGet? j frame'.locals = some ptr' →
            ptr'.allocId = some aid' → aid ≠ aid') := by
  intro vs
  induction vs with
  | nil =>
    intro start frame mem _ _ _ _ hnd hcaller hlt _ hdisj
    dsimp only [List.length]
    rw [Nat.add_zero]
    exact ⟨frame, mem, rfl, rfl, rfl, rfl, rfl, hnd, hcaller, hlt,
      fun _ _ => rfl, fun _ _ _ _ _ _ _ _ h => h, fun _ _ _ hv => (by cases hv), hdisj⟩
  | cons v rest ih =>
    intro start frame mem hfn hge1 hleLen hmatch hnd hcaller hlt hlivePre hdisj
    have hstartLt : start < body.locals.length := by
      dsimp only [List.length] at hleLen
      exact Nat.lt_of_succ_le (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ _)) (by rw [Nat.add_succ] at hleLen; exact hleLen))
    cases listGet?_some_of_lt body.locals start hstartLt with
    | intro tyStart htyStart =>
      have hdropHead : (body.locals.drop start).take (v :: rest).length =
          tyStart :: ((body.locals.drop (start + 1)).take rest.length) := by
        have hdropCons : ∃ tail, body.locals.drop start = tyStart :: tail ∧
            tail = body.locals.drop (start + 1) := by
          have hgen : ∀ (xs : List MirTy) (k : Nat) (x : MirTy),
              listGet? xs k = some x →
              xs.drop k = x :: xs.drop (k + 1) := by
            intro xs; induction xs with
            | nil => intro _ _ hg; cases hg
            | cons a as iha =>
              intro k x hg; cases k with
              | zero =>
                dsimp only [listGet?] at hg; injection hg with hax; subst hax; rfl
              | succ k' => exact iha k' x hg
          exact ⟨body.locals.drop (start + 1), hgen body.locals start tyStart htyStart, rfl⟩
        cases hdropCons with
        | intro tail ht => rw [ht.1, ht.2]; rfl
      rw [hdropHead] at hmatch
      dsimp only [checkArgsMatch] at hmatch
      cases hcv : checkVal v tyStart with
      | false => rw [hcv] at hmatch; cases hmatch
      | true =>
        rw [hcv] at hmatch
        have htySupp : isSupportedScalarOrUnitTy tyStart = true :=
          listGet?_all isSupportedScalarOrUnitTy body.locals start tyStart hsupp htyStart
        have hvalidAlign := translateTy_validSize_and_alignPos tyStart htySupp
        have hmrLoc : listGet? frame.func.locals start = some (translateTy tyStart) := by
          rw [hfn]; dsimp only [translateBody]; rw [listGet?_map, htyStart]; rfl
        have hdeadStart : localMapGet? start frame.locals = none := by
          cases hg : localMapGet? start frame.locals with
          | none => rfl
          | some ptr => exact False.elim (Nat.lt_irrefl start (hlt start ptr hg))
        cases storageLiveFrame_fresh frame mem start (translateTy tyStart)
            hmrLoc hdeadStart hvalidAlign.1 hvalidAlign.2 with
        | intro mem1 hS1 => cases hS1 with | intro ptr1 hS2 => cases hS2 with
          | intro hslOk hS3 => cases hS3 with | intro hlive1 hpres1 =>
            cases localMapInsert_spec start ptr1 frame.locals hnd with
            | intro hget1 hIns1 => cases hIns1 with | intro hgetOther1 hnd1 =>
              cases mrEncode_mrDecode_roundtrip tyStart v htySupp hcv with
              | intro vBytes hrt =>
                cases allocLiveAt_store mem1 (translateTy tyStart) ptr1 mem.allocations.length
                    (List.replicate (translateTy tyStart).size.bytes .uninit) vBytes
                    (translateTy tyStart).align hlive1 (allocLiveAt_isAligned hlive1) hrt.2.1 with
                | intro mem2 hSt =>
                  have hcaller1 := hpres1 (translateTy retMirTy) callerRetPtr callerRetId callerRetData hcaller
                  have hcaller2 := hSt.2.2 (translateTy retMirTy) callerRetPtr callerRetId callerRetData
                    hcaller1.1 hcaller1.2
                  have htypedSt : typedStore mem1 ptr1 (translateVal v) (translateTy tyStart)
                      (translateTy tyStart).align = .ok mem2 := by
                    dsimp only [typedStore, liftMemRes]; rw [hrt.1]; dsimp only; rw [hSt.1]
                  have hlenNext : start + 1 + rest.length ≤ body.locals.length := by
                    rw [Nat.add_assoc, Nat.add_comm 1 rest.length]; exact hleLen
                  let frame1 : StackFrame := { frame with locals := localMapInsert start ptr1 frame.locals }
                  have hlt1 : ∀ k ptr, localMapGet? k frame1.locals = some ptr → k < start + 1 := by
                    intro k ptr hg
                    cases hkeq : Nat.beq start k with
                    | true =>
                      have heq := Nat.eq_of_beq_eq_true hkeq; subst heq; exact Nat.lt_succ_self _
                    | false =>
                      have hne : start ≠ k := by intro h; subst h; rw [Nat.beq_refl] at hkeq; cases hkeq
                      rw [hgetOther1 k (fun h => hne h.symm)] at hg
                      exact Nat.lt_trans (hlt k ptr hg) (Nat.lt_succ_self _)
                  have hlivePre1 : ∀ k ty ptr, k < start + 1 →
                      listGet? body.locals k = some ty →
                      localMapGet? k frame1.locals = some ptr →
                      ∃ id data, AllocLiveAt mem2 (translateTy ty) ptr id data := by
                    intro k ty ptr hk htyK hg
                    cases hkeq : Nat.beq start k with
                    | true =>
                      have heq := Nat.eq_of_beq_eq_true hkeq; subst heq
                      rw [htyStart] at htyK; injection htyK with hte; subst hte
                      rw [hget1] at hg; injection hg with hpe; subst hpe
                      exact ⟨mem.allocations.length, vBytes, hSt.2.1⟩
                    | false =>
                      have hne : start ≠ k := by intro h; subst h; rw [Nat.beq_refl] at hkeq; cases hkeq
                      rw [hgetOther1 k (fun h => hne h.symm)] at hg
                      have hkLt : k < start := hlt k ptr hg
                      cases hlivePre k ty ptr hkLt htyK hg with
                      | intro idK hK => cases hK with | intro dataK hliveK =>
                        have hp := hpres1 (translateTy ty) ptr idK dataK hliveK
                        exact ⟨idK, dataK, hSt.2.2 (translateTy ty) ptr idK dataK hp.1 hp.2⟩
                  have hfreshOld : ∀ k ptr aid,
                      localMapGet? k frame.locals = some ptr →
                      ptr.allocId = some aid →
                      aid ≠ mem.allocations.length := by
                    intro k ptr aid hg hpid
                    have hkLt := hlt k ptr hg
                    cases listGet?_some_of_lt body.locals k (Nat.lt_trans hkLt hstartLt) with
                    | intro tyK htyK =>
                      cases hlivePre k tyK ptr hkLt htyK hg with
                      | intro idK hK => cases hK with | intro dataK hliveK =>
                        rw [hliveK.1] at hpid; injection hpid with heq; subst heq
                        exact (hpres1 (translateTy tyK) ptr idK dataK hliveK).1
                  have hdisj1 : ∀ i ptr aid,
                      localMapGet? i frame1.locals = some ptr →
                      ptr.allocId = some aid →
                      aid ≠ callerRetId ∧
                      ∀ j ptr' aid', i ≠ j → localMapGet? j frame1.locals = some ptr' →
                        ptr'.allocId = some aid' → aid ≠ aid' := by
                    intro i ptr aid hg hpid
                    cases hieq : Nat.beq start i with
                    | true =>
                      have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                      rw [hget1] at hg; injection hg with hpe; subst hpe
                      rw [hlive1.1] at hpid; injection hpid with hae; subst hae
                      refine ⟨fun h => hcaller1.1 h.symm, fun j ptrJ aidJ hneIJ hgJ hpidJ => ?_⟩
                      rw [hgetOther1 j (fun h => hneIJ h.symm)] at hgJ
                      exact fun h => hfreshOld j ptrJ aidJ hgJ hpidJ h.symm
                    | false =>
                      have hneI : start ≠ i := by intro h; subst h; rw [Nat.beq_refl] at hieq; cases hieq
                      rw [hgetOther1 i (fun h => hneI h.symm)] at hg
                      cases hdisj i ptr aid hg hpid with
                      | intro hneC hdisjI =>
                        refine ⟨hneC, fun j ptrJ aidJ hneIJ hgJ hpidJ => ?_⟩
                        cases hjeq : Nat.beq start j with
                        | true =>
                          have heq := Nat.eq_of_beq_eq_true hjeq; subst heq
                          rw [hget1] at hgJ; injection hgJ with hpe; subst hpe
                          rw [hlive1.1] at hpidJ; injection hpidJ with hae; subst hae
                          exact hfreshOld i ptr aid hg hpid
                        | false =>
                          have hneJ : start ≠ j := by intro h; subst h; rw [Nat.beq_refl] at hjeq; cases hjeq
                          rw [hgetOther1 j (fun h => hneJ h.symm)] at hgJ
                          exact hdisjI j ptrJ aidJ hneIJ hgJ hpidJ
                  cases ih (start + 1) frame1 mem2 hfn (Nat.le_trans hge1 (Nat.le_succ _))
                      hlenNext hmatch hnd1 hcaller2 hlt1 hlivePre1 hdisj1 with
                  | intro frame' hI1 => cases hI1 with | intro mem' hI2 =>
                    cases hI2 with
                    | intro hloopOk hI3 => cases hI3 with
                      | intro hfn' hI4 => cases hI4 with
                        | intro hblk' hI5 => cases hI5 with
                          | intro hstmt' hI6 => cases hI6 with
                            | intro hpop' hI7 => cases hI7 with
                              | intro hnd' hI8 => cases hI8 with
                                | intro hcaller' hI9 => cases hI9 with
                                  | intro hlt' hI10 => cases hI10 with
                                    | intro hkeepPre' hI11 => cases hI11 with
                                      | intro hliveKeep' hI12 => cases hI12 with
                                        | intro hargs' hdisj' =>
                                          dsimp only [initMrArgsLoop]
                                          rw [hslOk]
                                          dsimp only
                                          have hloc1 : listGet? frame1.func.locals start = some (translateTy tyStart) := hmrLoc
                                          rw [hloc1, hget1]
                                          dsimp only
                                          rw [htypedSt]
                                          have hlenAdd : start + (v :: rest).length = start + 1 + rest.length := by
                                            dsimp only [List.length]; rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
                                          refine ⟨frame', mem', hloopOk, hfn', hblk', hstmt', hpop',
                                            hnd', hcaller', ?_, ?_, ?_, ?_, hdisj'⟩
                                          · intro k ptrK hgK; rw [hlenAdd]; exact hlt' k ptrK hgK
                                          · intro k hk
                                            rw [hkeepPre' k (Nat.lt_trans hk (Nat.lt_succ_self _))]
                                            exact hgetOther1 k (Nat.ne_of_lt hk)
                                          · intro k tyK ptrK idK dataK hk htyK hgK hliveK
                                            have hp := hpres1 (translateTy tyK) ptrK idK dataK hliveK
                                            have hliveK2 := hSt.2.2 (translateTy tyK) ptrK idK dataK hp.1 hp.2
                                            have hgK1 : localMapGet? k frame1.locals = some ptrK := by
                                              rw [hgetOther1 k (Nat.ne_of_lt hk)]; exact hgK
                                            exact hliveKeep' k tyK ptrK idK dataK
                                              (Nat.lt_trans hk (Nat.lt_succ_self _)) htyK hgK1 hliveK2
                                          · intro off w tyW hw htyW
                                            cases off with
                                            | zero =>
                                              dsimp only [listGet?] at hw; injection hw with hvw; subst hvw
                                              rw [Nat.add_zero] at htyW; rw [Nat.add_zero]
                                              rw [htyStart] at htyW; injection htyW with hte; subst hte
                                              have hgetStart' : localMapGet? start frame'.locals = some ptr1 := by
                                                rw [hkeepPre' start (Nat.lt_succ_self _)]; exact hget1
                                              have hliveStart' := hliveKeep' start tyStart ptr1
                                                mem.allocations.length vBytes (Nat.lt_succ_self _)
                                                htyStart hget1 hSt.2.1
                                              exact ⟨ptr1, mem.allocations.length, vBytes, hgetStart',
                                                hliveStart', hcv, hrt.2.2⟩
                                            | succ k =>
                                              dsimp only [listGet?] at hw
                                              have hidx : start + Nat.succ k = start + 1 + k := by
                                                rw [Nat.add_assoc, Nat.add_comm 1 k]
                                              rw [hidx] at htyW; rw [hidx]
                                              exact hargs' k w tyW hw htyW

/-- Multi-step execution of `initBlock`'s `StorageLive` statements starting from
statement index `stmtIdx`, allocating every local in `temps.drop stmtIdx`. -/
theorem runInitBlock_steps (p : Program) (body : Body)
    (retMirTy : MirTy) (callerRetPtr : ThinPtr) (callerRetId : AllocId)
    (callerRetData : List AbstractByte) (callerFrame : StackFrame)
    (hbbPos : 0 < body.basicBlocks.length)
    (hsupp : body.locals.all isSupportedScalarOrUnitTy = true)
    (temps : List LocalName)
    (htempsSpec : ∀ k, k ∈ temps → k < body.locals.length)
    (hpw : natListPairwiseNe temps = true) :
    ∀ (idx : Nat) (calleeFrame : StackFrame) (mem : MrMemory),
      idx ≤ temps.length →
      calleeFrame.func = translateBody body →
      calleeFrame.nextBlock = 0 →
      calleeFrame.nextStmt = idx →
      listGet? calleeFrame.func.blocks 0 =
        some { statements := temps.map MrStatement.storageLive, terminator := .goto 1 } →
      LocalMapNoDup calleeFrame.locals →
      AllocLiveAt mem (translateTy retMirTy) callerRetPtr callerRetId callerRetData →
      (∀ k, k ∈ temps.drop idx → localMapGet? k calleeFrame.locals = none) →
      (∀ k ptr, localMapGet? k calleeFrame.locals = some ptr →
        ∃ ty id data, listGet? body.locals k = some ty ∧
          AllocLiveAt mem (translateTy ty) ptr id data) →
      (∀ i ptr aid,
        localMapGet? i calleeFrame.locals = some ptr →
        ptr.allocId = some aid →
        aid ≠ callerRetId ∧
        ∀ j ptr' aid', i ≠ j → localMapGet? j calleeFrame.locals = some ptr' →
          ptr'.allocId = some aid' → aid ≠ aid') →
      ∃ (calleeFrame' : StackFrame) (mem' : MrMemory),
        MrReaches
          { prog := translateProg p, mem := mem, stack := [calleeFrame, callerFrame] }
          { prog := translateProg p, mem := mem', stack := [calleeFrame', callerFrame] } ∧
        calleeFrame'.func = calleeFrame.func ∧
        calleeFrame'.nextBlock = 1 ∧
        calleeFrame'.nextStmt = 0 ∧
        calleeFrame'.stackPopAction = calleeFrame.stackPopAction ∧
        LocalMapNoDup calleeFrame'.locals ∧
        AllocLiveAt mem' (translateTy retMirTy) callerRetPtr callerRetId callerRetData ∧
        (∀ k, k ∈ temps.drop idx →
          ∃ ty ptr id,
            listGet? body.locals k = some ty ∧
            localMapGet? k calleeFrame'.locals = some ptr ∧
            AllocLiveAt mem' (translateTy ty) ptr id
              (List.replicate (translateTy ty).size.bytes .uninit)) ∧
        (∀ k, ¬ (k ∈ temps.drop idx) →
          localMapGet? k calleeFrame'.locals = localMapGet? k calleeFrame.locals) ∧
        (∀ k ty ptr id data,
          ¬ (k ∈ temps.drop idx) →
          listGet? body.locals k = some ty →
          localMapGet? k calleeFrame.locals = some ptr →
          AllocLiveAt mem (translateTy ty) ptr id data →
          AllocLiveAt mem' (translateTy ty) ptr id data) ∧
        (∀ i ptr aid,
          localMapGet? i calleeFrame'.locals = some ptr →
          ptr.allocId = some aid →
          aid ≠ callerRetId ∧
          ∀ j ptr' aid', i ≠ j → localMapGet? j calleeFrame'.locals = some ptr' →
            ptr'.allocId = some aid' → aid ≠ aid') := by
  have haux : ∀ (rem : Nat) (idx : Nat) (calleeFrame : StackFrame) (mem : MrMemory),
      idx + rem = temps.length →
      calleeFrame.func = translateBody body →
      calleeFrame.nextBlock = 0 →
      calleeFrame.nextStmt = idx →
      listGet? calleeFrame.func.blocks 0 =
        some { statements := temps.map MrStatement.storageLive, terminator := .goto 1 } →
      LocalMapNoDup calleeFrame.locals →
      AllocLiveAt mem (translateTy retMirTy) callerRetPtr callerRetId callerRetData →
      (∀ k, k ∈ temps.drop idx → localMapGet? k calleeFrame.locals = none) →
      (∀ k ptr, localMapGet? k calleeFrame.locals = some ptr →
        ∃ ty id data, listGet? body.locals k = some ty ∧
          AllocLiveAt mem (translateTy ty) ptr id data) →
      (∀ i ptr aid,
        localMapGet? i calleeFrame.locals = some ptr →
        ptr.allocId = some aid →
        aid ≠ callerRetId ∧
        ∀ j ptr' aid', i ≠ j → localMapGet? j calleeFrame.locals = some ptr' →
          ptr'.allocId = some aid' → aid ≠ aid') →
      ∃ (calleeFrame' : StackFrame) (mem' : MrMemory),
        MrReaches
          { prog := translateProg p, mem := mem, stack := [calleeFrame, callerFrame] }
          { prog := translateProg p, mem := mem', stack := [calleeFrame', callerFrame] } ∧
        calleeFrame'.func = calleeFrame.func ∧
        calleeFrame'.nextBlock = 1 ∧
        calleeFrame'.nextStmt = 0 ∧
        calleeFrame'.stackPopAction = calleeFrame.stackPopAction ∧
        LocalMapNoDup calleeFrame'.locals ∧
        AllocLiveAt mem' (translateTy retMirTy) callerRetPtr callerRetId callerRetData ∧
        (∀ k, k ∈ temps.drop idx →
          ∃ ty ptr id,
            listGet? body.locals k = some ty ∧
            localMapGet? k calleeFrame'.locals = some ptr ∧
            AllocLiveAt mem' (translateTy ty) ptr id
              (List.replicate (translateTy ty).size.bytes .uninit)) ∧
        (∀ k, ¬ (k ∈ temps.drop idx) →
          localMapGet? k calleeFrame'.locals = localMapGet? k calleeFrame.locals) ∧
        (∀ k ty ptr id data,
          ¬ (k ∈ temps.drop idx) →
          listGet? body.locals k = some ty →
          localMapGet? k calleeFrame.locals = some ptr →
          AllocLiveAt mem (translateTy ty) ptr id data →
          AllocLiveAt mem' (translateTy ty) ptr id data) ∧
        (∀ i ptr aid,
          localMapGet? i calleeFrame'.locals = some ptr →
          ptr.allocId = some aid →
          aid ≠ callerRetId ∧
          ∀ j ptr' aid', i ≠ j → localMapGet? j calleeFrame'.locals = some ptr' →
            ptr'.allocId = some aid' → aid ≠ aid') := by
    intro rem
    induction rem with
    | zero =>
      intro idx calleeFrame mem hsum hfn hblk hstmt hblk0 hnd hcaller _ _ hdisj
      rw [Nat.add_zero] at hsum
      have hdropNil : temps.drop idx = [] := by
        have hlen : (temps.drop idx).length = 0 := by
          rw [list_length_drop, hsum, Nat.sub_self]
        cases hd : temps.drop idx with
        | nil => rfl
        | cons _ _ => rw [hd] at hlen; cases hlen
      have hgetNone : listGet? (temps.map MrStatement.storageLive) idx = none := by
        cases hg : listGet? (temps.map MrStatement.storageLive) idx with
        | none => rfl
        | some s =>
          have hlt := listGet?_lt_length _ idx s hg
          rw [list_length_map, ← hsum] at hlt
          exact False.elim (Nat.lt_irrefl idx hlt)
      have hgotoStep : mrStep { prog := translateProg p, mem := mem, stack := [calleeFrame, callerFrame] } =
          .step { prog := translateProg p, mem := mem, stack := [{ calleeFrame with nextBlock := 1, nextStmt := 0 }, callerFrame] } := by
        dsimp only [mrStep]
        rw [hblk, hblk0]; dsimp only
        rw [hstmt, hgetNone]; dsimp only
        rw [list_length_map, hsum, Nat.beq_refl, if_true_eq_true]
        have hblk1Lt : (!Nat.blt 1 calleeFrame.func.blocks.length) = false := by
          rw [hfn]; dsimp only [translateBody, List.length]
          rw [list_length_map, nat_blt_eq_true_of_lt (Nat.succ_lt_succ hbbPos)]; rfl
        dsimp only [stepTerminator]; rw [hblk1Lt, if_false_eq_true]
      refine ⟨{ calleeFrame with nextBlock := 1, nextStmt := 0 }, mem,
        MrReaches.head hgotoStep (MrReaches.refl _),
        rfl, rfl, rfl, rfl, hnd, hcaller, ?_, fun _ _ => rfl,
        fun _ _ _ _ _ _ _ _ h => h, hdisj⟩
      · intro k hk; rw [hdropNil] at hk; cases hk
    | succ r ih =>
      intro idx calleeFrame mem hsum hfn hblk hstmt hblk0 hnd hcaller hdeadRem hliveCur hdisj
      have hidxLt : idx < temps.length := by
        rw [← hsum, Nat.add_succ]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.succ_le_succ (Nat.le_add_right _ _))
      cases listGet?_some_of_lt temps idx hidxLt with
      | intro k hkGet =>
        have hdropCons : temps.drop idx = k :: temps.drop (idx + 1) := by
          have hgen : ∀ (xs : List Nat) (i : Nat) (x : Nat),
              listGet? xs i = some x → xs.drop i = x :: xs.drop (i + 1) := by
            intro xs; induction xs with
            | nil => intro _ _ hg; cases hg
            | cons a as iha =>
              intro i x hg; cases i with
              | zero => dsimp only [listGet?] at hg; injection hg with hax; subst hax; rfl
              | succ i' => exact iha i' x hg
          exact hgen temps idx k hkGet
        have hkMem : k ∈ temps := by
          have hgen : ∀ (xs : List Nat) (i : Nat) (x : Nat),
              listGet? xs i = some x → x ∈ xs := by
            intro xs; induction xs with
            | nil => intro _ _ hg; cases hg
            | cons a as iha =>
              intro i x hg; cases i with
              | zero =>
                dsimp only [listGet?] at hg; injection hg with hax; subst hax; exact List.Mem.head _
              | succ i' => exact List.Mem.tail _ (iha i' x hg)
          exact hgen temps idx k hkGet
        have hkNotInTail : ¬ (k ∈ temps.drop (idx + 1)) := by
          have hpwDrop : ∀ (xs : List Nat) (i : Nat),
              natListPairwiseNe xs = true → natListPairwiseNe (xs.drop i) = true := by
            intro xs; induction xs with
            | nil => intro i _; cases i <;> rfl
            | cons a as iha =>
              intro i hp; cases i with
              | zero => exact hp
              | succ i' =>
                dsimp only [natListPairwiseNe] at hp
                cases hne : natNotElem a as with
                | false => rw [hne] at hp; cases hp
                | true => rw [hne] at hp; exact iha i' hp
          have hpIdx := hpwDrop temps idx hpw
          rw [hdropCons] at hpIdx
          dsimp only [natListPairwiseNe] at hpIdx
          cases hne : natNotElem k (temps.drop (idx + 1)) with
          | false => rw [hne] at hpIdx; cases hpIdx
          | true =>
            intro hin
            have hmemFalse : ∀ (ys : List Nat), natNotElem k ys = true → ¬ (k ∈ ys) := by
              intro ys; induction ys with
              | nil => intro _ h; cases h
              | cons y ys ihy =>
                intro hneY hmemY; dsimp only [natNotElem] at hneY
                cases hb : Nat.beq k y with
                | true => rw [hb] at hneY; cases hneY
                | false =>
                  rw [hb] at hneY
                  cases hmemY with
                  | head => rw [Nat.beq_refl] at hb; cases hb
                  | tail _ ht => exact ihy hneY ht
            exact hmemFalse _ hne hin
        have hkLt : k < body.locals.length := htempsSpec k hkMem
        cases listGet?_some_of_lt body.locals k hkLt with
        | intro tyK htyK =>
          have htySupp : isSupportedScalarOrUnitTy tyK = true :=
            listGet?_all isSupportedScalarOrUnitTy body.locals k tyK hsupp htyK
          have hvalidAlign := translateTy_validSize_and_alignPos tyK htySupp
          have hmrLoc : listGet? calleeFrame.func.locals k = some (translateTy tyK) := by
            rw [hfn]; dsimp only [translateBody]; rw [listGet?_map, htyK]; rfl
          have hdeadK : localMapGet? k calleeFrame.locals = none :=
            hdeadRem k (by rw [hdropCons]; exact List.Mem.head _)
          cases storageLiveFrame_fresh calleeFrame mem k (translateTy tyK)
              hmrLoc hdeadK hvalidAlign.1 hvalidAlign.2 with
          | intro mem1 hS1 => cases hS1 with | intro ptr1 hS2 => cases hS2 with
            | intro hslOk hS3 => cases hS3 with | intro hlive1 hpres1 =>
              cases localMapInsert_spec k ptr1 calleeFrame.locals hnd with
              | intro hget1 hIns1 => cases hIns1 with | intro hgetOther1 hnd1 =>
                let calleeFrame1 : StackFrame :=
                  { calleeFrame with
                    locals := localMapInsert k ptr1 calleeFrame.locals
                    nextStmt := idx + 1 }
                have hstep1 : mrStep { prog := translateProg p, mem := mem, stack := [calleeFrame, callerFrame] } =
                    .step { prog := translateProg p, mem := mem1, stack := [calleeFrame1, callerFrame] } := by
                  dsimp only [mrStep]
                  rw [hblk, hblk0]; dsimp only
                  rw [hstmt, listGet?_map, hkGet]
                  dsimp only [Option.map, stepStatement]
                  rw [hslOk]; dsimp only
                  rw [hstmt]
                have hcaller1 := hpres1 (translateTy retMirTy) callerRetPtr callerRetId callerRetData hcaller
                have hsum1 : idx + 1 + r = temps.length := by
                  rw [Nat.add_assoc, Nat.add_comm 1 r, ← Nat.add_assoc]; exact hsum
                have hdeadRem1 : ∀ j, j ∈ temps.drop (idx + 1) → localMapGet? j calleeFrame1.locals = none := by
                  intro j hj
                  have hne : j ≠ k := by intro heq; subst heq; exact hkNotInTail hj
                  rw [hgetOther1 j hne]
                  exact hdeadRem j (by rw [hdropCons]; exact List.Mem.tail _ hj)
                have hliveCur1 : ∀ j ptrJ, localMapGet? j calleeFrame1.locals = some ptrJ →
                    ∃ ty id data, listGet? body.locals j = some ty ∧
                      AllocLiveAt mem1 (translateTy ty) ptrJ id data := by
                  intro j ptrJ hgJ
                  cases hjeq : Nat.beq k j with
                  | true =>
                    have heq := Nat.eq_of_beq_eq_true hjeq; subst heq
                    rw [hget1] at hgJ; injection hgJ with hpe; subst hpe
                    exact ⟨tyK, mem.allocations.length,
                      List.replicate (translateTy tyK).size.bytes .uninit, htyK, hlive1⟩
                  | false =>
                    have hne : k ≠ j := by intro h; subst h; rw [Nat.beq_refl] at hjeq; cases hjeq
                    rw [hgetOther1 j (fun h => hne h.symm)] at hgJ
                    cases hliveCur j ptrJ hgJ with
                    | intro tyJ hJ1 => cases hJ1 with | intro idJ hJ2 => cases hJ2 with
                      | intro dataJ hJ3 =>
                        exact ⟨tyJ, idJ, dataJ, hJ3.1, (hpres1 (translateTy tyJ) ptrJ idJ dataJ hJ3.2).2⟩
                have hfreshOld : ∀ j ptrJ aidJ,
                    localMapGet? j calleeFrame.locals = some ptrJ →
                    ptrJ.allocId = some aidJ →
                    aidJ ≠ mem.allocations.length := by
                  intro j ptrJ aidJ hgJ hpidJ
                  cases hliveCur j ptrJ hgJ with
                  | intro tyJ hJ1 => cases hJ1 with | intro idJ hJ2 => cases hJ2 with
                    | intro dataJ hJ3 =>
                      rw [hJ3.2.1] at hpidJ; injection hpidJ with heq; subst heq
                      exact (hpres1 (translateTy tyJ) ptrJ idJ dataJ hJ3.2).1
                have hdisj1 : ∀ i ptrI aidI,
                    localMapGet? i calleeFrame1.locals = some ptrI →
                    ptrI.allocId = some aidI →
                    aidI ≠ callerRetId ∧
                    ∀ j ptrJ aidJ, i ≠ j → localMapGet? j calleeFrame1.locals = some ptrJ →
                      ptrJ.allocId = some aidJ → aidI ≠ aidJ := by
                  intro i ptrI aidI hgI hpidI
                  cases hieq : Nat.beq k i with
                  | true =>
                    have heq := Nat.eq_of_beq_eq_true hieq; subst heq
                    rw [hget1] at hgI; injection hgI with hpe; subst hpe
                    rw [hlive1.1] at hpidI; injection hpidI with hae; subst hae
                    refine ⟨fun h => hcaller1.1 h.symm, fun j ptrJ aidJ hneIJ hgJ hpidJ => ?_⟩
                    rw [hgetOther1 j (fun h => hneIJ h.symm)] at hgJ
                    exact fun h => hfreshOld j ptrJ aidJ hgJ hpidJ h.symm
                  | false =>
                    have hneI : k ≠ i := by intro h; subst h; rw [Nat.beq_refl] at hieq; cases hieq
                    rw [hgetOther1 i (fun h => hneI h.symm)] at hgI
                    cases hdisj i ptrI aidI hgI hpidI with
                    | intro hneC hdisjI =>
                      refine ⟨hneC, fun j ptrJ aidJ hneIJ hgJ hpidJ => ?_⟩
                      cases hjeq : Nat.beq k j with
                      | true =>
                        have heq := Nat.eq_of_beq_eq_true hjeq; subst heq
                        rw [hget1] at hgJ; injection hgJ with hpe; subst hpe
                        rw [hlive1.1] at hpidJ; injection hpidJ with hae; subst hae
                        exact hfreshOld i ptrI aidI hgI hpidI
                      | false =>
                        have hneJ : k ≠ j := by intro h; subst h; rw [Nat.beq_refl] at hjeq; cases hjeq
                        rw [hgetOther1 j (fun h => hneJ h.symm)] at hgJ
                        exact hdisjI j ptrJ aidJ hneIJ hgJ hpidJ
                cases ih (idx + 1) calleeFrame1 mem1 hsum1 hfn hblk rfl hblk0
                    hnd1 hcaller1.2 hdeadRem1 hliveCur1 hdisj1 with
                | intro calleeFrame' hR1 => cases hR1 with | intro mem' hR2 =>
                  cases hR2 with
                  | intro hreach hR3 => cases hR3 with
                    | intro hfn' hR4 => cases hR4 with
                      | intro hblk' hR5 => cases hR5 with
                        | intro hstmt' hR6 => cases hR6 with
                          | intro hpop' hR7 => cases hR7 with
                            | intro hnd' hR8 => cases hR8 with
                              | intro hcaller' hR9 => cases hR9 with
                                | intro hallocTail hR10 => cases hR10 with
                                  | intro hkeepTail hR11 => cases hR11 with
                                    | intro hliveTail hdisj' =>
                                      refine ⟨calleeFrame', mem', MrReaches.head hstep1 hreach,
                                        hfn', hblk', hstmt', hpop', hnd', hcaller', ?_, ?_, ?_, hdisj'⟩
                                      · intro j hj
                                        rw [hdropCons] at hj
                                        cases hj with
                                        | head =>
                                          refine ⟨tyK, ptr1, mem.allocations.length, htyK, ?_, ?_⟩
                                          · rw [hkeepTail k hkNotInTail]; exact hget1
                                          · exact hliveTail k tyK ptr1 mem.allocations.length _
                                              hkNotInTail htyK hget1 hlive1
                                        | tail _ htl => exact hallocTail j htl
                                      · intro j hnotIn
                                        have hneJK : j ≠ k := fun heq =>
                                          hnotIn (by rw [heq, hdropCons]; exact List.Mem.head _)
                                        have hnotTail : ¬ (j ∈ temps.drop (idx + 1)) := fun ht =>
                                          hnotIn (by rw [hdropCons]; exact List.Mem.tail _ ht)
                                        rw [hkeepTail j hnotTail, hgetOther1 j hneJK]
                                      · intro j tyJ ptrJ idJ dataJ hnotIn htyJ hgJ hliveJ
                                        have hneJK : j ≠ k := fun heq =>
                                          hnotIn (by rw [heq, hdropCons]; exact List.Mem.head _)
                                        have hnotTail : ¬ (j ∈ temps.drop (idx + 1)) := fun ht =>
                                          hnotIn (by rw [hdropCons]; exact List.Mem.tail _ ht)
                                        have hgJ1 : localMapGet? j calleeFrame1.locals = some ptrJ := by
                                          rw [hgetOther1 j hneJK]; exact hgJ
                                        exact hliveTail j tyJ ptrJ idJ dataJ hnotTail htyJ hgJ1
                                          (hpres1 (translateTy tyJ) ptrJ idJ dataJ hliveJ).2
  intro idx calleeFrame mem hle
  exact haux (temps.length - idx) idx calleeFrame mem (Nat.add_sub_of_le hle)

/-- Main entry initialization theorem: for any admitted `(p, q)`, both
`initState p q` and `initMrMachine p q` succeed, and MiniRust steps through
`initBlock` to a machine `m₁` satisfying `StateRel exact p s₀ m₁`. -/
theorem init_stateRel (exact : Bool) (p : Program) (q : Query)
    (hadm : if exact then MiniRustExactAdmitted p q else MiniRustAdmitted p q) :
    ∃ s₀ m₀ m₁,
      initState p q = .ok s₀ ∧
      initMrMachine p q = .ok m₀ ∧
      MrReaches m₀ m₁ ∧
      StateRel exact p s₀ m₁ := by
  have hunpack :
      p.pointerWidthBits = 64 ∧
      p.mirProfileVersion = 1 ∧
      q.callerMem.allocations.isEmpty = true ∧
      ∃ body : Body,
        Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body ∧
        bodyAdmittedWith exact body = true ∧
        checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount) = true := by
    cases exact with
    | false =>
      dsimp only [MiniRustAdmitted, MiniRustProgAdmitted] at hadm
      cases hadm with
      | intro hprog hrest => cases hrest with | intro hcm hargs =>
        cases hw : Nat.beq p.pointerWidthBits 64 with
        | false => rw [hw] at hprog; cases hprog
        | true =>
          cases hv : Nat.beq p.mirProfileVersion 1 with
          | false => rw [hw, hv] at hprog; cases hprog
          | true =>
            rw [hw, hv] at hprog
            cases hb : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
            | none => rw [hb] at hprog; cases hprog
            | some body =>
              rw [hb] at hprog hargs
              exact ⟨Nat.eq_of_beq_eq_true hw, Nat.eq_of_beq_eq_true hv, hcm, body, rfl, hprog, hargs⟩
    | true =>
      dsimp only [MiniRustExactAdmitted, MiniRustExactProgAdmitted] at hadm
      cases hadm with
      | intro hprog hrest => cases hrest with | intro hcm hargs =>
        cases hw : Nat.beq p.pointerWidthBits 64 with
        | false => rw [hw] at hprog; cases hprog
        | true =>
          cases hv : Nat.beq p.mirProfileVersion 1 with
          | false => rw [hw, hv] at hprog; cases hprog
          | true =>
            rw [hw, hv] at hprog
            cases hb : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
            | none => rw [hb] at hprog; cases hprog
            | some body =>
              rw [hb] at hprog hargs
              exact ⟨Nat.eq_of_beq_eq_true hw, Nat.eq_of_beq_eq_true hv, hcm, body, rfl, hprog, hargs⟩
  cases hunpack with
  | intro hpw h1 => cases h1 with | intro hpv h2 => cases h2 with
    | intro hcm h3 => cases h3 with | intro body h4 => cases h4 with
      | intro hbody h5 => cases h5 with | intro hbadm hargs =>
        cases bodyAdmittedWith_spec exact body hbadm with
        | intro hbbNe h6 => cases h6 with | intro hargLt h7 => cases h7 with
          | intro hstab h8 => cases h8 with | intro hdiscV h9 => cases h9 with
            | intro hcastV h10 => cases h10 with | intro hsupp hblocksAdm =>
              have h0Lt : 0 < body.locals.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hargLt
              have hbbPos : 0 < body.basicBlocks.length := by
                cases hbb : body.basicBlocks with
                | nil => rw [hbb] at hbbNe; cases hbbNe
                | cons _ _ => exact Nat.zero_lt_succ _
              cases listGet?_some_of_lt body.locals 0 h0Lt with
              | intro retMirTy hretTy =>
                have hretTy' : Trusted.MirSemantics.getElem? body.locals 0 = some retMirTy := by
                  rw [getElem?_eq_listGet?]; exact hretTy
                have hretSupp : isSupportedScalarOrUnitTy retMirTy = true :=
                  listGet?_all isSupportedScalarOrUnitTy body.locals 0 retMirTy hsupp hretTy
                have hretVA := translateTy_validSize_and_alignPos retMirTy hretSupp
                have hcmNil : q.callerMem.allocations = [] := by
                  cases hc : q.callerMem.allocations with
                  | nil => rfl
                  | cons _ _ => rw [hc] at hcm; cases hcm
                have hinitA : initState p q = .ok {
                    frames := [{
                      defId := p.entryDefId
                      blockIdx := 0
                      stmtIdx := 0
                      locals := initLocalsLoop body q.args 0 body.locals
                    }]
                    callerMem := q.callerMem
                    mem := entryMemory
                  } := by
                  dsimp only [initState]
                  rw [hpw, hpv]
                  have hf1 : (!Nat.beq 64 64 || !Nat.beq 1 1) = false := rfl
                  rw [hf1, if_false_eq_true, hcm, if_not_true, hbody]
                  dsimp only
                  rw [hbbNe, if_false_eq_true, nat_blt_eq_true_of_lt hargLt, if_not_true,
                    hstab, if_not_true, hdiscV, if_not_true, hcastV, if_not_true,
                    assertConditionTypesValid_of_blocksAdm exact body hblocksAdm, if_not_true,
                    hsupp, if_not_true,
                    callsAdmitted_of_blocksAdm exact p body hblocksAdm, if_not_true,
                    allCallBodiesStaticAdmitted_of_blocksAdm exact p body hblocksAdm, if_not_true,
                    hargs, if_not_true]
                -- Step 1: allocate callerRetPtr in MrMemory.empty
                cases allocLiveAt_allocate MrMemory.empty (translateTy retMirTy)
                    hretVA.1 hretVA.2 with
                | intro mem1 hC1 => cases hC1 with | intro callerRetPtr hC2 =>
                  cases hC2 with | intro hallocCaller hC3 => cases hC3 with
                    | intro hcallerLive1 _ =>
                      let callerFrame : StackFrame := {
                        func := harnessCallerFunc (translateTy retMirTy)
                        locals := [(0, callerRetPtr)]
                        stackPopAction := .bottomOfStack
                        nextBlock := 0
                        nextStmt := 0
                      }
                      let calleeFrame0 : StackFrame := {
                        func := translateBody body
                        locals := []
                        stackPopAction := .backToCaller callerRetPtr (some 0)
                        nextBlock := 0
                        nextStmt := 0
                      }
                      -- Step 2: allocate _0 in calleeFrame0
                      have hloc0 : listGet? calleeFrame0.func.locals 0 = some (translateTy retMirTy) := by
                        dsimp only [calleeFrame0, translateBody]; rw [listGet?_map, hretTy]; rfl
                      cases storageLiveFrame_fresh calleeFrame0 mem1 0 (translateTy retMirTy)
                          hloc0 rfl hretVA.1 hretVA.2 with
                      | intro mem2 hR01 => cases hR01 with | intro retPtr hR02 =>
                        cases hR02 with | intro hsl0 hR03 => cases hR03 with
                          | intro hliveRet0 hpres0 =>
                            have hcallerLive2 := hpres0 (translateTy retMirTy) callerRetPtr 0
                              (List.replicate (translateTy retMirTy).size.bytes .uninit) hcallerLive1
                            let calleeFrame1 : StackFrame :=
                              { calleeFrame0 with locals := localMapInsert 0 retPtr calleeFrame0.locals }
                            -- Step 3: initMrArgsLoop for _1 .. _argumentCount
                            have hargsLen : q.args.length = body.argumentCount := by
                              have h1 := checkArgsMatch_length q.args
                                ((body.locals.drop 1).take body.argumentCount) hargs
                              have hleDrop : body.argumentCount ≤ (body.locals.drop 1).length := by
                                rw [list_length_drop]
                                exact Nat.le_sub_of_add_le hargLt
                              rw [list_length_take_of_le _ _ hleDrop] at h1
                              exact h1
                            have hleArgs : 1 + q.args.length ≤ body.locals.length := by
                              rw [hargsLen, Nat.add_comm]; exact hargLt
                            have hargsMatch' : checkArgsMatch q.args
                                ((body.locals.drop 1).take q.args.length) = true := by
                              rw [hargsLen]; exact hargs
                            have hnd1 : LocalMapNoDup calleeFrame1.locals := ⟨rfl, True.intro⟩
                            have hlt1 : ∀ k ptr, localMapGet? k calleeFrame1.locals = some ptr → k < 1 := by
                              intro k ptr hg
                              dsimp only [calleeFrame1, localMapInsert, calleeFrame0, localMapGet?] at hg
                              cases hb : Nat.beq 0 k with
                              | true =>
                                have heq := Nat.eq_of_beq_eq_true hb; subst heq; exact Nat.zero_lt_succ 0
                              | false => rw [hb, if_false_eq_true] at hg; cases hg
                            have hlivePre1 : ∀ k ty ptr, k < 1 →
                                listGet? body.locals k = some ty →
                                localMapGet? k calleeFrame1.locals = some ptr →
                                ∃ id data, AllocLiveAt mem2 (translateTy ty) ptr id data := by
                              intro k ty ptr hk htyK hg
                              have hk0 : k = 0 := by
                                cases k with | zero => rfl | succ k' => exact False.elim (Nat.not_lt_zero k' (Nat.lt_of_succ_lt_succ hk))
                              subst hk0
                              rw [hretTy] at htyK; injection htyK with hte; subst hte
                              dsimp only [calleeFrame1, localMapInsert, calleeFrame0, localMapGet?] at hg
                              rw [Nat.beq_refl, if_true_eq_true] at hg; injection hg with hpe; subst hpe
                              exact ⟨mem1.allocations.length, _, hliveRet0⟩
                            have hdisj1 : ∀ i ptr aid,
                                localMapGet? i calleeFrame1.locals = some ptr →
                                ptr.allocId = some aid →
                                aid ≠ 0 ∧
                                ∀ j ptr' aid', i ≠ j → localMapGet? j calleeFrame1.locals = some ptr' →
                                  ptr'.allocId = some aid' → aid ≠ aid' := by
                              intro i ptr aid hg hpid
                              have hi0 : i = 0 := by
                                have hlt := hlt1 i ptr hg
                                cases i with | zero => rfl | succ i' => exact False.elim (Nat.not_lt_zero i' (Nat.lt_of_succ_lt_succ hlt))
                              subst hi0
                              dsimp only [calleeFrame1, localMapInsert, calleeFrame0, localMapGet?] at hg
                              rw [Nat.beq_refl, if_true_eq_true] at hg; injection hg with hpe; subst hpe
                              rw [hliveRet0.1] at hpid; injection hpid with hae; subst hae
                              refine ⟨fun h => hcallerLive2.1 h.symm, fun j ptrJ _ hne hgJ _ => ?_⟩
                              have hj0 : j = 0 := by
                                have hlt := hlt1 j ptrJ hgJ
                                cases j with | zero => rfl | succ j' => exact False.elim (Nat.not_lt_zero j' (Nat.lt_of_succ_lt_succ hlt))
                              exact False.elim (hne hj0.symm)
                            cases initMrArgsLoop_spec body retMirTy callerRetPtr 0
                                (List.replicate (translateTy retMirTy).size.bytes .uninit) hsupp
                                q.args 1 calleeFrame1 mem2 rfl (Nat.le_refl 1) hleArgs hargsMatch'
                                hnd1 hcallerLive2.2 hlt1 hlivePre1 hdisj1 with
                            | intro calleeFrame2 hA1 => cases hA1 with | intro mem3 hA2 =>
                              cases hA2 with | intro hargsOk hA3 => cases hA3 with
                                | intro hfn2 hA4 => cases hA4 with | intro hblk2 hA5 =>
                                  cases hA5 with | intro hstmt2 hA6 => cases hA6 with
                                    | intro hpop2 hA7 => cases hA7 with | intro hnd2 hA8 =>
                                      cases hA8 with | intro hcaller3 hA9 => cases hA9 with
                                        | intro hlt2 hA10 => cases hA10 with | intro hkeep0 hA11 =>
                                          cases hA11 with | intro hlive0 hA12 => cases hA12 with
                                            | intro hargSlots hdisj2 =>
                                              have hinitM : initMrMachine p q = .ok {
                                                  prog := translateProg p
                                                  mem := mem3
                                                  stack := [calleeFrame2, callerFrame]
                                                } := by
                                                dsimp only [initMrMachine]
                                                rw [hpw, hpv]
                                                have hf1 : (!Nat.beq 64 64 || !Nat.beq 1 1) = false := rfl
                                                rw [hf1, if_false_eq_true, hcm, if_not_true, hbody]
                                                dsimp only
                                                rw [hretTy']
                                                dsimp only
                                                rw [hallocCaller]
                                                dsimp only
                                                rw [hsl0]
                                                dsimp only
                                                rw [hargsOk]
                                              have htempsAll := alwaysLiveTempsAux_spec body 0 body.locals
                                              have htempsSpec : ∀ k, k ∈ alwaysLiveTemps body → k < body.locals.length := by
                                                intro k hk
                                                have h := (htempsAll.1 k hk).2.1
                                                rw [Nat.zero_add] at h; exact h
                                              have hdeadTemps : ∀ k, k ∈ (alwaysLiveTemps body).drop 0 →
                                                  localMapGet? k calleeFrame2.locals = none := by
                                                intro k hk
                                                have hgtArg : body.argumentCount < k := (htempsAll.1 k hk).2.2.1
                                                cases hg : localMapGet? k calleeFrame2.locals with
                                                | none => rfl
                                                | some ptr =>
                                                  have hltK := hlt2 k ptr hg
                                                  rw [hargsLen, Nat.add_comm] at hltK
                                                  exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt_succ hltK) hgtArg)
                                              have hliveCur2 : ∀ k ptr, localMapGet? k calleeFrame2.locals = some ptr →
                                                  ∃ ty id data, listGet? body.locals k = some ty ∧
                                                    AllocLiveAt mem3 (translateTy ty) ptr id data := by
                                                intro k ptr hg
                                                have hltK := hlt2 k ptr hg
                                                rw [hargsLen] at hltK
                                                cases k with
                                                | zero =>
                                                  rw [hkeep0 0 (Nat.zero_lt_succ 0)] at hg
                                                  dsimp only [calleeFrame1, localMapInsert, calleeFrame0, localMapGet?] at hg
                                                  rw [Nat.beq_refl, if_true_eq_true] at hg; injection hg with hpe; subst hpe
                                                  exact ⟨retMirTy, mem1.allocations.length, _, hretTy,
                                                    hlive0 0 retMirTy retPtr mem1.allocations.length _
                                                      (Nat.zero_lt_succ 0) hretTy
                                                      (by dsimp only [calleeFrame1, localMapInsert, calleeFrame0, localMapGet?]; rw [Nat.beq_refl, if_true_eq_true])
                                                      hliveRet0⟩
                                                | succ k' =>
                                                  have hk'Lt : k' < q.args.length := by
                                                    rw [hargsLen]; rw [Nat.add_comm] at hltK; exact Nat.lt_of_succ_lt_succ hltK
                                                  cases listGet?_some_of_lt q.args k' hk'Lt with
                                                  | intro vK hvK =>
                                                    have hskLt : Nat.succ k' < body.locals.length :=
                                                      Nat.lt_of_lt_of_le (by rw [← hargsLen] at hltK; exact hltK) hleArgs
                                                    cases listGet?_some_of_lt body.locals (1 + k') (by rw [Nat.add_comm]; exact hskLt) with
                                                    | intro tyK htyK =>
                                                      cases hargSlots k' vK tyK hvK htyK with
                                                      | intro ptrK hK1 => cases hK1 with | intro idK hK2 => cases hK2 with
                                                        | intro dataK hK3 =>
                                                          rw [Nat.add_comm] at htyK
                                                          have hskEq : 1 + k' = Nat.succ k' := Nat.add_comm 1 k'
                                                          rw [hskEq] at hK3
                                                          rw [hg] at hK3; injection hK3.1 with hpe; subst hpe
                                                          exact ⟨tyK, idK, dataK, htyK, hK3.2.1⟩
                                              have hblk0 : listGet? calleeFrame2.func.blocks 0 =
                                                  some { statements := (alwaysLiveTemps body).map MrStatement.storageLive, terminator := .goto 1 } := by
                                                rw [hfn2]; rfl
                                              cases runInitBlock_steps p body retMirTy callerRetPtr 0
                                                  (List.replicate (translateTy retMirTy).size.bytes .uninit)
                                                  callerFrame hbbPos hsupp (alwaysLiveTemps body) htempsSpec htempsAll.2.1
                                                  0 calleeFrame2 mem3 (Nat.zero_le _) hfn2 hblk2 hstmt2 hblk0
                                                  hnd2 hcaller3 hdeadTemps hliveCur2 hdisj2 with
                                              | intro calleeFrame3 hB1 => cases hB1 with | intro mem4 hB2 =>
                                                cases hB2 with | intro hreach hB3 => cases hB3 with
                                                  | intro hfn3 hB4 => cases hB4 with | intro hblk3 hB5 =>
                                                    cases hB5 with | intro hstmt3 hB6 => cases hB6 with
                                                      | intro hpop3 hB7 => cases hB7 with | intro hnd3 hB8 =>
                                                        cases hB8 with | intro hcaller4 hB9 => cases hB9 with
                                                          | intro hallocT hB10 => cases hB10 with | intro hkeepT hB11 =>
                                                            cases hB11 with | intro hliveT hdisj3 =>
                                                              refine ⟨_, _, _, hinitA, hinitM, hreach, ?_⟩
                                                              refine ⟨hpw, hpv, hcmNil, body,
                                                                { defId := p.entryDefId, blockIdx := 0, stmtIdx := 0,
                                                                  locals := initLocalsLoop body q.args 0 body.locals },
                                                                calleeFrame3, callerFrame, callerRetPtr, 0,
                                                                List.replicate (translateTy retMirTy).size.bytes .uninit,
                                                                retMirTy, hbody, hbadm, hretTy', rfl, rfl, rfl,
                                                                initLocalsLoop_length body q.args 0 body.locals,
                                                                hbbPos, rfl, rfl, Eq.trans hfn3 hfn2, hblk3, hstmt3,
                                                                Eq.trans hpop3 hpop2, rfl, hcaller4, hnd3, ?_, ?_, ?_, hdisj3⟩
                                                              -- _0 is live
                                                              · have hg0 := initLocalsLoop_getElem? body q.args 0 body.locals 0 retMirTy hretTy
                                                                rw [getElem?_eq_listGet?, hg0]
                                                                dsimp only [Nat.add_zero]
                                                                have h0b : Nat.beq 0 0 = true := rfl
                                                                rw [h0b, if_true_eq_true]
                                                                cases liveUninitSlot_isImmediate retMirTy with
                                                                | intro ov hov => exact ⟨ov, congrArg some hov⟩
                                                              · intro k ptrK hgK
                                                                cases hble : Nat.ble k body.argumentCount with
                                                                | true =>
                                                                  have hkLe : k ≤ body.argumentCount := Nat.le_of_ble_eq_true hble
                                                                  have hkLt : k < body.locals.length := Nat.lt_of_le_of_lt hkLe hargLt
                                                                  refine ⟨hkLt, ?_⟩
                                                                  cases listGet?_some_of_lt body.locals k hkLt with
                                                                  | intro tyK htyK =>
                                                                    rw [getElem?_eq_listGet?, initLocalsLoop_getElem? body q.args 0 body.locals k tyK htyK]
                                                                    rw [Nat.zero_add]; dsimp only
                                                                    cases k with
                                                                    | zero =>
                                                                      have h0b : Nat.beq 0 0 = true := rfl
                                                                      rw [h0b, if_true_eq_true]
                                                                      cases liveUninitSlot_isImmediate tyK with
                                                                      | intro ov hov => exact ⟨ov, congrArg some hov⟩
                                                                    | succ k' =>
                                                                      have hnb : Nat.beq (Nat.succ k') 0 = false := rfl
                                                                      rw [hnb, if_false_eq_true, hble, if_true_eq_true]
                                                                      have hk'Lt : k' < q.args.length := by
                                                                        rw [hargsLen]; exact Nat.lt_of_succ_le hkLe
                                                                      cases listGet?_some_of_lt q.args k' hk'Lt with
                                                                      | intro vK hvK =>
                                                                        have hsub : Nat.succ k' - 1 = k' := rfl
                                                                        rw [getElem?_eq_listGet?, hsub, hvK]
                                                                        exact ⟨some vK, rfl⟩
                                                                | false =>
                                                                  have hkGt : body.argumentCount < k := by
                                                                    cases Nat.lt_or_ge body.argumentCount k with
                                                                    | inl h => exact h
                                                                    | inr hle => rw [Nat.ble_eq_true_of_le hle] at hble; cases hble
                                                                  have hnotOld : localMapGet? k calleeFrame2.locals = none := by
                                                                    cases hg2 : localMapGet? k calleeFrame2.locals with
                                                                    | none => rfl
                                                                    | some ptr2 =>
                                                                      have hlt2K := hlt2 k ptr2 hg2
                                                                      rw [hargsLen, Nat.add_comm] at hlt2K
                                                                      exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt_succ hlt2K) hkGt)
                                                                  have hkIn : k ∈ alwaysLiveTemps body := by
                                                                    cases hnotIn : (if hasStorageAnnotation body k then false else true) with
                                                                    | true =>
                                                                      have hnoS : hasStorageAnnotation body k = false := by
                                                                        cases hs : hasStorageAnnotation body k with
                                                                        | false => rfl | true => rw [hs] at hnotIn; cases hnotIn
                                                                      cases Nat.lt_or_ge k body.locals.length with
                                                                      | inl hkLt =>
                                                                        have h := htempsAll.2.2 k hkLt (by rw [Nat.zero_add]; exact hkGt)
                                                                          (by rw [Nat.zero_add]; exact hnoS)
                                                                        rw [Nat.zero_add] at h; exact h
                                                                      | inr hkGe =>
                                                                        have hnotMem : ¬ (k ∈ (alwaysLiveTemps body).drop 0) := by
                                                                          intro hm; exact Nat.not_lt_of_ge hkGe (htempsSpec k hm)
                                                                        rw [hkeepT k hnotMem, hnotOld] at hgK; cases hgK
                                                                    | false =>
                                                                      have hhasS : hasStorageAnnotation body k = true := by
                                                                        cases hs : hasStorageAnnotation body k with
                                                                        | true => rfl | false => rw [hs] at hnotIn; cases hnotIn
                                                                      have hnotMem : ¬ (k ∈ (alwaysLiveTemps body).drop 0) := by
                                                                        intro hm
                                                                        have hf := (htempsAll.1 k hm).2.2.2
                                                                        rw [hhasS] at hf; cases hf
                                                                      rw [hkeepT k hnotMem, hnotOld] at hgK; cases hgK
                                                                  have hkLt : k < body.locals.length := htempsSpec k hkIn
                                                                  have hnoS : hasStorageAnnotation body k = false := (htempsAll.1 k hkIn).2.2.2
                                                                  refine ⟨hkLt, ?_⟩
                                                                  cases listGet?_some_of_lt body.locals k hkLt with
                                                                  | intro tyK htyK =>
                                                                    rw [getElem?_eq_listGet?, initLocalsLoop_getElem? body q.args 0 body.locals k tyK htyK]
                                                                    rw [Nat.zero_add]; dsimp only
                                                                    have hne0 : Nat.beq k 0 = false := by
                                                                      cases k with
                                                                      | zero => exact False.elim (Nat.not_lt_zero _ hkGt)
                                                                      | succ _ => rfl
                                                                    rw [hne0, if_false_eq_true, hble, if_false_eq_true, hnoS, if_false_eq_true]
                                                                    cases liveUninitSlot_isImmediate tyK with
                                                                    | intro ov hov => exact ⟨ov, congrArg some hov⟩
                                                              · intro i tyI slotI htyI hslotI
                                                                rw [getElem?_eq_listGet?] at htyI hslotI
                                                                rw [initLocalsLoop_getElem? body q.args 0 body.locals i tyI htyI] at hslotI
                                                                rw [Nat.zero_add] at hslotI
                                                                injection hslotI with hsl; subst hsl
                                                                dsimp only
                                                                have htyISupp : isSupportedScalarOrUnitTy tyI = true :=
                                                                  listGet?_all isSupportedScalarOrUnitTy body.locals i tyI hsupp htyI
                                                                cases hi0 : Nat.beq i 0 with
                                                                | true =>
                                                                  have heq := Nat.eq_of_beq_eq_true hi0; subst heq
                                                                  rw [if_true_eq_true]
                                                                  rw [hretTy] at htyI; injection htyI with hte; subst hte
                                                                  have hnotT0 : ¬ (0 ∈ (alwaysLiveTemps body).drop 0) := by
                                                                    intro hm; exact Nat.not_lt_zero _ (htempsAll.1 0 hm).2.2.1
                                                                  have hg02 : localMapGet? 0 calleeFrame2.locals = some retPtr := by
                                                                    rw [hkeep0 0 (Nat.zero_lt_succ 0)]
                                                                    dsimp only [calleeFrame1, localMapInsert, calleeFrame0, localMapGet?]
                                                                    rw [Nat.beq_refl, if_true_eq_true]
                                                                  have hlive02 := hlive0 0 retMirTy retPtr mem1.allocations.length _
                                                                    (Nat.zero_lt_succ 0) hretTy
                                                                    (by dsimp only [calleeFrame1, localMapInsert, calleeFrame0, localMapGet?]; rw [Nat.beq_refl, if_true_eq_true])
                                                                    hliveRet0
                                                                  rw [hkeepT 0 hnotT0, hg02]
                                                                  exact liveUninitSlot_slotRel exact mem4 retMirTy retPtr
                                                                    mem1.allocations.length hretSupp
                                                                    (hliveT 0 retMirTy retPtr mem1.allocations.length _
                                                                      hnotT0 hretTy hg02 hlive02)
                                                                | false =>
                                                                  rw [if_false_eq_true]
                                                                  cases hble : Nat.ble i body.argumentCount with
                                                                  | true =>
                                                                    rw [if_true_eq_true]
                                                                    have hiLe : i ≤ body.argumentCount := Nat.le_of_ble_eq_true hble
                                                                    have hnotTi : ¬ (i ∈ (alwaysLiveTemps body).drop 0) := by
                                                                      intro hm
                                                                      exact Nat.not_lt_of_ge hiLe (htempsAll.1 i hm).2.2.1
                                                                    cases i with
                                                                    | zero => cases hi0
                                                                    | succ i' =>
                                                                      have hi'Lt : i' < q.args.length := by
                                                                        rw [hargsLen]; exact Nat.lt_of_succ_le hiLe
                                                                      cases listGet?_some_of_lt q.args i' hi'Lt with
                                                                      | intro vI hvI =>
                                                                        rw [getElem?_eq_listGet?, Nat.add_sub_cancel, hvI]
                                                                        have h1i : 1 + i' = Nat.succ i' := Nat.add_comm 1 i'
                                                                        have htyI' : listGet? body.locals (1 + i') = some tyI := by rw [h1i]; exact htyI
                                                                        cases hargSlots i' vI tyI hvI htyI' with
                                                                        | intro ptrI hI1 => cases hI1 with | intro idI hI2 => cases hI2 with
                                                                          | intro dataI hI3 =>
                                                                            rw [h1i] at hI3
                                                                            rw [hkeepT (Nat.succ i') hnotTi, hI3.1]
                                                                            exact ⟨ptrI, idI, dataI, rfl,
                                                                              hliveT (Nat.succ i') tyI ptrI idI dataI
                                                                                hnotTi htyI hI3.1 hI3.2.1,
                                                                              hI3.2.2⟩
                                                                  | false =>
                                                                    rw [if_false_eq_true]
                                                                    have hiGt : body.argumentCount < i := by
                                                                      cases Nat.lt_or_ge body.argumentCount i with
                                                                      | inl h => exact h
                                                                      | inr hle => rw [Nat.ble_eq_true_of_le hle] at hble; cases hble
                                                                    cases hhasS : hasStorageAnnotation body i with
                                                                    | true =>
                                                                      rw [if_true_eq_true]
                                                                      have hnotTi : ¬ (i ∈ (alwaysLiveTemps body).drop 0) := by
                                                                        intro hm
                                                                        have hf := (htempsAll.1 i hm).2.2.2
                                                                        rw [hhasS] at hf; cases hf
                                                                      dsimp only [SlotRel]
                                                                      rw [hkeepT i hnotTi]
                                                                      cases hg2 : localMapGet? i calleeFrame2.locals with
                                                                      | none => rfl
                                                                      | some ptr2 =>
                                                                        have hlt2I := hlt2 i ptr2 hg2
                                                                        rw [hargsLen, Nat.add_comm] at hlt2I
                                                                        exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt_succ hlt2I) hiGt)
                                                                    | false =>
                                                                      rw [if_false_eq_true]
                                                                      have hiLt : i < body.locals.length := listGet?_lt_length body.locals i tyI htyI
                                                                      have hiIn : i ∈ (alwaysLiveTemps body).drop 0 := by
                                                                        have h := htempsAll.2.2 i hiLt
                                                                          (by rw [Nat.zero_add]; exact hiGt)
                                                                          (by rw [Nat.zero_add]; exact hhasS)
                                                                        rw [Nat.zero_add] at h; exact h
                                                                      cases hallocT i hiIn with
                                                                      | intro tyT hT1 => cases hT1 with | intro ptrT hT2 => cases hT2 with
                                                                        | intro idT hT3 =>
                                                                          rw [htyI] at hT3
                                                                          injection hT3.1 with hte; subst hte
                                                                          rw [hT3.2.1]
                                                                          exact liveUninitSlot_slotRel exact mem4 tyI ptrT idT htyISupp hT3.2.2

/-! ## SwitchInt Branch Correspondence Lemmas -/

theorem switchBranches_int_sim (numBlocks : Nat) (w : IntWidth) (s : Bool)
    (sv : ScalarVal) (otherwise : BasicBlockId)
    (hw : sv.width = w) (hs : sv.signed = s) (hwf : truncateBits w sv.bits = sv.bits)
    (hoth : otherwise < numBlocks) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)),
      switchBranchesAdmitted numBlocks (.int w s) branches = true →
      ∃ target,
        evalSwitchBranches w sv.bits otherwise branches = .ok target ∧
        target < numBlocks ∧
        lookupSwitchCase (decodeScalar sv) (otherwise + 1)
          (translateIntSwitchBranches w s branches) = target + 1 := by
  intro branches
  induction branches with
  | nil =>
    intro _
    exact ⟨otherwise, rfl, hoth, rfl⟩
  | cons entry rest ih =>
    cases entry with
    | mk caseBits target =>
      intro hadm
      dsimp only [switchBranchesAdmitted] at hadm
      cases htLt : Nat.blt target numBlocks with
      | false => rw [htLt] at hadm; cases hadm
      | true =>
        cases htr : (truncateBits w caseBits == caseBits) with
        | false => rw [htLt, htr] at hadm; cases hadm
        | true =>
          rw [htLt, htr] at hadm
          have htruncC : truncateBits w caseBits = caseBits := eq_of_beq htr
          have hneC : (truncateBits w caseBits != caseBits) = false := by
            dsimp only [bne]; rw [htr]; rfl
          have hkeyEq : (decodeScalar ⟨w, s, caseBits⟩ == decodeScalar sv) =
              (truncateBits w sv.bits == truncateBits w caseBits) := by
            cases sv with
            | mk svw svs svb =>
              dsimp only at hw hs hwf
              have hw' := hw.symm; have hs' := hs.symm; subst hw'; subst hs'
              cases hb1 : (decodeScalar ⟨w, s, caseBits⟩ == decodeScalar ⟨w, s, svb⟩) with
              | true =>
                have heq := eq_of_beq hb1
                have h1 := intEmodNat_decodeScalar w s caseBits
                have h2 := intEmodNat_decodeScalar w s svb
                rw [heq] at h1
                have hbv : truncateBits w svb = truncateBits w caseBits :=
                  bv_eq_of_toNat_eq (Eq.trans h2.symm h1)
                rw [hbv, beq_self_eq_true]
              | false =>
                cases hb2 : (truncateBits w svb == truncateBits w caseBits) with
                | false => rfl
                | true =>
                  have heq := eq_of_beq hb2
                  rw [hwf, htruncC] at heq
                  rw [heq, beq_self_eq_true] at hb1; cases hb1
          dsimp only [evalSwitchBranches, translateIntSwitchBranches, lookupSwitchCase]
          rw [hneC, if_false_eq_true, hkeyEq]
          cases hcmp : (truncateBits w sv.bits == truncateBits w caseBits) with
          | true =>
            rw [if_true_eq_true, if_true_eq_true]
            exact ⟨target, rfl, nat_lt_of_blt_eq_true htLt, rfl⟩
          | false =>
            rw [if_false_eq_true, if_false_eq_true]
            exact ih hadm

theorem switchBranches_bool_sim (numBlocks : Nat) (b : Bool)
    (otherwise : BasicBlockId) (hoth : otherwise < numBlocks) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)),
      switchBranchesAdmitted numBlocks .bool branches = true →
      ∃ target,
        evalBoolSwitchBranches b otherwise branches = .ok target ∧
        target < numBlocks ∧
        lookupSwitchCase (if b then 1 else 0) (otherwise + 1)
          (translateNatSwitchBranches branches) = target + 1 := by
  intro branches
  induction branches with
  | nil =>
    intro _
    exact ⟨otherwise, rfl, hoth, rfl⟩
  | cons entry rest ih =>
    cases entry with
    | mk caseBits target =>
      intro hadm
      dsimp only [switchBranchesAdmitted] at hadm
      cases htLt : Nat.blt target numBlocks with
      | false => rw [htLt] at hadm; cases hadm
      | true =>
        cases htr : (truncateBits .i8 caseBits == caseBits) with
        | false => rw [htLt, htr] at hadm; cases hadm
        | true =>
          cases h01 : (Nat.beq caseBits.toNat 0 || Nat.beq caseBits.toNat 1) with
          | false => rw [htLt, htr, h01] at hadm; cases hadm
          | true =>
            rw [htLt, htr, h01] at hadm
            have htrunc : truncateBits .i8 caseBits = caseBits := eq_of_beq htr
            have hne : (truncateBits .i8 caseBits != caseBits) = false := by
              dsimp only [bne]; rw [htr]; rfl
            dsimp only [evalBoolSwitchBranches, evalConstLit, translateNatSwitchBranches, lookupSwitchCase]
            rw [hne, if_false_eq_true, htrunc]
            cases h0 : Nat.beq caseBits.toNat 0 with
            | true =>
              have hz : caseBits.toNat = 0 := Nat.eq_of_beq_eq_true h0
              rw [hz]
              cases b with
              | false => exact ⟨target, rfl, nat_lt_of_blt_eq_true htLt, rfl⟩
              | true => exact ih hadm
            | false =>
              rw [h0] at h01
              have h1 : caseBits.toNat = 1 := Nat.eq_of_beq_eq_true h01
              rw [h1]
              cases b with
              | false => exact ih hadm
              | true => exact ⟨target, rfl, nat_lt_of_blt_eq_true htLt, rfl⟩

theorem switchBranches_char_sim (numBlocks : Nat) (c : Char)
    (otherwise : BasicBlockId) (hoth : otherwise < numBlocks) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)),
      switchBranchesAdmitted numBlocks .char branches = true →
      ∃ target,
        evalCharSwitchBranches c otherwise branches = .ok target ∧
        target < numBlocks ∧
        lookupSwitchCase (Int.ofNat c.toNat) (otherwise + 1)
          (translateNatSwitchBranches branches) = target + 1 := by
  intro branches
  induction branches with
  | nil =>
    intro _
    exact ⟨otherwise, rfl, hoth, rfl⟩
  | cons entry rest ih =>
    cases entry with
    | mk caseBits target =>
      intro hadm
      dsimp only [switchBranchesAdmitted] at hadm
      cases htLt : Nat.blt target numBlocks with
      | false => rw [htLt] at hadm; cases hadm
      | true =>
        cases htr : (truncateBits .i32 caseBits == caseBits) with
        | false => rw [htLt, htr] at hadm; cases hadm
        | true =>
          cases hu : isUnicodeScalar caseBits.toNat with
          | false => rw [htLt, htr, hu] at hadm; cases hadm
          | true =>
            rw [htLt, htr, hu] at hadm
            have hne : (truncateBits .i32 caseBits != caseBits) = false := by
              dsimp only [bne]; rw [htr]; rfl
            have hcharToNat : (Char.ofNat caseBits.toNat).toNat = caseBits.toNat := by
              have hvalid : caseBits.toNat.isValidChar := by
                dsimp only [isUnicodeScalar] at hu
                dsimp only [Nat.isValidChar]
                cases hle1 : Nat.ble caseBits.toNat 0x10ffff with
                | false => rw [hle1] at hu; cases hu
                | true =>
                  rw [hle1] at hu
                  cases hgeD8 : Nat.ble 0xd800 caseBits.toNat with
                  | false =>
                    left
                    exact Nat.lt_of_not_le (fun h => by rw [Nat.ble_eq_true_of_le h] at hgeD8; cases hgeD8)
                  | true =>
                    rw [hgeD8] at hu
                    cases hleDF : Nat.ble caseBits.toNat 0xdfff with
                    | true => rw [hleDF] at hu; cases hu
                    | false =>
                      right
                      exact ⟨Nat.lt_of_not_le (fun h => by rw [Nat.ble_eq_true_of_le h] at hleDF; cases hleDF),
                        Nat.lt_succ_of_le (Nat.le_of_ble_eq_true hle1)⟩
              dsimp only [Char.ofNat, Char.toNat, Char.ofNatAux]
              simp only [hvalid, dite_true]
              rfl
            have hkeyEq : (Int.ofNat caseBits.toNat == Int.ofNat c.toNat) =
                Nat.beq c.toNat caseBits.toNat := by
              cases hb1 : (Int.ofNat caseBits.toNat == Int.ofNat c.toNat) with
              | true =>
                have heq := eq_of_beq hb1
                injection heq with hne2; rw [hne2, Nat.beq_refl]
              | false =>
                cases hb2 : Nat.beq c.toNat caseBits.toNat with
                | false => rfl
                | true =>
                  have heq := Nat.eq_of_beq_eq_true hb2
                  rw [heq, beq_self_eq_true] at hb1; cases hb1
            dsimp only [evalCharSwitchBranches, evalConstLit, translateNatSwitchBranches, lookupSwitchCase]
            rw [hne, if_false_eq_true, hu, if_true_eq_true]
            dsimp only
            rw [hcharToNat, hkeyEq]
            cases hcmp : Nat.beq c.toNat caseBits.toNat with
            | true =>
              rw [if_true_eq_true, if_true_eq_true]
              exact ⟨target, rfl, nat_lt_of_blt_eq_true htLt, rfl⟩
            | false =>
              rw [if_false_eq_true, if_false_eq_true]
              exact ih hadm

/-! ## Single-Step Lockstep Simulation (`evalStep_sim_core`) -/

/-- Helper: `s.callerMem.allocations = []` implies `s.callerMem = ⟨[]⟩`. -/
theorem callerMem_eq_empty (cm : CallerMemory) (h : cm.allocations = []) :
    cm = ⟨[]⟩ := by
  cases cm with
  | mk allocs =>
    dsimp only at h; subst h; rfl

/-- Helper: `id` strictly past `start + count - 1` never appears in
`rangeNat start count`. -/
theorem rangeNat_any_beq_false :
    ∀ (count start id : Nat), start + count ≤ id →
      (rangeNat start count).any (Nat.beq id) = false
  | 0, _, _, _ => rfl
  | c + 1, start, id, hle => by
    dsimp only [rangeNat, List.any]
    have hlt : start < id :=
      Nat.lt_of_lt_of_le
        (by
          rw [Nat.add_succ]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
            (Nat.succ_le_succ (Nat.le_add_right start c)))
        hle
    have hbeq : Nat.beq id start = false := by
      cases hb : Nat.beq id start with
      | false => rfl
      | true =>
        rw [Nat.eq_of_beq_eq_true hb] at hlt
        exact False.elim (Nat.lt_irrefl _ hlt)
    rw [hbeq, Bool.false_or]
    exact rangeNat_any_beq_false c (start + 1) id
      (by rw [Nat.add_assoc, Nat.add_comm 1 c, ← Nat.add_assoc]; exact hle)

/-- Statement-index in-bounds invariant paired with `StateRel`:
`frame.stmtIdx ≤ bb.statements.length`. -/
def StmtIdxInBounds (p : Program) (s : State) : Prop :=
  ∀ (body : Body) (frame : FrameState) (bb : BasicBlock),
    s.frames = [frame] →
    Trusted.MirSemantics.getElem? p.bodies frame.defId = some body →
    Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb →
    frame.stmtIdx ≤ bb.statements.length

/-- Full simulation invariant pairing `StateRel` with `StmtIdxInBounds`. -/
def FullStateRel (exact : Bool) (p : Program) (s : State) (m : Machine) : Prop :=
  StateRel exact p s m ∧ StmtIdxInBounds p s

/-- Core single-step correspondence under `StateRel` and `StmtIdxInBounds`.
Covers every admitted statement (`.nop`, `.storageLive`, `.storageDead`,
`.assign`) and terminator (`.goto`, `.return_`, `.unreachable`, `.switchInt`),
and rules out `.fault .unsupported`. -/
theorem evalStep_sim_core (exact : Bool) (p : Program) (s : State) (m : Machine)
    (hrel : StateRel exact p s m) (hstmtB : StmtIdxInBounds p s) :
    match evalStep p 0 s with
    | .step s' =>
      ∃ m', mrStep m = .step m' ∧ StateRel exact p s' m'
    | .done (.returned out) =>
      out.callerMem = ⟨[]⟩ ∧
      ∃ m1, mrStep m = .step m1 ∧ mrStep m1 = .returned (translateVal out.ret)
    | .done (.unwound _) | .done (.aborted _) => False
    | .fault .undefined =>
      exact = true → ∃ reason, mrStep m = .ub reason
    | .fault .unsupported => False := by
  cases hrel with
  | intro hpw h1 => cases h1 with | intro hpv h2 => cases h2 with
    | intro hcm h3 => cases h3 with | intro body h4 => cases h4 with
      | intro frame h5 => cases h5 with | intro calleeFrame h6 => cases h6 with
        | intro callerFrame h7 => cases h7 with | intro callerRetPtr h8 => cases h8 with
          | intro callerRetId h9 => cases h9 with | intro callerRetData h10 => cases h10 with
            | intro retMirTy h11 =>
              cases h11 with | intro hbody h12 => cases h12 with
                | intro hbadm h13 => cases h13 with | intro hretTy h14 => cases h14 with
                  | intro hsFrames h15 => cases h15 with | intro hdefId h16 => cases h16 with
                  | intro hsysop h16b => cases h16b with
                    | intro hlocLen h17 => cases h17 with | intro hblkLt h18 => cases h18 with
                      | intro hmProg h19 => cases h19 with | intro hmStack h20 => cases h20 with
                        | intro hfnEq h21 => cases h21 with | intro hnxtBlk h22 => cases h22 with
                          | intro hnxtStmt h23 => cases h23 with | intro hpopAct h24 => cases h24 with
                            | intro hcallerEq h25 => cases h25 with | intro hcallerLive h26 => cases h26 with
                              | intro hnd h27 => cases h27 with | intro hret0Live h28 => cases h28 with
                                | intro hbounds h29 => cases h29 with | intro hslots hdisj =>
  cases bodyAdmittedWith_spec exact body hbadm with
  | intro hbbNe hB1 => cases hB1 with | intro hargLt hB2 => cases hB2 with
    | intro hstab hB3 => cases hB3 with | intro hdiscV hB4 => cases hB4 with
      | intro hcastV hB5 => cases hB5 with | intro hsupp hblocksAdm =>
        cases listGet?_some_of_lt body.basicBlocks frame.blockIdx hblkLt with
        | intro bb hbb =>
          have hbb' : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx = some bb := by
            rw [getElem?_eq_listGet?]; exact hbb
          have hbbAdm :
              blockAdmitted exact body.argumentCount body.locals
                body.basicBlocks.length bb = true :=
            listGet?_all _ body.basicBlocks frame.blockIdx bb hblocksAdm hbb
          have hbbUnpack : bb.cleanup = false ∧
              bb.statements.all
                (stmtAdmitted exact body.argumentCount body.locals) = true ∧
              (match bb.terminator with
              | .goto target => Nat.blt target body.basicBlocks.length
              | .return_ => true
              | .unreachable => true
              | .switchInt discr targets =>
                operandAdmitted exact body.locals discr &&
                  Nat.blt targets.otherwise body.basicBlocks.length &&
                  match operandTy? body.locals discr with
                  | some dTy =>
                    (match dTy with
                    | .int _ _ | .bool => true
                    | .char => !exact
                    | _ => false) &&
                      switchBranchesAdmitted body.basicBlocks.length dTy targets.branches &&
                      switchCasesUnique (translateSwitchCasesForTy dTy targets.branches)
                  | none => false
              | _ => false) = true := by
            dsimp only [blockAdmitted] at hbbAdm
            cases hc : bb.cleanup with
            | true => rw [hc] at hbbAdm; cases hbbAdm
            | false =>
              rw [hc] at hbbAdm
              cases hs : bb.statements.all
                  (stmtAdmitted exact body.argumentCount body.locals) with
              | false => rw [hs] at hbbAdm; cases hbbAdm
              | true => rw [hs] at hbbAdm; exact ⟨rfl, rfl, hbbAdm⟩
          have hmrBlock : listGet? calleeFrame.func.blocks calleeFrame.nextBlock =
              some (translateBlock body.locals bb) := by
            rw [hfnEq, hnxtBlk]
            dsimp only [translateBody, listGet?]
            rw [listGet?_map, hbb]; rfl
          have hfnLoc : calleeFrame.func.locals = body.locals.map translateTy := by
            rw [hfnEq]; rfl
          have hfsRel : FrameSlotsRel exact body.locals frame.locals calleeFrame.locals m.mem :=
            ⟨hlocLen, hslots⟩
          -- Expose `evalStep` and `mrStep` at `(bb, frame.stmtIdx)`
          dsimp only [evalStep]
          rw [hsFrames]; dsimp only [activeFrameBody, attachCallers]
          rw [hsysop, hdefId, hbody]; dsimp only
          rw [hbb']; dsimp only
          cases hst : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | some stmt =>
            have hstList : listGet? bb.statements frame.stmtIdx = some stmt := by
              rw [← getElem?_eq_listGet?]; exact hst
            have hstmtAdm :
                stmtAdmitted exact body.argumentCount body.locals stmt = true :=
              listGet?_all _ bb.statements frame.stmtIdx stmt hbbUnpack.2.1 hstList
            have hmrStepEq : mrStep m = stepStatement m.prog calleeFrame [callerFrame] m.mem
                (translateStmt body.locals stmt) := by
              dsimp only [mrStep]
              rw [hmStack]; dsimp only
              rw [hmrBlock]; dsimp only
              rw [hnxtStmt]
              dsimp only [translateBlock]
              rw [listGet?_map, hstList]; rfl
            cases stmt with
            | unsupported => cases hstmtAdm
            | nop =>
              dsimp only [evalStatement]
              rw [hmrStepEq]
              cases hret0Live with
              | intro optRet hret0 =>
                have hsr0 := hslots 0 retMirTy (.immediate optRet) hretTy hret0
                cases hsr0 with
                | intro ptr0 h01 => cases h01 with | intro id0 h02 => cases h02 with
                  | intro data0 h03 =>
                    have hmrLoc0 : listGet? calleeFrame.func.locals 0 = some (translateTy retMirTy) := by
                      rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hretTy]; rfl
                    dsimp only [translateStmt, stepStatement, evalPlace]
                    rw [hmrLoc0, h03.1]
                    refine ⟨_, rfl, hpw, hpv, hcm, body, { frame with stmtIdx := frame.stmtIdx + 1 },
                      { calleeFrame with nextStmt := calleeFrame.nextStmt + 1 },
                      callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                      hbody, hbadm, hretTy, rfl, hdefId, hsysop, hlocLen, hblkLt, hmProg, rfl,
                      hfnEq, hnxtBlk, congrArg Nat.succ hnxtStmt, hpopAct, hcallerEq,
                      hcallerLive, hnd, ⟨optRet, hret0⟩, hbounds, hslots, hdisj⟩
            | storageLive localId =>
              dsimp only [stmtAdmitted] at hstmtAdm
              have hidLt : localId < body.locals.length := nat_lt_of_blt_eq_true hstmtAdm
              cases listGet?_some_of_lt body.locals localId hidLt with
              | intro localTy hlocTy =>
                have hlocTy' : Trusted.MirSemantics.getElem? body.locals localId = some localTy := by
                  rw [getElem?_eq_listGet?]; exact hlocTy
                cases listGet?_some_of_lt frame.locals localId (by rw [hlocLen]; exact hidLt) with
                | intro oldSlot hold =>
                  have hold' : Trusted.MirSemantics.getElem? frame.locals localId = some oldSlot := by
                    rw [getElem?_eq_listGet?]; exact hold
                  cases storageLiveFrame_sim exact body.locals frame.locals calleeFrame m.mem
                      retMirTy callerRetPtr callerRetId callerRetData localId localTy oldSlot
                      hfnLoc hsupp hlocTy' hold' hfsRel hnd hcallerLive hbounds hdisj with
                  | intro mrF' hSL1 => cases hSL1 with | intro mrM' hSL2 => cases hSL2 with
                    | intro locals' hSL3 =>
                      cases hSL3 with | intro hsetOk hSL4 => cases hSL4 with
                        | intro hslOk hSL5 => cases hSL5 with | intro hfn' hSL6 =>
                          cases hSL6 with | intro hblk' hSL7 => cases hSL7 with
                            | intro hstmt' hSL8 => cases hSL8 with | intro hpop' hSL9 =>
                              cases hSL9 with | intro hnd' hSL10 => cases hSL10 with
                                | intro hcaller' hSL11 => cases hSL11 with | intro hrel' hSL12 =>
                                  cases hSL12 with | intro hbounds' hdisj' =>
                                    dsimp only [evalStatement]
                                    rw [hlocTy']; dsimp only
                                    rw [hold']; dsimp only
                                    rw [hsetOk]; dsimp only
                                    have hdeallocA : deallocateLocal s.mem oldSlot = .ok s.mem := by
                                      have hsr := hslots localId localTy oldSlot hlocTy' hold'
                                      cases oldSlot with
                                      | dead => rfl | immediate _ => rfl | indirect _ | partialTuple _ => cases hsr
                                    rw [hdeallocA]; dsimp only
                                    rw [hmrStepEq]
                                    dsimp only [translateStmt, stepStatement]
                                    rw [hslOk]; dsimp only
                                    refine ⟨_, rfl, hpw, hpv, hcm, body,
                                      { frame with stmtIdx := frame.stmtIdx + 1, locals := locals' },
                                      { mrF' with nextStmt := mrF'.nextStmt + 1 },
                                      callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                                      hbody, hbadm, hretTy, rfl, hdefId, hsysop, hrel'.1, hblkLt, hmProg, rfl,
                                      Eq.trans hfn' hfnEq, Eq.trans hblk' hnxtBlk,
                                      congrArg Nat.succ (Eq.trans hstmt' hnxtStmt),
                                      Eq.trans hpop' hpopAct, hcallerEq, hcaller', hnd', ?_,
                                      hbounds', hrel'.2, hdisj'⟩
                                    -- _0 stays live
                                    · cases h0eq : Nat.beq localId 0 with
                                      | true =>
                                        have heq := Nat.eq_of_beq_eq_true h0eq; subst heq
                                        rw [getElem?_setElem?_eq _ _ _ _ hsetOk]
                                        cases liveUninitSlot_isImmediate localTy with
                                        | intro ov hov => exact ⟨ov, congrArg some hov⟩
                                      | false =>
                                        have hne : localId ≠ 0 := by intro h; subst h; cases h0eq
                                        rw [getElem?_setElem?_ne _ _ _ _ _ hsetOk hne]
                                        exact hret0Live
            | storageDead localId =>
              dsimp only [stmtAdmitted] at hstmtAdm
              cases hargB : Nat.blt body.argumentCount localId with
              | false => rw [hargB] at hstmtAdm; cases hstmtAdm
              | true =>
                rw [hargB, Bool.true_and] at hstmtAdm
                have hargLtId : body.argumentCount < localId := nat_lt_of_blt_eq_true hargB
                have h0LtId : 0 < localId := Nat.lt_of_le_of_lt (Nat.zero_le _) hargLtId
                have h0b : Nat.beq localId 0 = false := by
                  cases hb : Nat.beq localId 0 with
                  | false => rfl
                  | true => rw [Nat.eq_of_beq_eq_true hb] at h0LtId; cases h0LtId
                have hfnRet : calleeFrame.func.ret = 0 := by rw [hfnEq]; rfl
                have hfnArgs : calleeFrame.func.args = rangeNat 1 body.argumentCount := by
                  rw [hfnEq]; rfl
                have hargsAny : calleeFrame.func.args.any (Nat.beq localId) = false := by
                  rw [hfnArgs]
                  exact rangeNat_any_beq_false body.argumentCount 1 localId
                    (by rw [Nat.add_comm]; exact hargLtId)
                have hidLt : localId < body.locals.length := nat_lt_of_blt_eq_true hstmtAdm
                cases listGet?_some_of_lt body.locals localId hidLt with
                | intro localTy hlocTy =>
                  have hlocTy' : Trusted.MirSemantics.getElem? body.locals localId = some localTy := by
                    rw [getElem?_eq_listGet?]; exact hlocTy
                  cases listGet?_some_of_lt frame.locals localId (by rw [hlocLen]; exact hidLt) with
                  | intro oldSlot hold =>
                    have hold' : Trusted.MirSemantics.getElem? frame.locals localId = some oldSlot := by
                      rw [getElem?_eq_listGet?]; exact hold
                    cases storageDeadFrame_sim exact body.locals frame.locals calleeFrame m.mem
                        retMirTy callerRetPtr callerRetId callerRetData localId localTy oldSlot
                        hfnLoc hlocTy' hold' hfsRel hnd hcallerLive hbounds hdisj with
                    | intro mrF' hSD1 => cases hSD1 with | intro mrM' hSD2 => cases hSD2 with
                      | intro locals' hSD3 =>
                        cases hSD3 with | intro hsetOk hSD4 => cases hSD4 with
                          | intro hsdOk hSD5 => cases hSD5 with | intro hfn' hSD6 =>
                            cases hSD6 with | intro hblk' hSD7 => cases hSD7 with
                              | intro hstmt' hSD8 => cases hSD8 with | intro hpop' hSD9 =>
                                cases hSD9 with | intro _ hSD10 => cases hSD10 with
                                  | intro hnd' hSD11 => cases hSD11 with | intro hcaller' hSD12 =>
                                    cases hSD12 with | intro hrel' hSD13 => cases hSD13 with
                                      | intro hbounds' hdisj' =>
                                        dsimp only [evalStatement]
                                        rw [h0b, if_false_eq_true, hold']; dsimp only
                                        rw [hsetOk]; dsimp only
                                        have hdeallocA : deallocateLocal s.mem oldSlot = .ok s.mem := by
                                          have hsr := hslots localId localTy oldSlot hlocTy' hold'
                                          cases oldSlot with
                                          | dead => rfl | immediate _ => rfl | indirect _ | partialTuple _ => cases hsr
                                        rw [hdeallocA]; dsimp only
                                        rw [hmrStepEq]
                                        dsimp only [translateStmt, stepStatement]
                                        rw [hfnRet, h0b, hargsAny, Bool.false_or, if_false_eq_true, hsdOk]
                                        dsimp only
                                        have hne0 : localId ≠ 0 := by intro h; subst h; cases h0b
                                        refine ⟨_, rfl, hpw, hpv, hcm, body,
                                          { frame with stmtIdx := frame.stmtIdx + 1, locals := locals' },
                                          { mrF' with nextStmt := mrF'.nextStmt + 1 },
                                          callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                                          hbody, hbadm, hretTy, rfl, hdefId, hsysop, hrel'.1, hblkLt, hmProg, rfl,
                                          Eq.trans hfn' hfnEq, Eq.trans hblk' hnxtBlk,
                                          congrArg Nat.succ (Eq.trans hstmt' hnxtStmt),
                                          Eq.trans hpop' hpopAct, hcallerEq, hcaller', hnd', ?_,
                                          hbounds', hrel'.2, hdisj'⟩
                                        · rw [getElem?_setElem?_ne _ _ _ _ _ hsetOk hne0]; exact hret0Live
            | assign dst rv =>
              dsimp only [stmtAdmitted] at hstmtAdm
              cases hproj : dst.projection.isEmpty with
              | false => rw [hproj] at hstmtAdm; cases hstmtAdm
              | true =>
                rw [hproj] at hstmtAdm
                cases hdstTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rw [hdstTy] at hstmtAdm; cases hstmtAdm
                | some dstTy =>
                  rw [hdstTy] at hstmtAdm
                  have hdstLt : dst.localId < body.locals.length := by
                    rw [getElem?_eq_listGet?] at hdstTy
                    exact listGet?_lt_length body.locals dst.localId dstTy hdstTy
                  cases listGet?_some_of_lt frame.locals dst.localId (by rw [hlocLen]; exact hdstLt) with
                  | intro dstSlot hdstSlot =>
                    have hdstSlot' : Trusted.MirSemantics.getElem? frame.locals dst.localId = some dstSlot := by
                      rw [getElem?_eq_listGet?]; exact hdstSlot
                    have hmrDstLoc : listGet? calleeFrame.func.locals dst.localId = some (translateTy dstTy) := by
                      rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hdstTy]; rfl
                    have hrvSim := evalRvalue_sim exact body.locals frame.locals s.mem
                      calleeFrame m.mem dstTy rv hfnLoc hsupp hfsRel hstmtAdm
                    dsimp only [evalStatement]
                    rw [hproj, if_not_true, hdstTy]; dsimp only
                    cases hrv : evalRvalue body.locals frame.locals s.mem dstTy rv with
                    | error fk =>
                      rw [hrv] at hrvSim
                      cases fk with
                      | unsupported => exact hrvSim
                      | undefined =>
                        dsimp only at hrvSim; dsimp only
                        intro hexT
                        rw [hmrStepEq]
                        dsimp only [translateStmt, stepStatement, evalPlace]
                        rw [hmrDstLoc]; dsimp only
                        cases hmapDst : localMapGet? dst.localId calleeFrame.locals with
                        | none => exact ⟨_, rfl⟩
                        | some ptrDst =>
                          dsimp only
                          cases hrvSim hexT with
                          | intro msg hmsg => rw [hmsg]; exact ⟨msg, rfl⟩
                    | ok rvRes =>
                      rw [hrv] at hrvSim; dsimp only at hrvSim
                      cases rvRes with
                      | mk val rv1 => cases rv1 with | mk locals1 mem1 =>
                        dsimp only
                        cases hrvSim with
                        | intro hmem1 hrv2 => cases hrv2 with
                          | intro hcvVal hrv3 => cases hrv3 with
                            | intro hrel1 hrv4 => cases hrv4 with
                              | intro hexSame hrv5 => cases hrv5 with
                                | intro hpresImm hevalVal =>
                                  have hsrDst := hslots dst.localId dstTy dstSlot hdstTy hdstSlot'
                                  cases dstSlot with
                                  | indirect _ | partialTuple _ => cases hsrDst
                                  | dead =>
                                    dsimp only [SlotRel] at hsrDst
                                    have hdstDead1 : Trusted.MirSemantics.getElem? locals1 dst.localId = some .dead := by
                                      have hlt1 : dst.localId < locals1.length := by rw [hrel1.1]; exact hdstLt
                                      cases listGet?_some_of_lt locals1 dst.localId hlt1 with
                                      | intro sl1 hsl1 =>
                                        have hsl1' : Trusted.MirSemantics.getElem? locals1 dst.localId = some sl1 := by
                                          rw [getElem?_eq_listGet?]; exact hsl1
                                        have hsr1 := hrel1.2 dst.localId dstTy sl1 hdstTy hsl1'
                                        cases sl1 with
                                        | dead => exact hsl1'
                                        | indirect _ | partialTuple _ => cases hsr1
                                        | immediate _ =>
                                          cases hsr1 with
                                          | intro p hp => cases hp with | intro _ hp2 => cases hp2 with
                                            | intro _ hp3 => rw [hsrDst] at hp3; cases hp3.1
                                    dsimp only [writePlace]
                                    rw [hcvVal, if_not_true, hdstDead1]; dsimp only
                                    intro _
                                    rw [hmrStepEq]
                                    dsimp only [translateStmt, stepStatement, evalPlace]
                                    rw [hmrDstLoc, hsrDst]
                                    exact ⟨_, rfl⟩
                                  | immediate optOld =>
                                    cases hpresImm dst.localId optOld hdstSlot' with
                                    | intro optOld1 hdstSlot1 =>
                                      have hbounds1 : ∀ k ptrK, localMapGet? k calleeFrame.locals = some ptrK →
                                          k < body.locals.length ∧
                                          ∃ optV, Trusted.MirSemantics.getElem? locals1 k = some (.immediate optV) := by
                                        intro k ptrK hgK
                                        cases hbounds k ptrK hgK with
                                        | intro hltK hexK =>
                                          cases hexK with
                                          | intro ovK hovK =>
                                            exact ⟨hltK, hpresImm k ovK hovK⟩
                                      cases writePlace_live_sim exact body.locals locals1 mem1 calleeFrame m.mem
                                          retMirTy callerRetPtr callerRetId callerRetData
                                          dst.localId dstTy optOld1 val hsupp hdstTy hdstSlot1 hcvVal
                                          hrel1 hcallerLive hbounds1 hdisj with
                                      | intro locals2 hW1 => cases hW1 with | intro ptrDst hW2 =>
                                        cases hW2 with | intro mrMem2 hW3 =>
                                          cases hW3 with | intro hwrOk hW4 => cases hW4 with
                                            | intro hmapDst hW5 => cases hW5 with | intro hstOk hW6 =>
                                              cases hW6 with | intro hcaller2 hW7 => cases hW7 with
                                                | intro hrel2 hbounds2 =>
                                                  rw [hwrOk]; dsimp only
                                                  rw [hmrStepEq]
                                                  dsimp only [translateStmt, stepStatement, evalPlace]
                                                  rw [hmrDstLoc, hmapDst]
                                                  dsimp only
                                                  rw [hevalVal]
                                                  dsimp only
                                                  rw [if_not_true, hstOk]
                                                  have hret0_2 : ∃ optRet, Trusted.MirSemantics.getElem? locals2 0 = some (.immediate optRet) := by
                                                    cases hret0Live with
                                                    | intro optRet0 hret0 =>
                                                      have hsr0 := hslots 0 retMirTy (.immediate optRet0) hretTy hret0
                                                      cases hsr0 with
                                                      | intro ptr0 h01 => cases h01 with | intro _ h02 => cases h02 with
                                                        | intro _ h03 => exact (hbounds2 0 ptr0 h03.1).2
                                                  refine ⟨_, rfl, hpw, hpv, hcm, body,
                                                    { frame with stmtIdx := frame.stmtIdx + 1, locals := locals2 },
                                                    { calleeFrame with nextStmt := calleeFrame.nextStmt + 1 },
                                                    callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                                                    hbody, hbadm, hretTy, rfl, hdefId, hsysop, hrel2.1, hblkLt, hmProg, rfl,
                                                    hfnEq, hnxtBlk, congrArg Nat.succ hnxtStmt, hpopAct, hcallerEq,
                                                    hcaller2, hnd, hret0_2, hbounds2, hrel2.2, hdisj⟩
          | none =>
            -- Terminator case: check `frame.stmtIdx == bb.statements.length`
            have hstListNone : listGet? bb.statements frame.stmtIdx = none := by
              rw [← getElem?_eq_listGet?]; exact hst
            cases hstEqLen : Nat.beq frame.stmtIdx bb.statements.length with
            | false =>
              have hle : frame.stmtIdx ≤ bb.statements.length :=
                hstmtB body frame bb hsFrames (by rw [hdefId]; exact hbody) hbb'
              cases Nat.eq_or_lt_of_le hle with
              | inl heq => rw [heq, Nat.beq_refl] at hstEqLen; cases hstEqLen
              | inr hlt =>
                cases listGet?_some_of_lt bb.statements frame.stmtIdx hlt with
                | intro s' hs' => rw [hs'] at hstListNone; cases hstListNone
            | true =>
              rw [if_true_eq_true]
              have hmrTermEq : mrStep m = stepTerminator m.prog calleeFrame [callerFrame] m.mem
                  (translateTerm body.locals bb.terminator) := by
                dsimp only [mrStep]
                rw [hmStack]; dsimp only
                rw [hmrBlock]; dsimp only
                rw [hnxtStmt]
                dsimp only [translateBlock]
                rw [listGet?_map, hstListNone]
                dsimp only [Option.map]
                simp only [list_length_map, hstEqLen, ite_true]
              have htermAdm := hbbUnpack.2.2
              cases hterm : bb.terminator with
              | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | coreCall _ _ _ _ _
              | sysrootCall _ _ _ _ _ | unsupported | callNe _ _ _
              | drop _ _ _ =>
                rw [hterm] at htermAdm; cases htermAdm
              | goto target =>
                rw [hterm] at htermAdm hmrTermEq
                have htLt : target < body.basicBlocks.length := nat_lt_of_blt_eq_true htermAdm
                have hblkTgt : (!Nat.blt (target + 1) calleeFrame.func.blocks.length) = false := by
                  rw [hfnEq]; dsimp only [translateBody, List.length]
                  rw [list_length_map, nat_blt_eq_true_of_lt (Nat.succ_lt_succ htLt)]; rfl
                dsimp only [attachCallers, evalTerminator]
                rw [hterm]; dsimp only [jumpToBlock]
                rw [hmrTermEq]
                dsimp only [translateTerm, stepTerminator]
                rw [hblkTgt, if_false_eq_true]
                refine ⟨_, rfl, hpw, hpv, hcm, body,
                  { frame with blockIdx := target, stmtIdx := 0 },
                  { calleeFrame with nextBlock := target + 1, nextStmt := 0 },
                  callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                  hbody, hbadm, hretTy, rfl, hdefId, hsysop, hlocLen, htLt, hmProg, rfl,
                  hfnEq, rfl, rfl, hpopAct, hcallerEq, hcallerLive, hnd, hret0Live,
                  hbounds, hslots, hdisj⟩
              | unreachable =>
                rw [hterm] at hmrTermEq
                dsimp only [attachCallers, evalTerminator]; rw [hterm]
                intro _
                rw [hmrTermEq]
                exact ⟨_, rfl⟩
              | return_ =>
                rw [hterm] at hmrTermEq
                dsimp only [evalTerminator]; rw [hterm]
                rw [hbbUnpack.1, if_false_eq_true]
                cases hret0Live with
                | intro optRet hret0 =>
                  rw [hret0]
                  have hsr0 := hslots 0 retMirTy (.immediate optRet) hretTy hret0
                  have hmrLoc0 : listGet? calleeFrame.func.locals 0 = some (translateTy retMirTy) := by
                    rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hretTy]; rfl
                  have hretFun0 : calleeFrame.func.ret = 0 := by rw [hfnEq]; rfl
                  cases hsr0 with
                  | intro ptr0 h01 => cases h01 with | intro id0 h02 => cases h02 with
                    | intro data0 h03 => cases h03 with | intro hmap0 h04 => cases h04 with
                      | intro hlive0 hval0 =>
                        cases optRet with
                        | none =>
                          intro hexT
                          have hrep := hval0.2 hexT
                          have hretSupp : isSupportedScalarOrUnitTy retMirTy = true := by
                            rw [getElem?_eq_listGet?] at hretTy
                            exact listGet?_all isSupportedScalarOrUnitTy body.locals 0 retMirTy hsupp hretTy
                          rw [hmrTermEq]
                          dsimp only [translateTerm, stepTerminator]
                          rw [hretFun0, hmrLoc0, hmap0]; dsimp only
                          rw [allocLiveAt_typedLoad m.mem (translateTy retMirTy) ptr0 id0 data0
                            (translateTy retMirTy).align hlive0 (allocLiveAt_isAligned hlive0),
                            hrep, mrDecode_replicate_uninit_none retMirTy hretSupp hval0.1]
                          exact ⟨_, rfl⟩
                        | some retVal =>
                          have hretSupp : isSupportedScalarOrUnitTy retMirTy = true := by
                            rw [getElem?_eq_listGet?] at hretTy
                            exact listGet?_all isSupportedScalarOrUnitTy body.locals 0 retMirTy hsupp hretTy
                          have hload0 : typedLoad m.mem ptr0 (translateTy retMirTy) (translateTy retMirTy).align =
                              .ok (translateVal retVal) := by
                            rw [allocLiveAt_typedLoad m.mem (translateTy retMirTy) ptr0 id0 data0
                              (translateTy retMirTy).align hlive0 (allocLiveAt_isAligned hlive0),
                              hval0.2]
                          have hallLive : ∀ k ptrK, localMapGet? k calleeFrame.locals = some ptrK →
                              ∃ ty id data,
                                listGet? calleeFrame.func.locals k = some ty ∧
                                AllocLiveAt m.mem ty ptrK id data ∧
                                id ≠ callerRetId ∧
                                ∀ j ptr' id',
                                  k ≠ j → localMapGet? j calleeFrame.locals = some ptr' →
                                  ptr'.allocId = some id' → id ≠ id' := by
                            intro k ptrK hgK
                            cases hbounds k ptrK hgK with
                            | intro hltK hexK =>
                              cases listGet?_some_of_lt body.locals k hltK with
                              | intro tyK htyK =>
                                have htyK' : Trusted.MirSemantics.getElem? body.locals k = some tyK := by
                                  rw [getElem?_eq_listGet?]; exact htyK
                                cases hexK with
                                | intro ovK hovK =>
                                  have hsrK := hslots k tyK (.immediate ovK) htyK' hovK
                                  cases hsrK with
                                  | intro ptrK' hK1 => cases hK1 with | intro idK hK2 => cases hK2 with
                                    | intro dataK hK3 =>
                                      rw [hgK] at hK3; injection hK3.1 with hpe; subst hpe
                                      have hdisjK := hdisj k ptrK idK hgK hK3.2.1.1
                                      exact ⟨translateTy tyK, idK, dataK,
                                        by rw [hfnLoc, listGet?_map, htyK]; rfl,
                                        hK3.2.1, hdisjK.1, hdisjK.2⟩
                          cases deallocateAllLocals_spec calleeFrame.func (translateTy retMirTy)
                              callerRetPtr callerRetId callerRetData calleeFrame.locals m.mem
                              hnd hcallerLive hallLive with
                          | intro mem1 hdeallocAll =>
                            cases mrEncode_mrDecode_roundtrip retMirTy retVal hretSupp hval0.1 with
                            | intro retBytes hrt =>
                              cases allocLiveAt_store mem1 (translateTy retMirTy) callerRetPtr
                                  callerRetId callerRetData retBytes (translateTy retMirTy).align
                                  hdeallocAll.2 (allocLiveAt_isAligned hdeallocAll.2) hrt.2.1 with
                              | intro mem2 hstCaller =>
                                have htypedSt : typedStore mem1 callerRetPtr (translateVal retVal)
                                    (translateTy retMirTy) (translateTy retMirTy).align = .ok mem2 := by
                                  dsimp only [typedStore, liftMemRes]; rw [hrt.1]; dsimp only; rw [hstCaller.1]
                                refine ⟨callerMem_eq_empty s.callerMem hcm,
                                  { prog := m.prog, mem := mem2,
                                    stack := [{ callerFrame with nextBlock := 0, nextStmt := 0 }] },
                                  ?_, ?_⟩
                                · rw [hmrTermEq]
                                  dsimp only [translateTerm, stepTerminator]
                                  rw [hretFun0, hmrLoc0, hmap0]; dsimp only
                                  rw [hload0]; dsimp only
                                  rw [hdeallocAll.1]; dsimp only
                                  rw [hpopAct]; dsimp only
                                  rw [htypedSt]; dsimp only
                                  rw [hcallerEq]; rfl
                                · dsimp only [mrStep]
                                  rw [hcallerEq]
                                  dsimp only [harnessCallerFunc, listGet?, List.length, Nat.beq,
                                    stepTerminator, localMapGet?]
                                  simp only [ite_true]
                                  rw [allocLiveAt_typedLoad mem2 (translateTy retMirTy) callerRetPtr
                                    callerRetId retBytes (translateTy retMirTy).align
                                    hstCaller.2.1 (allocLiveAt_isAligned hstCaller.2.1), hrt.2.2]
              | switchInt discr targets =>
                rw [hterm] at htermAdm hmrTermEq
                dsimp only [attachCallers, evalTerminator]; rw [hterm]; dsimp only
                dsimp only at htermAdm
                cases hoa : operandAdmitted exact body.locals discr with
                | false => rw [hoa] at htermAdm; cases htermAdm
                | true =>
                  cases hoth : Nat.blt targets.otherwise body.basicBlocks.length with
                  | false => rw [hoa, hoth] at htermAdm; cases htermAdm
                  | true =>
                    rw [hoa, hoth] at htermAdm
                    cases hdt : operandTy? body.locals discr with
                    | none => rw [hdt] at htermAdm; cases htermAdm
                    | some dTy =>
                      rw [hdt] at htermAdm
                      have hdPrim : isPrimitiveReadableTy dTy = true := by
                        cases dTy <;> (first | rfl | cases htermAdm)
                      have hps := evalPrimitiveOperand_sim exact body.locals frame.locals s.mem
                        calleeFrame m.mem discr dTy hfnLoc hsupp hfsRel hoa hdt hdPrim
                      cases hpo : evalPrimitiveOperand body.locals frame.locals s.mem discr with
                      | error fk =>
                        rw [hpo] at hps
                        cases fk with
                        | unsupported => exact hps
                        | undefined =>
                          dsimp only at hps; dsimp only
                          intro hexT
                          cases hps hexT with
                          | intro msg hmsg =>
                            rw [hmrTermEq]
                            dsimp only [translateTerm]
                            rw [hdt]
                            cases dTy with
                            | int _ _ =>
                              dsimp only [stepTerminator]; rw [hmsg]; exact ⟨msg, rfl⟩
                            | bool =>
                              dsimp only [stepTerminator]
                              rw [evalValue_unOp, hmsg]; exact ⟨msg, rfl⟩
                            | char =>
                              dsimp only [stepTerminator]; rw [hmsg]; exact ⟨msg, rfl⟩
                            | _ => cases htermAdm
                      | ok poRes =>
                        rw [hpo] at hps; dsimp only at hps
                        cases poRes with
                        | mk discrVal po1 => cases po1 with | mk locals1 mem1 =>
                          dsimp only
                          cases hps with
                          | intro hmem1 hps2 => cases hps2 with
                            | intro hcvD hps3 => cases hps3 with
                              | intro hrel1 hps4 => cases hps4 with
                                | intro _ hps5 => cases hps5 with
                                  | intro hpresImm hevalD =>
                                    have hbounds1 : ∀ k ptrK, localMapGet? k calleeFrame.locals = some ptrK →
                                        k < body.locals.length ∧
                                        ∃ optV, Trusted.MirSemantics.getElem? locals1 k = some (.immediate optV) := by
                                      intro k ptrK hgK
                                      cases hbounds k ptrK hgK with
                                      | intro hltK hexK =>
                                        cases hexK with
                                        | intro ovK hovK => exact ⟨hltK, hpresImm k ovK hovK⟩
                                    have hret0_1 : ∃ optRet, Trusted.MirSemantics.getElem? locals1 0 = some (.immediate optRet) := by
                                      cases hret0Live with
                                      | intro optRet0 hret0 => exact hpresImm 0 optRet0 hret0
                                    have hothLt : targets.otherwise < body.basicBlocks.length :=
                                      nat_lt_of_blt_eq_true hoth
                                    have hswAdm : switchBranchesAdmitted body.basicBlocks.length dTy targets.branches = true := by
                                      rw [Bool.true_and, Bool.true_and] at htermAdm
                                      dsimp only at htermAdm
                                      cases hdOk : (match dTy with | .int _ _ | .bool => true | .char => !exact | _ => false) with
                                      | false => rw [hdOk] at htermAdm; cases htermAdm
                                      | true =>
                                        rw [hdOk, Bool.true_and] at htermAdm
                                        cases hsba : switchBranchesAdmitted body.basicBlocks.length dTy targets.branches with
                                        | false => rw [hsba] at htermAdm; cases htermAdm
                                        | true => rfl
                                    cases dTy with
                                    | int w sgn =>
                                      cases checkVal_int_elim hcvD with
                                      | intro bits hbits =>
                                        cases hbits with
                                        | intro hdEq hwf =>
                                          subst hdEq
                                          cases switchBranches_int_sim body.basicBlocks.length w sgn
                                              ⟨w, sgn, bits⟩ targets.otherwise rfl rfl hwf hothLt
                                              targets.branches hswAdm with
                                          | intro target hsw =>
                                            have hblkTgt : (!Nat.blt (target + 1) calleeFrame.func.blocks.length) = false := by
                                              rw [hfnEq]; dsimp only [translateBody, List.length]
                                              rw [list_length_map, nat_blt_eq_true_of_lt (Nat.succ_lt_succ hsw.2.1)]; rfl
                                            dsimp only
                                            rw [hsw.1]
                                            dsimp only [jumpToBlock]
                                            rw [hmrTermEq]
                                            dsimp only [translateTerm]
                                            rw [hdt]
                                            dsimp only [stepTerminator]
                                            rw [hevalD]
                                            dsimp only [translateVal]
                                            rw [hsw.2.2, hblkTgt, if_false_eq_true]
                                            refine ⟨_, rfl, hpw, hpv, hcm, body,
                                              { frame with blockIdx := target, stmtIdx := 0, locals := locals1 },
                                              { calleeFrame with nextBlock := target + 1, nextStmt := 0 },
                                              callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                                              hbody, hbadm, hretTy, rfl, hdefId, hsysop, hrel1.1, hsw.2.1, hmProg, rfl,
                                              hfnEq, rfl, rfl, hpopAct, hcallerEq, hcallerLive, hnd, hret0_1,
                                              hbounds1, hrel1.2, hdisj⟩
                                    | bool =>
                                      cases checkVal_bool_elim hcvD with
                                      | intro b hb =>
                                        subst hb
                                        cases switchBranches_bool_sim body.basicBlocks.length b
                                            targets.otherwise hothLt targets.branches hswAdm with
                                        | intro target hsw =>
                                          have hblkTgt : (!Nat.blt (target + 1) calleeFrame.func.blocks.length) = false := by
                                            rw [hfnEq]; dsimp only [translateBody, List.length]
                                            rw [list_length_map, nat_blt_eq_true_of_lt (Nat.succ_lt_succ hsw.2.1)]; rfl
                                          dsimp only
                                          rw [hsw.1]
                                          dsimp only [jumpToBlock]
                                          rw [hmrTermEq]
                                          dsimp only [translateTerm]
                                          rw [hdt]
                                          dsimp only [stepTerminator]
                                          rw [evalValue_unOp, hevalD]
                                          dsimp only [translateVal, translateTy]
                                          rw [evalUnOp_cast_transmute_ok _ _ _ _ (evalTransmute_bool_to_u8 b)]
                                          dsimp only
                                          rw [hsw.2.2, hblkTgt, if_false_eq_true]
                                          refine ⟨_, rfl, hpw, hpv, hcm, body,
                                            { frame with blockIdx := target, stmtIdx := 0, locals := locals1 },
                                            { calleeFrame with nextBlock := target + 1, nextStmt := 0 },
                                            callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                                            hbody, hbadm, hretTy, rfl, hdefId, hsysop, hrel1.1, hsw.2.1, hmProg, rfl,
                                            hfnEq, rfl, rfl, hpopAct, hcallerEq, hcallerLive, hnd, hret0_1,
                                            hbounds1, hrel1.2, hdisj⟩
                                    | char =>
                                      cases checkVal_char_elim hcvD with
                                      | intro c hc =>
                                        subst hc
                                        cases switchBranches_char_sim body.basicBlocks.length c
                                            targets.otherwise hothLt targets.branches hswAdm with
                                        | intro target hsw =>
                                          have hblkTgt : (!Nat.blt (target + 1) calleeFrame.func.blocks.length) = false := by
                                            rw [hfnEq]; dsimp only [translateBody, List.length]
                                            rw [list_length_map, nat_blt_eq_true_of_lt (Nat.succ_lt_succ hsw.2.1)]; rfl
                                          dsimp only
                                          rw [hsw.1]
                                          dsimp only [jumpToBlock]
                                          rw [hmrTermEq]
                                          dsimp only [translateTerm]
                                          rw [hdt]
                                          dsimp only [stepTerminator]
                                          rw [hevalD]
                                          dsimp only [translateVal]
                                          rw [hsw.2.2, hblkTgt, if_false_eq_true]
                                          refine ⟨_, rfl, hpw, hpv, hcm, body,
                                            { frame with blockIdx := target, stmtIdx := 0, locals := locals1 },
                                            { calleeFrame with nextBlock := target + 1, nextStmt := 0 },
                                            callerFrame, callerRetPtr, callerRetId, callerRetData, retMirTy,
                                            hbody, hbadm, hretTy, rfl, hdefId, hsysop, hrel1.1, hsw.2.1, hmProg, rfl,
                                            hfnEq, rfl, rfl, hpopAct, hcallerEq, hcallerLive, hnd, hret0_1,
                                            hbounds1, hrel1.2, hdisj⟩
                                    | _ => cases htermAdm

/-! ## Multi-Step Reachability, Behavior, Fault, and Divergence Theorems -/

/-- Constructive deterministic next-step iterator for MiniRust (`0`
`Classical.choice`). -/
def mrNext (m : Machine) : Machine :=
  match mrStep m with
  | .step m' => m'
  | _ => m

/-- `n`-step deterministic MiniRust state iterator. -/
def mrIter : Nat → Machine → Machine
  | 0, m => m
  | n + 1, m => mrIter n (mrNext m)

theorem mrIter_succ_right (n : Nat) (m : Machine) :
    mrIter (n + 1) m = mrNext (mrIter n m) := by
  induction n generalizing m with
  | zero => rfl
  | succ k ih => exact ih (mrNext m)

/-- Constructive deterministic next-step iterator for Anneal (`c = 0`). -/
noncomputable def annealNext (p : Program) (s : State) : State :=
  match evalStep p 0 s with
  | .step s' => s'
  | _ => s

/-- `n`-step deterministic Anneal state iterator. -/
noncomputable def annealIter (p : Program) : Nat → State → State
  | 0, s => s
  | n + 1, s => annealIter p n (annealNext p s)

theorem annealIter_succ_right (p : Program) (n : Nat) (s : State) :
    annealIter p (n + 1) s = annealNext p (annealIter p n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => exact ih (annealNext p s)

/-- Extract the deterministic step count `k` from `MrReachesHead m₀ m₁`. -/
theorem mrReachesHead_to_iter {m₀ m₁ : Machine} (h : MrReachesHead m₀ m₁) :
    ∃ k : Nat,
      mrIter k m₀ = m₁ ∧
      ∀ i : Nat, i < k → mrStep (mrIter i m₀) = .step (mrIter (i + 1) m₀) := by
  induction h with
  | refl m =>
    exact ⟨0, rfl, fun _ hlt => by cases hlt⟩
  | @head m₁ m₂ _ hstep _ ih =>
    cases ih with
    | intro k hk =>
      have hnext : mrNext m₁ = m₂ := by dsimp only [mrNext]; rw [hstep]
      refine ⟨k + 1, ?_, fun i hlt => ?_⟩
      · dsimp only [mrIter]; rw [hnext]; exact hk.1
      · cases i with
        | zero =>
          dsimp only [mrIter]; rw [hnext]; exact hstep
        | succ i' =>
          dsimp only [mrIter]; rw [hnext]
          exact hk.2 i' (Nat.lt_of_succ_lt_succ hlt)

/-- Stepping from `MrReaches` along a `MrDiverges` trace stays on the trace. -/
theorem mrDiverges_follow_reaches {m₀ m₁ : Machine} {trace : Nat → Machine}
    (ht0 : trace 0 = m₀)
    (htStep : ∀ n, mrStep (trace n) = .step (trace (n + 1)))
    (hreach : MrReachesHead m₀ m₁) :
    ∃ k : Nat, trace k = m₁ := by
  have haux : ∀ (a b : Machine), MrReachesHead a b →
      ∀ (j : Nat), trace j = a → ∃ k, trace k = b := by
    intro a b hr
    induction hr with
    | refl _ => intro j hj; exact ⟨j, hj⟩
    | head hstep _ ih =>
      intro j hj
      have hs := htStep j
      rw [hj, hstep] at hs
      injection hs with heq
      exact ih (j + 1) heq.symm
  exact haux m₀ m₁ hreach 0 ht0

/-- Lift `evalStep_sim_core` to preserve `FullStateRel`. -/
theorem fullStep_sim (exact : Bool) (p : Program) (s : State) (m : Machine)
    (hrel : FullStateRel exact p s m) :
    match evalStep p 0 s with
    | .step s' =>
      ∃ m', mrStep m = .step m' ∧ FullStateRel exact p s' m'
    | .done (.returned out) =>
      out.callerMem = ⟨[]⟩ ∧
      ∃ m1, mrStep m = .step m1 ∧ mrStep m1 = .returned (translateVal out.ret)
    | .done (.unwound _) | .done (.aborted _) => False
    | .fault .undefined =>
      exact = true → ∃ reason, mrStep m = .ub reason
    | .fault .unsupported => False := by
  have hcore := evalStep_sim_core exact p s m hrel.1 hrel.2
  cases hev : evalStep p 0 s with
  | step s' =>
    rw [hev] at hcore
    cases hcore with
    | intro m' hm' =>
      refine ⟨m', hm'.1, hm'.2, ?_⟩
      intro body frame bb hsF hbody hbb
      -- Derive `frame.stmtIdx ≤ bb.statements.length` from `hm'.2` and `hev`
      cases hrel.1 with
      | intro _ h1 => cases h1 with | intro _ h2 => cases h2 with
        | intro _ h3 => cases h3 with | intro body0 h4 => cases h4 with
          | intro frame0 h5 => cases h5 with | intro _ h6 => cases h6 with
            | intro _ h7 => cases h7 with | intro _ h8 => cases h8 with
              | intro _ h9 => cases h9 with | intro _ h10 => cases h10 with
                | intro _ h11 =>
                  have hbody0 := h11.1
                  have hbadm0 := h11.2.1
                  have hsF0 := h11.2.2.2.1
                  have hdef0 := h11.2.2.2.2.1
                  have hsys0 := h11.2.2.2.2.2.1
                  dsimp only [evalStep] at hev
                  rw [hsF0] at hev; dsimp only [activeFrameBody, attachCallers] at hev
                  rw [hsys0, hdef0, hbody0] at hev; dsimp only at hev
                  cases hbb0 : Trusted.MirSemantics.getElem? body0.basicBlocks frame0.blockIdx with
                  | none => rw [hbb0] at hev; cases hev
                  | some bb0 =>
                    rw [hbb0] at hev; dsimp only at hev
                    cases hst0 : Trusted.MirSemantics.getElem? bb0.statements frame0.stmtIdx with
                    | some stmt0 =>
                      rw [hst0] at hev
                      have hlt0 : frame0.stmtIdx < bb0.statements.length := by
                        rw [getElem?_eq_listGet?] at hst0
                        exact listGet?_lt_length bb0.statements frame0.stmtIdx stmt0 hst0
                      have hframeEq : frame.defId = frame0.defId ∧ frame.blockIdx = frame0.blockIdx ∧
                          frame.stmtIdx = frame0.stmtIdx + 1 := by
                        cases stmt0 with
                        | nop =>
                          dsimp only [evalStatement] at hev; injection hev with hse; subst hse
                          dsimp only at hsF; injection hsF with hfe; subst hfe; exact ⟨rfl, rfl, rfl⟩
                        | storageLive id =>
                          dsimp only [evalStatement] at hev
                          cases hg1 : Trusted.MirSemantics.getElem? body0.locals id with
                          | none => rw [hg1] at hev; cases hev
                          | some localTy =>
                            rw [hg1] at hev; dsimp only at hev
                            cases hg2 : Trusted.MirSemantics.getElem? frame0.locals id with
                            | none => rw [hg2] at hev; cases hev
                            | some old =>
                              rw [hg2] at hev; dsimp only at hev
                              cases hset : setElem? frame0.locals id (liveUninitSlot localTy) with
                              | none => rw [hset] at hev; cases hev
                              | some _ =>
                                rw [hset] at hev; dsimp only at hev
                                cases hd : deallocateLocal s.mem old with
                                | error _ => rw [hd] at hev; cases hev
                                | ok _ =>
                                  rw [hd] at hev; injection hev with hse; subst hse
                                  dsimp only at hsF; injection hsF with hfe; subst hfe; exact ⟨rfl, rfl, rfl⟩
                        | storageDead id =>
                          dsimp only [evalStatement] at hev
                          cases hb0 : Nat.beq id 0 with
                          | true => rw [hb0, if_true_eq_true] at hev; cases hev
                          | false =>
                            rw [hb0, if_false_eq_true] at hev
                            cases hg2 : Trusted.MirSemantics.getElem? frame0.locals id with
                            | none => rw [hg2] at hev; cases hev
                            | some old =>
                              rw [hg2] at hev; dsimp only at hev
                              cases hset : setElem? frame0.locals id .dead with
                              | none => rw [hset] at hev; cases hev
                              | some _ =>
                                rw [hset] at hev; dsimp only at hev
                                cases hd : deallocateLocal s.mem old with
                                | error _ => rw [hd] at hev; cases hev
                                | ok _ =>
                                  rw [hd] at hev; injection hev with hse; subst hse
                                  dsimp only at hsF; injection hsF with hfe; subst hfe; exact ⟨rfl, rfl, rfl⟩
                        | assign dst rv =>
                          dsimp only [evalStatement] at hev
                          cases hp : dst.projection.isEmpty with
                          | false => rw [hp, if_not_false] at hev; cases hev
                          | true =>
                            rw [hp, if_not_true] at hev
                            cases hg1 : Trusted.MirSemantics.getElem? body0.locals dst.localId with
                            | none => rw [hg1] at hev; cases hev
                            | some dstTy =>
                              rw [hg1] at hev; dsimp only at hev
                              cases hrv : evalRvalue body0.locals frame0.locals s.mem dstTy rv with
                              | error _ => rw [hrv] at hev; cases hev
                              | ok rvRes =>
                                rw [hrv] at hev; dsimp only at hev
                                cases rvRes with
                                | mk v rv1 => cases rv1 with | mk l1 m1 =>
                                  cases hwp : writePlace l1 m1 dst.localId dstTy v with
                                  | error _ => rw [hwp] at hev; cases hev
                                  | ok wpRes =>
                                    rw [hwp] at hev
                                    cases wpRes with
                                    | mk _ _ =>
                                      injection hev with hse; subst hse
                                      dsimp only at hsF; injection hsF with hfe; subst hfe; exact ⟨rfl, rfl, rfl⟩
                        | unsupported => cases hev
                      rw [hframeEq.1, hdef0, hbody0] at hbody; injection hbody with hbe; subst hbe
                      rw [hframeEq.2.1, hbb0] at hbb; injection hbb with hbbe; subst hbbe
                      rw [hframeEq.2.2]; exact hlt0
                    | none =>
                      rw [hst0] at hev; dsimp only at hev
                      cases hlenB : Nat.beq frame0.stmtIdx bb0.statements.length with
                      | false => rw [hlenB, if_false_eq_true] at hev; cases hev
                      | true =>
                        rw [hlenB, if_true_eq_true] at hev
                        cases ht : bb0.terminator with
                        | goto _ =>
                          rw [ht] at hev; dsimp only [attachCallers, evalTerminator] at hev
                          rw [ht] at hev; dsimp only [jumpToBlock] at hev
                          injection hev with hse; subst hse
                          dsimp only at hsF; injection hsF with hfe; subst hfe
                          exact Nat.zero_le _
                        | switchInt discr targets =>
                          rw [ht] at hev; dsimp only [attachCallers, evalTerminator] at hev
                          rw [ht] at hev; dsimp only at hev
                          cases hpo : evalPrimitiveOperand body0.locals frame0.locals s.mem discr with
                          | error _ => rw [hpo] at hev; cases hev
                          | ok poRes =>
                            rw [hpo] at hev; dsimp only at hev
                            cases poRes with
                            | mk dVal po1 => cases po1 with | mk l1 m1 =>
                              dsimp only at hev
                              cases dVal with
                              | scalar sv =>
                                dsimp only at hev
                                cases htr : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                                | error _ => rw [htr] at hev; cases hev
                                | ok tgt =>
                                  rw [htr] at hev; dsimp only [jumpToBlock] at hev
                                  injection hev with hse; subst hse
                                  dsimp only at hsF; injection hsF with hfe; subst hfe
                                  exact Nat.zero_le _
                              | bool b =>
                                dsimp only at hev
                                cases htr : evalBoolSwitchBranches b targets.otherwise targets.branches with
                                | error _ => rw [htr] at hev; cases hev
                                | ok tgt =>
                                  rw [htr] at hev; dsimp only [jumpToBlock] at hev
                                  injection hev with hse; subst hse
                                  dsimp only at hsF; injection hsF with hfe; subst hfe
                                  exact Nat.zero_le _
                              | char c =>
                                dsimp only at hev
                                cases htr : evalCharSwitchBranches c targets.otherwise targets.branches with
                                | error _ => rw [htr] at hev; cases hev
                                | ok tgt =>
                                  rw [htr] at hev; dsimp only [jumpToBlock] at hev
                                  injection hev with hse; subst hse
                                  dsimp only at hsF; injection hsF with hfe; subst hfe
                                  exact Nat.zero_le _
                              | _ =>
                                dsimp only at hev
                                cases hbr : targets.branches with
                                | cons _ _ => rw [hbr] at hev; cases hev
                                | nil =>
                                  rw [hbr] at hev; dsimp only [jumpToBlock] at hev
                                  injection hev with hse; subst hse
                                  dsimp only at hsF; injection hsF with hfe; subst hfe
                                  exact Nat.zero_le _
                        | return_ =>
                          rw [ht] at hev; dsimp only [evalTerminator] at hev
                          rw [ht] at hev; dsimp only at hev
                          cases hcl : bb0.cleanup with
                          | true => rw [hcl, if_true_eq_true] at hev; cases hev
                          | false =>
                            rw [hcl, if_false_eq_true] at hev
                            cases h0 : Trusted.MirSemantics.getElem? frame0.locals 0 with
                            | none => rw [h0] at hev; cases hev
                            | some sl0 =>
                              rw [h0] at hev
                              cases sl0 with
                              | dead => cases hev
                              | immediate ov => cases ov <;> cases hev
                              | partialTuple _ => cases hev
                              | indirect mp =>
                                cases hty0 : Trusted.MirSemantics.getElem? body0.locals 0 with
                                | none => rw [hty0] at hev; cases hev
                                | some rty =>
                                  rw [hty0] at hev; dsimp only at hev
                                  cases hld : loadIndirect s.mem rty mp with
                                  | error _ => rw [hld] at hev; cases hev
                                  | ok ov => cases ov <;> rw [hld] at hev <;> cases hev
                        | unreachable =>
                          rw [ht] at hev; dsimp only [attachCallers, evalTerminator] at hev
                          rw [ht] at hev; cases hev
                        | unwindResume | coreCall _ _ _ _ _ | unsupported
                        | callNe _ _ _ _ _ | drop _ _ _ =>
                          rw [ht] at hev; dsimp only [attachCallers, evalTerminator] at hev
                          rw [ht] at hev; cases hev
                        | assert _ _ _ _ _ | call _ _ _ _ _ | sysrootCall _ _ _ _ _ =>
                          have hbb0' : listGet? body0.basicBlocks frame0.blockIdx = some bb0 := by
                            rw [← getElem?_eq_listGet?]; exact hbb0
                          have hnc := block_terminator_not_call_or_assert exact body0.argumentCount
                            body0.locals body0.basicBlocks.length bb0
                            (listGet?_all _ body0.basicBlocks frame0.blockIdx bb0
                              (bodyAdmittedWith_spec exact body0 hbadm0).2.2.2.2.2.2 hbb0')
                          rw [ht] at hnc; cases hnc
  | done out =>
    rw [hev] at hcore
    cases out with
    | returned _ | unwound _ | aborted _ => exact hcore
  | fault k =>
    rw [hev] at hcore
    cases k with | undefined => exact hcore | unsupported => exact hcore

/-- `init_stateRel` lifted to `FullStateRel`. -/
theorem init_fullStateRel (exact : Bool) (p : Program) (q : Query)
    (hadm : if exact then MiniRustExactAdmitted p q else MiniRustAdmitted p q) :
    ∃ s₀ m₀ m₁,
      initState p q = .ok s₀ ∧
      initMrMachine p q = .ok m₀ ∧
      MrReaches m₀ m₁ ∧
      FullStateRel exact p s₀ m₁ := by
  cases init_stateRel exact p q hadm with
  | intro s₀ h1 => cases h1 with | intro m₀ h2 => cases h2 with
    | intro m₁ h3 =>
      refine ⟨s₀, m₀, m₁, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2, ?_⟩
      intro body frame bb hsF _ _
      -- From `h3.2.2.2` and `h3.1`, `frame.stmtIdx = 0`
      cases h3.2.2.2 with
      | intro _ hA => cases hA with | intro _ hB => cases hB with
        | intro _ hC => cases hC with | intro b0 hD => cases hD with
          | intro f0 hE => cases hE with | intro cf hF => cases hF with
            | intro _ hG => cases hG with | intro _ hH => cases hH with
              | intro _ hI => cases hI with | intro _ hJ => cases hJ with
                | intro _ hK =>
                  have hsF0 := hK.2.2.2.1
                  rw [hsF0] at hsF; injection hsF with hfe; subst hfe
                  -- From `initState p q = .ok s₀`, `f0.stmtIdx = 0`
                  have hst0 : f0.stmtIdx = 0 := by
                    have hi := h3.1
                    dsimp only [initState] at hi
                    cases h1' : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) with
                    | true => rw [h1', if_true_eq_true] at hi; cases hi
                    | false =>
                      rw [h1', if_false_eq_true] at hi
                      cases h2' : !q.callerMem.allocations.isEmpty with
                      | true => rw [h2', if_true_eq_true] at hi; cases hi
                      | false =>
                        rw [h2', if_false_eq_true] at hi
                        cases h3' : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
                        | none => rw [h3'] at hi; cases hi
                        | some bd =>
                          rw [h3'] at hi; dsimp only at hi
                          cases h4' : bd.basicBlocks.isEmpty with
                          | true => rw [h4', if_true_eq_true] at hi; cases hi
                          | false =>
                            rw [h4', if_false_eq_true] at hi
                            cases h5' : !Nat.blt bd.argumentCount bd.locals.length with
                            | true => rw [h5', if_true_eq_true] at hi; cases hi
                            | false =>
                              rw [h5', if_false_eq_true] at hi
                              cases h6' : !storageAnnotationsInBounds bd with
                              | true => rw [h6', if_true_eq_true] at hi; cases hi
                              | false =>
                                rw [h6', if_false_eq_true] at hi
                                cases h7' : !discriminantTypesValid bd with
                                | true => rw [h7', if_true_eq_true] at hi; cases hi
                                | false =>
                                  rw [h7', if_false_eq_true] at hi
                                  cases h8' : !castTypesValid bd with
                                  | true => rw [h8', if_true_eq_true] at hi; cases hi
                                  | false =>
                                    rw [h8', if_false_eq_true] at hi
                                    cases h8a : !assertConditionTypesValid bd with
                                    | true => rw [h8a, if_true_eq_true] at hi; cases hi
                                    | false =>
                                      rw [h8a, if_false_eq_true] at hi
                                      cases h9' : !bd.locals.all isSupportedScalarOrUnitTy with
                                      | true => rw [h9', if_true_eq_true] at hi; cases hi
                                      | false =>
                                        rw [h9', if_false_eq_true] at hi
                                        cases hc1 : !callsAdmitted p bd with
                                        | true => rw [hc1, if_true_eq_true] at hi; cases hi
                                        | false =>
                                          rw [hc1, if_false_eq_true] at hi
                                          cases hc2 : !allCallBodiesStaticAdmitted p bd with
                                          | true => rw [hc2, if_true_eq_true] at hi; cases hi
                                          | false =>
                                            rw [hc2, if_false_eq_true] at hi
                                            cases h10' : !checkArgsMatch q.args ((bd.locals.drop 1).take bd.argumentCount) with
                                            | true => rw [h10', if_true_eq_true] at hi; cases hi
                                            | false =>
                                              rw [h10', if_false_eq_true] at hi
                                              injection hi with hse; rw [← hse] at hsF0
                                              dsimp only at hsF0; injection hsF0 with hfe2; rw [← hfe2]
                  rw [hst0]; exact Nat.zero_le _

/-- Multi-step forward simulation of `Reaches`: every Anneal intermediate state
is matched by a reachable MiniRust state preserving `FullStateRel`. -/
theorem reaches_sim_forward (exact : Bool) (p : Program) {s₀ s : State} {m₀ : Machine}
    (hrel₀ : FullStateRel exact p s₀ m₀) (hreach : Reaches p s₀ s) :
    ∃ m, MrReaches m₀ m ∧ FullStateRel exact p s m := by
  induction hreach with
  | refl => exact ⟨m₀, MrReaches.refl m₀, hrel₀⟩
  | tail _ hstep ih =>
    cases ih with
    | intro m hm =>
      cases hstep with
      | intro c hc =>
        have hc0 : c = 0 := hc.1
        subst hc0
        have hsim := fullStep_sim exact p _ m hm.2
        rw [hc.2] at hsim
        cases hsim with
        | intro m' hm' =>
          exact ⟨m', MrReaches.tail hm.1 hm'.1, hm'.2⟩

/-- Reverse simulation from a MiniRust terminal or UB trace (`MrReachesHead`)
back to Anneal: covers `exact = false` (UB) and `exact = true` (UB & return). -/
theorem mrReachesHead_sim_back (exact : Bool) (p : Program) :
    ∀ {m mEnd : Machine} {s : State},
      FullStateRel exact p s m →
      MrReachesHead m mEnd →
      (∀ reason, mrStep mEnd = .ub reason →
        ∃ sf, Reaches p s sf ∧ Step p sf (.fault .undefined)) ∧
      (∀ v', exact = true → mrStep mEnd = .returned v' →
        ∃ sf v, Reaches p s sf ∧ Step p sf (.done (.returned ⟨v, ⟨[]⟩⟩)) ∧
          v' = translateVal v) := by
  intro m mEnd s hrel hreach
  induction hreach generalizing s with
  | refl m =>
    have hsim := fullStep_sim exact p s m hrel
    cases hev : evalStep p 0 s with
    | step s' =>
      rw [hev] at hsim
      cases hsim with
      | intro m' hm' =>
        refine ⟨fun reason hub => ?_, fun v' _ hret => ?_⟩
        · rw [hm'.1] at hub; cases hub
        · rw [hm'.1] at hret; cases hret
    | done out =>
      rw [hev] at hsim
      cases out with
      | unwound _ | aborted _ => exact False.elim hsim
      | returned r =>
        cases hsim with
        | intro _ hex =>
          cases hex with
          | intro m1 hm1 =>
            refine ⟨fun reason hub => ?_, fun v' _ hret => ?_⟩
            · rw [hm1.1] at hub; cases hub
            · rw [hm1.1] at hret; cases hret
    | fault fk =>
      rw [hev] at hsim
      cases fk with
      | unsupported => exact False.elim hsim
      | undefined =>
        refine ⟨fun _ _ => ⟨s, Reaches.refl s, ⟨0, rfl, hev⟩⟩, fun v' hexT hret => ?_⟩
        cases hsim hexT with
        | intro reason hub => rw [hub] at hret; cases hret
  | @head m₁ _ _ hstep hrest ih =>
    have hsim := fullStep_sim exact p s m₁ hrel
    cases hev : evalStep p 0 s with
    | step s' =>
      rw [hev] at hsim
      cases hsim with
      | intro m' hm' =>
        rw [hm'.1] at hstep; injection hstep with hmeq; subst hmeq
        have hstepA : Step p s (.step s') := ⟨0, rfl, hev⟩
        cases ih hm'.2 with
        | intro ihUB ihRet =>
          refine ⟨fun reason hub => ?_, fun v' hexT hret => ?_⟩
          · cases ihUB reason hub with
            | intro sf hsf =>
              -- Prepend `Step p s (.step s')` to `Reaches p s' sf`
              have hpre : ∀ a b, Reaches p a b → Step p s (.step a) → Reaches p s b := by
                intro a b hr hsA
                induction hr with
                | refl => exact Reaches.tail (Reaches.refl s) hsA
                | tail _ hst iha => exact Reaches.tail iha hst
              exact ⟨sf, hpre s' sf hsf.1 hstepA, hsf.2⟩
          · cases ihRet v' hexT hret with
            | intro sf hsf => cases hsf with | intro v hv =>
              have hpre : ∀ a b, Reaches p a b → Step p s (.step a) → Reaches p s b := by
                intro a b hr hsA
                induction hr with
                | refl => exact Reaches.tail (Reaches.refl s) hsA
                | tail _ hst iha => exact Reaches.tail iha hst
              exact ⟨sf, v, hpre s' sf hv.1 hstepA, hv.2⟩
    | done out =>
      rw [hev] at hsim
      cases out with
      | unwound _ | aborted _ => exact False.elim hsim
      | returned r =>
        cases r with
        | mk val cm =>
          cases hsim with
          | intro hcmEq hex =>
            dsimp only at hcmEq; subst hcmEq
            cases hex with
            | intro mNext hmNext =>
              rw [hmNext.1] at hstep; injection hstep with hmeq; subst hmeq
              refine ⟨fun reason hub => ?_, fun v' _ hret => ?_⟩
              · have heq := mrStep_deterministic_head (MrReachesHead.refl mNext) hmNext.2
                  (fun _ h => by cases h) hrest hub (fun _ h => by cases h)
                cases heq
              · have heq := mrStep_deterministic_head (MrReachesHead.refl mNext) hmNext.2
                  (fun _ h => by cases h) hrest hret (fun _ h => by cases h)
                injection heq with hveq
                exact ⟨s, val, Reaches.refl s, ⟨0, rfl, hev⟩, hveq.symm⟩
    | fault fk =>
      rw [hev] at hsim
      cases fk with
      | unsupported => exact False.elim hsim
      | undefined =>
        refine ⟨fun _ _ => ⟨s, Reaches.refl s, ⟨0, rfl, hev⟩⟩, fun v' hexT hret => ?_⟩
        cases hsim hexT with
        | intro reason hub => rw [hub] at hstep; cases hstep

/-- Helper: `Reaches` is closed under single-step prefix. -/
theorem reaches_head {p : Program} {s₁ s₂ s₃ : State}
    (hs : Step p s₁ (.step s₂)) (hr : Reaches p s₂ s₃) : Reaches p s₁ s₃ := by
  induction hr with
  | refl => exact Reaches.tail (Reaches.refl s₁) hs
  | tail _ hst ih => exact Reaches.tail ih hst

/-- Helper: `MrReachesHead` from `m₀` to `mEnd` with non-step outcome, when
`m₀` reaches `m₁` via `initBlock`, must pass through `m₁`. -/
theorem mrReaches_after_init {m₀ m₁ mEnd : Machine} {o : StepOutcome}
    (hinit : MrReachesHead m₀ m₁) (hreach : MrReachesHead m₀ mEnd)
    (hstepEnd : mrStep mEnd = o) (hns : ∀ m', o ≠ .step m') :
    MrReachesHead m₁ mEnd := by
  induction hinit with
  | refl => exact hreach
  | head hstep _ ih =>
    cases hreach with
    | refl =>
      rw [hstep] at hstepEnd
      exact False.elim (hns _ hstepEnd.symm)
    | head hstep2 hrest =>
      rw [hstep] at hstep2; injection hstep2 with heq; subst heq
      exact ih hrest

/-! ## Top-Level Forward Simulation Theorems -/

/-- No admitted `(p, q)` ever reaches `FaultKind.unsupported`
(`MiniRustAdmitted`). -/
theorem forward_no_unsupported (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ¬ ReachesResult p q (.fault .unsupported) := by
  intro hrr
  cases init_fullStateRel false p q hadm with
  | intro s₀ h1 => cases h1 with | intro m₀ h2 => cases h2 with
    | intro m₁ h3 =>
      dsimp only [ReachesResult] at hrr
      rw [h3.1] at hrr
      cases hrr with
      | intro sf hsf =>
        cases reaches_sim_forward false p h3.2.2.2 hsf.1 with
        | intro mf hmf =>
          cases hsf.2 with
          | intro c hc =>
            have hc0 : c = 0 := hc.1; subst hc0
            have hsim := fullStep_sim false p sf mf hmf.2
            rw [hc.2] at hsim
            exact hsim

/-- Forward simulation of normal return behavior (`MiniRustAdmitted`). -/
theorem forward_behavior (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      ∀ v, Behavior p q (.returned ⟨v, ⟨[]⟩⟩) →
        MrBehavior m₀ (translateVal v) := by
  intro m₀ hinitM v hbeh
  cases init_fullStateRel false p q hadm with
  | intro s₀ h1 => cases h1 with | intro m₀' h2 => cases h2 with
    | intro m₁ h3 =>
      rw [h3.2.1] at hinitM; injection hinitM with hmeq
      have hmeq' := hmeq.symm; subst hmeq'
      dsimp only [Behavior, ReachesResult] at hbeh
      rw [h3.1] at hbeh
      cases hbeh with
      | intro sf hsf =>
        cases reaches_sim_forward false p h3.2.2.2 hsf.1 with
        | intro mf hmf =>
          cases hsf.2 with
          | intro c hc =>
            have hc0 : c = 0 := hc.1; subst hc0
            have hsim := fullStep_sim false p sf mf hmf.2
            rw [hc.2] at hsim
            cases hsim.2 with
            | intro mRet hmRet =>
              exact ⟨mRet, MrReaches.tail (MrReaches.trans h3.2.2.1 hmf.1) hmRet.1,
                hmRet.2⟩

/-- Contrapositive UB soundness (`MiniRustAdmitted`): if MiniRust reaches UB
from `m₀`, then Anneal reaches `.fault .undefined` from `(p, q)`. -/
theorem forward_ub_contrapositive (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      MrFaultsUB m₀ → ReachesResult p q (.fault .undefined) := by
  intro m₀ hinitM hub
  cases init_fullStateRel false p q hadm with
  | intro s₀ h1 => cases h1 with | intro m₀' h2 => cases h2 with
    | intro m₁ h3 =>
      rw [h3.2.1] at hinitM; injection hinitM with hmeq
      have hmeq' := hmeq.symm; subst hmeq'
      cases hub with
      | intro mEnd hmEnd => cases hmEnd with | intro reason hre =>
        have hfrom1 := mrReaches_after_init h3.2.2.1.toHead hre.1.toHead hre.2
          (fun _ h => by cases h)
        cases (mrReachesHead_sim_back false p h3.2.2.2 hfrom1).1 reason hre.2 with
        | intro sf hsf =>
          dsimp only [ReachesResult]; rw [h3.1]
          exact ⟨sf, hsf⟩

/-- Soundness of `WellFormed` against MiniRust UB (`MiniRustAdmitted`):
`WellFormed p q → ¬ MrFaultsUB m₀`. -/
theorem forward_wellFormed_no_ub (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      WellFormed p q → ¬ MrFaultsUB m₀ := by
  intro m₀ hinitM hwf hub
  exact hwf.2 .undefined (forward_ub_contrapositive p q hadm m₀ hinitM hub)

/-- Forward simulation of divergence (`MiniRustAdmitted`):
`Diverges p q → MrDiverges m₀` (100% constructive via `mrIter`). -/
theorem forward_diverges (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      Diverges p q → MrDiverges m₀ := by
  intro m₀ hinitM hdiv
  cases init_fullStateRel false p q hadm with
  | intro s₀ h1 => cases h1 with | intro m₀' h2 => cases h2 with
    | intro m₁ h3 =>
      rw [h3.2.1] at hinitM; injection hinitM with hmeq
      have hmeq' := hmeq.symm; subst hmeq'
      cases hdiv with
      | intro s₀' hdiv1 =>
        rw [h3.1] at hdiv1
        cases hdiv1 with
        | intro hsEq htrEx =>
          injection hsEq with hse; subst hse
          cases htrEx with
          | intro aTrace haTrace =>
            cases mrReachesHead_to_iter h3.2.2.1.toHead with
            | intro k hk =>
              have hlockstep : ∀ n : Nat,
                  FullStateRel false p (aTrace n) (mrIter (k + n) m₀) ∧
                  mrStep (mrIter (k + n) m₀) = .step (mrIter (k + n + 1) m₀) := by
                intro n
                induction n with
                | zero =>
                  rw [Nat.add_zero, hk.1, haTrace.1]
                  cases haTrace.2 0 with
                  | intro c hc =>
                    have hc0 : c = 0 := hc.1; subst hc0
                    rw [haTrace.1] at hc
                    have hsim := fullStep_sim false p s₀ m₁ h3.2.2.2
                    rw [hc.2] at hsim
                    cases hsim with
                    | intro m' hm' =>
                      refine ⟨h3.2.2.2, ?_⟩
                      rw [mrIter_succ_right, hk.1]
                      dsimp only [mrNext]; rw [hm'.1]
                | succ j ih =>
                  have hstepA := haTrace.2 j
                  cases hstepA with
                  | intro c hc =>
                    have hc0 : c = 0 := hc.1; subst hc0
                    have hsim := fullStep_sim false p (aTrace j) (mrIter (k + j) m₀) ih.1
                    rw [hc.2] at hsim
                    cases hsim with
                    | intro m' hm' =>
                      have heqNext : mrIter (k + Nat.succ j) m₀ = m' := by
                        have hkn : k + Nat.succ j = (k + j) + 1 := Nat.add_succ k j
                        rw [hkn, mrIter_succ_right]
                        dsimp only [mrNext]; rw [hm'.1]
                      have hrelNext : FullStateRel false p (aTrace (j + 1))
                          (mrIter (k + Nat.succ j) m₀) := by
                        rw [heqNext]; exact hm'.2
                      cases haTrace.2 (j + 1) with
                      | intro c2 hc2 =>
                        have hc20 : c2 = 0 := hc2.1; subst hc20
                        have hsim2 := fullStep_sim false p (aTrace (j + 1))
                          (mrIter (k + Nat.succ j) m₀) hrelNext
                        rw [hc2.2] at hsim2
                        cases hsim2 with
                        | intro m'' hm'' =>
                          refine ⟨hrelNext, ?_⟩
                          rw [mrIter_succ_right]
                          dsimp only [mrNext]; rw [hm''.1]
              refine ⟨fun n => mrIter n m₀, rfl, fun n => ?_⟩
              cases Nat.lt_or_ge n k with
              | inl hlt => exact hk.2 n hlt
              | inr hge =>
                have hadd : k + (n - k) = n := Nat.add_sub_of_le hge
                have h := (hlockstep (n - k)).2
                rw [hadd] at h; exact h

end Anneal.MiniRust
