-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal.LoopInv
import Anneal.CnfOrd.Ord

namespace Anneal.CnfOrd

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.LoopInv

/-!
# `< ω^ω` MIR Loop Induction & Multi-Rank Worklists (`Anneal.CnfOrd.Worklist`)

Connects constructive `< ω^ω` Cantor Normal Form accessibility (`cnfAcc_all`)
to two multi-rank termination surfaces (`0` `noncomputable`, `0` `._unsafe_rec`,
`0` `omega`):

1. **`< ω^ω` MIR CFG loop induction (`wpLoop_cnfOrd_exists`,
   `wpLoop_cnfNorm_exists`, `execLoop_cnfNorm_exists`):** Generalizes
   `Anneal.LoopInv.wpLoop_nat_exists` from 1D `Nat` variants to arbitrary
   `< ω^ω` Cantor Normal Form rankings (`State → CnfOrd`), discharging
   nested/lexicographic MIR loops whose inner counters reset to unbounded
   runtime expressions whenever an outer counter decrements.
2. **Multi-rank worklist & wavefront termination (`RankedTask`, `WorklistPool`,
   `SpawnPolicy`, `spawnAdmissible`, `PolicyAdmissible`, `worklistStep`,
   `worklistStep_strict_cnf_descent`, `WorklistConverges`, `runWorklistSteps`,
   `worklist_terminates_all`, `isStrictlyDescendingTower`, `towerLookupNext`,
   `towerLookupNext_admissible`):** Certifies fuel-free termination across
   arbitrary-depth strictly descending rank towers (`r_0 > r_1 > ... > r_d`)
   with dynamic finite fanout and yield budgets over `fifoQueue` + `stealDeque`.
-/

/-! ## 1. `< ω^ω` Cantor Normal Form MIR CFG Loop Induction -/

private theorem wpLoop_cnfOrd_exists_aux {p : Program}
    {Inv Exit : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rank : State → CnfOrd}
    (hCanon : ∀ s, Inv s → isCanonicalCnf (rank s) = true)
    (hStep : ∀ s, Inv s →
      Exit s ∨ (∃ f,
        wpUntil p
          (fun s' => (Inv s' ∧ cnfLt (rank s') (rank s) = true) ∨ Exit s')
          onDone onFault f s))
    (ord : CnfOrd) (hCan : isCanonicalCnf ord = true) :
    ∀ (s : State), Inv s → rank s = ord →
      ∃ F, wpUntil p Exit onDone onFault F s := by
  induction cnfAcc_all ord hCan with
  | intro x _ ih =>
    intro s hInv hRank
    cases hStep s hInv with
    | inl hExit => exact ⟨0, wpUntil_stop hExit⟩
    | inr hIter =>
      refine wpUntil_bind_exists
        (mid := fun s' =>
          (Inv s' ∧ cnfLt (rank s') (rank s) = true) ∨ Exit s')
        hIter ?_
      intro s' hMid
      cases hMid with
      | inr hExit' => exact ⟨0, wpUntil_stop hExit'⟩
      | inl hCont =>
        have hCan' := hCanon s' hCont.1
        have hLtX : cnfLt (rank s') x = true := by
          rw [← hRank]; exact hCont.2
        exact ih (rank s') hCan' hLtX hCan' s' hCont.1 rfl

/-- `< ω^ω` Cantor Normal Form MIR loop-invariant induction over `wpUntil`:
if `rank s` is canonical on `Inv` and each non-`Exit` iteration reaches either
an `Exit` state or an `Inv` state with `cnfLt (rank s') (rank s) = true`, then
every `Inv` state reaches `Exit` in finite fuel. -/
theorem wpLoop_cnfOrd_exists {p : Program}
    {Inv Exit : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rank : State → CnfOrd}
    (hCanon : ∀ s, Inv s → isCanonicalCnf (rank s) = true)
    (hStep : ∀ s, Inv s →
      Exit s ∨ (∃ f,
        wpUntil p
          (fun s' => (Inv s' ∧ cnfLt (rank s') (rank s) = true) ∨ Exit s')
          onDone onFault f s))
    (s : State) (hInv : Inv s) :
    ∃ F, wpUntil p Exit onDone onFault F s :=
  wpLoop_cnfOrd_exists_aux hCanon hStep (rank s) (hCanon s hInv) s hInv rfl

/-- Normalization-wrapped `< ω^ω` MIR loop-invariant induction: automatically
normalizes `rawRank : State → CnfOrd` via `cnfNorm` so callers need not prove
`isCanonicalCnf` side conditions (including zero-coefficient terms). -/
theorem wpLoop_cnfNorm_exists {p : Program}
    {Inv Exit : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rawRank : State → CnfOrd}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (∃ f,
        wpUntil p
          (fun s' =>
            (Inv s' ∧ cnfLt (cnfNorm (rawRank s')) (cnfNorm (rawRank s)) = true)
            ∨ Exit s')
          onDone onFault f s))
    (s : State) (hInv : Inv s) :
    ∃ F, wpUntil p Exit onDone onFault F s :=
  wpLoop_cnfOrd_exists (rank := fun st => cnfNorm (rawRank st))
    (fun st _ => isCanonicalCnf_cnfNorm (rawRank st)) hStep s hInv

/-- Deterministic `execUntil` (`c = 0`) counterpart of `wpLoop_cnfNorm_exists`,
lifting directly into `wpUntil`. -/
theorem execLoop_cnfNorm_exists {p : Program}
    {Inv Exit : State → Prop} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} {rawRank : State → CnfOrd}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (∃ f,
        execUntil p
          (fun s' =>
            (Inv s' ∧ cnfLt (cnfNorm (rawRank s')) (cnfNorm (rawRank s)) = true)
            ∨ Exit s')
          onDone onFault f s))
    (s : State) (hInv : Inv s) :
    ∃ F, wpUntil p Exit onDone onFault F s :=
  wpLoop_cnfNorm_exists
    (fun st hI =>
      match hStep st hI with
      | .inl hEx => .inl hEx
      | .inr ⟨f, hExU⟩ => .inr ⟨f, wpUntil_iff_execUntil.mpr hExU⟩)
    s hInv

/-! ## 2. Multi-Rank `< ω^ω` Worklist & Wavefront Engine -/

private theorem boolFalseNeTrueW (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalseW (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandLeftW {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrueW h)
  | true => rfl

private theorem bandRightW {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrueW h)
  | true => exact h

private theorem natBeq_reflW (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_symmW (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  revert b
  induction a with
  | zero => intro b; cases b <;> rfl
  | succ _ ih =>
    intro b
    cases b with
    | zero => rfl
    | succ b' => exact ih b'

private theorem natEq_of_beqW (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrueW h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrueW h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem natBle_reflW (a : Nat) : Nat.ble a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBle_zero_leftW (a : Nat) : Nat.ble 0 a = true := by
  cases a <;> rfl

private theorem natBle_succ_rightW (a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble a (b + 1) = true := by
  revert b h
  induction a with
  | zero => intro _ _; rfl
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrueW h)
    | succ b' => exact ih b' h

private theorem natBle_transW (a b c : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b c = true) :
    Nat.ble a c = true := by
  revert b c
  induction a with
  | zero => intro _ c _ _; exact natBle_zero_leftW c
  | succ _ ih =>
    intro b c h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrueW h1)
    | succ b' =>
      cases c with
      | zero => exact False.elim (boolFalseNeTrueW h2)
      | succ c' => exact ih b' c' h1 h2

private theorem natAdd_zero_leftW (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_succ_leftW (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_commW (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => exact natAdd_zero_leftW b
  | succ a' ih => exact Eq.trans (natAdd_succ_leftW a' b) (congrArg Nat.succ ih)

private theorem natAdd_assocW (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBle_add_mono_rightW (a b c : Nat) (h : Nat.ble a b = true) :
    Nat.ble (a + c) (b + c) = true := by
  induction c with
  | zero => exact h
  | succ _ ih => exact ih

private theorem natBle_add_mono_leftW (c a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble (c + a) (c + b) = true := by
  rw [natAdd_commW c a, natAdd_commW c b]
  exact natBle_add_mono_rightW a b c h

private theorem natLtIrreflW (a : Nat) : natLt a a = false := by
  dsimp only [natLt]
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natLtSuccSelfW (a : Nat) : natLt a (a + 1) = true :=
  natBle_reflW (a + 1)

private theorem natLtTransW (a b c : Nat)
    (hab : natLt a b = true) (hbc : natLt b c = true) :
    natLt a c = true :=
  natBle_transW (a + 1) b c hab
    (natBle_transW b (b + 1) c (natBle_succ_rightW b b (natBle_reflW b)) hbc)

private theorem natLtOfLtOfBleW (a b c : Nat)
    (hab : natLt a b = true) (hbc : Nat.ble b c = true) :
    natLt a c = true :=
  natBle_transW (a + 1) b c hab hbc

private theorem natBeqFalseOfLtW {a b : Nat} (h : natLt a b = true) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true =>
    rw [natEq_of_beqW a b hb] at h
    exact False.elim (boolTrueNeFalseW (Eq.trans (Eq.symm h) (natLtIrreflW b)))

private theorem natLt_add_left_of_ltW (a b r : Nat) (h : natLt a b = true) :
    natLt (a + r) (b + r) = true := by
  dsimp only [natLt] at h
  dsimp only [natLt]
  rw [natAdd_commW a r, natAdd_commW b r]
  exact natBle_add_mono_leftW r (a + 1) b h

private def listFoldAuxW {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : List α × β :=
  List.foldr (fun x acc => (x :: acc.1, cons x acc.1 acc.2)) ([], nil) xs

private theorem listFoldAuxW_fst {α β : Type} (nil : β)
    (cons : α → List α → β → β) (xs : List α) :
    (listFoldAuxW nil cons xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

private def listFoldW {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : β :=
  (listFoldAuxW nil cons xs).2

private theorem listFoldW_cons {α β : Type} (nil : β)
    (cons : α → List α → β → β) (x : α) (tl : List α) :
    listFoldW nil cons (x :: tl) = cons x tl (listFoldW nil cons tl) := by
  dsimp only [listFoldW]
  change (cons x (listFoldAuxW nil cons tl).1 (listFoldAuxW nil cons tl).2) = _
  rw [listFoldAuxW_fst]

/-- Multi-rank worklist task descriptor with tier `rank` and remaining yield
budget `remYields`. -/
structure RankedTask where
  taskId : Nat
  rank : Nat
  remYields : Nat

/-- Dual-queue worklist state (`fifoQueue` + `stealDeque`) with deterministic
task-ID, completion, and step counters. -/
structure WorklistPool where
  fifoQueue : List RankedTask
  stealDeque : List RankedTask
  nextTaskId : Nat
  completedCount : Nat
  stepCount : Nat

/-- Exponent-`q` contribution of a single `RankedTask`:
`ω^{2·rank + 1} · 1 + ω^{2·rank} · remYields`. -/
def taskWeightAt (q : Nat) (t : RankedTask) : Nat :=
  (match Nat.beq (t.rank + t.rank + 1) q with | true => 1 | false => 0) +
  (match Nat.beq (t.rank + t.rank) q with | true => t.remYields | false => 0)

/-- Total exponent-`q` weight across a task list. -/
def tasksWeightAt (q : Nat) (qs : List RankedTask) : Nat :=
  qs.foldr (fun t acc => taskWeightAt q t + acc) 0

/-- Hessenberg CNF contribution of task `t` added onto `acc`. -/
def taskMeasure (t : RankedTask) (acc : CnfOrd) : CnfOrd :=
  cnfAddTerm (t.rank + t.rank + 1) 1
    (cnfAddTerm (t.rank + t.rank) t.remYields acc)

/-- Hessenberg CNF measure of task queue `qs` folded onto `init`. -/
def queueMeasure (qs : List RankedTask) (init : CnfOrd) : CnfOrd :=
  qs.foldr taskMeasure init

/-- Canonical `< ω^ω` Cantor Normal Form ordinal measure of `WorklistPool`. -/
def poolMeasure (w : WorklistPool) : CnfOrd :=
  queueMeasure w.fifoQueue (queueMeasure w.stealDeque [])

private theorem tasksWeightAt_append (q : Nat) (xs ys : List RankedTask) :
    tasksWeightAt q (xs ++ ys) = tasksWeightAt q xs + tasksWeightAt q ys := by
  induction xs with
  | nil => exact Eq.symm (natAdd_zero_leftW (tasksWeightAt q ys))
  | cons hd _ ih =>
    change taskWeightAt q hd + tasksWeightAt q (_ ++ ys) =
      (taskWeightAt q hd + tasksWeightAt q _) + tasksWeightAt q ys
    rw [ih, natAdd_assocW]

private theorem queueMeasure_canonical_and_coeff (q : Nat)
    (qs : List RankedTask) (init : CnfOrd)
    (hInit : isCanonicalCnf init = true) :
    isCanonicalCnf (queueMeasure qs init) = true ∧
    cnfCoeffAt q (queueMeasure qs init) =
      tasksWeightAt q qs + cnfCoeffAt q init := by
  induction qs with
  | nil => exact ⟨hInit, Eq.symm (natAdd_zero_leftW (cnfCoeffAt q init))⟩
  | cons t _ ih =>
    exact ⟨isCanonicalCnf_cnfAddTerm (t.rank + t.rank + 1) 1 _
      (isCanonicalCnf_cnfAddTerm (t.rank + t.rank) t.remYields _ ih.1),
      Eq.trans (cnfCoeffAt_cnfAddTerm q (t.rank + t.rank + 1) 1 _)
        (Eq.trans
          (congrArg (Nat.add _)
            (cnfCoeffAt_cnfAddTerm q (t.rank + t.rank) t.remYields _))
          (Eq.trans (Eq.symm (natAdd_assocW _ _ _))
            (Eq.trans (congrArg (Nat.add (taskWeightAt q t)) ih.2)
              (Eq.symm (natAdd_assocW _ _ _)))))⟩

/-- `poolMeasure w` is unconditionally canonical (`isCanonicalCnf`). -/
theorem poolMeasure_canonical (w : WorklistPool) :
    isCanonicalCnf (poolMeasure w) = true :=
  (queueMeasure_canonical_and_coeff 0 w.fifoQueue _
    (queueMeasure_canonical_and_coeff 0 w.stealDeque [] rfl).1).1

/-- Exponent-`q` coefficient of `poolMeasure w` equals the sum of queue weights.
-/
theorem cnfCoeffAt_poolMeasure (q : Nat) (w : WorklistPool) :
    cnfCoeffAt q (poolMeasure w) =
      tasksWeightAt q w.fifoQueue + tasksWeightAt q w.stealDeque := by
  have hS := queueMeasure_canonical_and_coeff q w.stealDeque [] rfl
  exact Eq.trans (queueMeasure_canonical_and_coeff q w.fifoQueue _ hS.1).2
    (congrArg (Nat.add (tasksWeightAt q w.fifoQueue)) hS.2)

/-- Spawn admissibility guard: spawning `k > 0` child tasks requires strict tier
drop `childRank < parentRank` (`k = 0` spawns nothing and is always valid). -/
def spawnAdmissible (parentRank k childRank : Nat) : Bool :=
  match k with
  | 0 => true
  | _ + 1 => natLt childRank parentRank

/-- Spawns `count` child tasks starting at `baseId` at `(rank, yields)`. -/
def mkRankedTasks (baseId count rank yields : Nat) : List RankedTask :=
  @Nat.rec (fun _ => Nat → List RankedTask)
    (fun _ => [])
    (fun _ ih tid => RankedTask.mk tid rank yields :: ih (tid + 1))
    count baseId

/-- Tier-indexed spawn policy mapping `parentRank` to
`(fanout, childRank, childYields)`. -/
abbrev SpawnPolicy : Type := Nat → (Nat × Nat × Nat)

/-- Policy-level admissibility: every tier satisfies `spawnAdmissible`. -/
def PolicyAdmissible (pol : SpawnPolicy) : Prop :=
  ∀ (r : Nat), spawnAdmissible r (pol r).1 (pol r).2.1 = true

/-- Outcome of a single multi-rank worklist step. -/
inductive WorklistOut where
  | returned (wOut : WorklistPool)
  | faultInvalidSpawn

/-- `true` iff either `fifoQueue` or `stealDeque` is non-empty. -/
def poolIsNonEmpty (w : WorklistPool) : Bool :=
  match w.fifoQueue with
  | _ :: _ => true
  | [] =>
    match w.stealDeque with
    | _ :: _ => true
    | [] => false

/-- Executes one popped `RankedTask` under `pol`, failing closed with
`.faultInvalidSpawn` if `spawnAdmissible` rejects `(hd.rank, k, childRank)`. -/
def execWorklistPopped (pol : SpawnPolicy) (hd : RankedTask)
    (remFifo remSteal : List RankedTask) (w : WorklistPool) : WorklistOut :=
  let polRes := pol hd.rank
  let k := polRes.1
  let childRank := polRes.2.1
  let childYields := polRes.2.2
  match spawnAdmissible hd.rank k childRank with
  | false => .faultInvalidSpawn
  | true =>
    let children := mkRankedTasks w.nextTaskId k childRank childYields
    let nextSteal := children ++ remSteal
    match hd.remYields with
    | y' + 1 =>
      let hdNext := RankedTask.mk hd.taskId hd.rank y'
      .returned {
        fifoQueue := remFifo ++ [hdNext]
        stealDeque := nextSteal
        nextTaskId := w.nextTaskId + k
        completedCount := w.completedCount
        stepCount := w.stepCount + 1
      }
    | 0 =>
      .returned {
        fifoQueue := remFifo
        stealDeque := nextSteal
        nextTaskId := w.nextTaskId + k
        completedCount := w.completedCount + 1
        stepCount := w.stepCount + 1
      }

/-- Single worklist dispatch step: pops `fifoQueue` first, falling back to
`stealDeque`, or faults if called on an empty pool. -/
def worklistStep (pol : SpawnPolicy) (w : WorklistPool) : WorklistOut :=
  match w.fifoQueue with
  | hd :: ft => execWorklistPopped pol hd ft w.stealDeque w
  | [] =>
    match w.stealDeque with
    | hd :: stTail => execWorklistPopped pol hd [] stTail w
    | [] => .faultInvalidSpawn

private theorem childRank_double_plus1_lt (rc rp : Nat)
    (hLt : natLt rc rp = true) :
    natLt (rc + rc + 1) (rp + rp) = true := by
  dsimp only [natLt] at hLt
  dsimp only [natLt]
  have hSum : (rc + rc + 1) + 1 = (rc + 1) + (rc + 1) := by
    rw [natAdd_assocW (rc + rc) 1 1, natAdd_assocW rc rc 2,
      natAdd_commW rc 2, ← natAdd_assocW rc 2 rc]
    have h2 : rc + 2 = (rc + 1) + 1 := rfl
    rw [h2, natAdd_assocW (rc + 1) 1 rc, natAdd_commW 1 rc]
  rw [hSum]
  exact natBle_transW ((rc + 1) + (rc + 1)) (rp + (rc + 1)) (rp + rp)
    (natBle_add_mono_rightW (rc + 1) rp (rc + 1) hLt)
    (natBle_add_mono_leftW rp (rc + 1) rp hLt)

private theorem tasksWeightAt_mkRankedTasks_zero_above
    (q baseId k rc cy rp : Nat)
    (hAdm : spawnAdmissible rp k rc = true)
    (hGe : Nat.ble (rp + rp) q = true) :
    tasksWeightAt q (mkRankedTasks baseId k rc cy) = 0 := by
  cases k with
  | zero => rfl
  | succ k' =>
    dsimp only [spawnAdmissible] at hAdm
    have hOddLt : natLt (rc + rc + 1) q = true :=
      natLtOfLtOfBleW (rc + rc + 1) (rp + rp) q
        (childRank_double_plus1_lt rc rp hAdm) hGe
    have hEvenLt : natLt (rc + rc) q = true :=
      natLtTransW (rc + rc) (rc + rc + 1) q (natLtSuccSelfW (rc + rc)) hOddLt
    have hB1 : Nat.beq (rc + rc + 1) q = false := natBeqFalseOfLtW hOddLt
    have hB0 : Nat.beq (rc + rc) q = false := natBeqFalseOfLtW hEvenLt
    revert baseId
    induction k' with
    | zero =>
      intro baseId
      dsimp only [mkRankedTasks, tasksWeightAt, List.foldr, taskWeightAt]
      rw [hB1, hB0]
      rfl
    | succ m ih =>
      intro baseId
      change taskWeightAt q (RankedTask.mk baseId rc cy) +
        tasksWeightAt q (mkRankedTasks (baseId + 1) (m + 1) rc cy) = 0
      dsimp only [taskWeightAt]
      rw [hB1, hB0, ih (baseId + 1)]
      rfl

private theorem taskWeightAt_self_even (t : RankedTask) :
    taskWeightAt (t.rank + t.rank) t = t.remYields := by
  dsimp only [taskWeightAt]
  have hNe : Nat.beq (t.rank + t.rank + 1) (t.rank + t.rank) = false := by
    rw [natBeq_symmW]
    exact natBeqFalseOfLtW (natLtSuccSelfW (t.rank + t.rank))
  rw [hNe, natBeq_reflW (t.rank + t.rank), natAdd_zero_leftW]

private theorem taskWeightAt_self_odd (t : RankedTask) :
    taskWeightAt (t.rank + t.rank + 1) t = 1 := by
  dsimp only [taskWeightAt]
  have hNe : Nat.beq (t.rank + t.rank) (t.rank + t.rank + 1) = false :=
    natBeqFalseOfLtW (natLtSuccSelfW (t.rank + t.rank))
  rw [natBeq_reflW (t.rank + t.rank + 1), hNe]
  rfl

private theorem taskWeightAt_zero_above_odd (t : RankedTask) (q : Nat)
    (hGt : natLt (t.rank + t.rank + 1) q = true) :
    taskWeightAt q t = 0 := by
  dsimp only [taskWeightAt]
  have hEvenGt : natLt (t.rank + t.rank) q = true :=
    natLtTransW (t.rank + t.rank) (t.rank + t.rank + 1) q
      (natLtSuccSelfW (t.rank + t.rank)) hGt
  rw [natBeqFalseOfLtW hGt, natBeqFalseOfLtW hEvenGt]
  rfl

private theorem execWorklistPopped_strict_cnf_descent (pol : SpawnPolicy)
    (hd : RankedTask) (remFifo remSteal : List RankedTask)
    (w wOut : WorklistPool)
    (hQueueSum : ∀ (q : Nat),
      cnfCoeffAt q (poolMeasure w) =
        taskWeightAt q hd + (tasksWeightAt q remFifo + tasksWeightAt q remSteal))
    (hStep : execWorklistPopped pol hd remFifo remSteal w = .returned wOut) :
    cnfLt (poolMeasure wOut) (poolMeasure w) = true := by
  dsimp only [execWorklistPopped] at hStep
  cases hAdm : spawnAdmissible hd.rank (pol hd.rank).1 (pol hd.rank).2.1 with
  | false => rw [hAdm] at hStep; nomatch hStep
  | true =>
    rw [hAdm] at hStep
    dsimp only at hStep
    cases hy : hd.remYields with
    | succ y' =>
      rw [hy] at hStep
      injection hStep with hwOut
      rw [← hwOut]
      let q0 := hd.rank + hd.rank
      apply cnfLt_of_coeff_drop _ _
        (poolMeasure_canonical _) (poolMeasure_canonical w) q0
      · rw [cnfCoeffAt_poolMeasure, hQueueSum q0]
        dsimp only
        rw [tasksWeightAt_append, tasksWeightAt_append]
        have hCh0 := tasksWeightAt_mkRankedTasks_zero_above q0 w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2
          hd.rank hAdm (natBle_reflW q0)
        rw [hCh0, natAdd_zero_leftW]
        have hSingle :
            tasksWeightAt q0 [RankedTask.mk hd.taskId hd.rank y'] = y' := by
          dsimp only [q0, tasksWeightAt, List.foldr]
          rw [taskWeightAt_self_even (RankedTask.mk hd.taskId hd.rank y')]
          rfl
        rw [hSingle]
        dsimp only [q0]
        rw [taskWeightAt_self_even hd, hy]
        rw [natAdd_commW (tasksWeightAt (hd.rank + hd.rank) remFifo) y',
          natAdd_assocW y' (tasksWeightAt (hd.rank + hd.rank) remFifo)
            (tasksWeightAt (hd.rank + hd.rank) remSteal)]
        exact natLt_add_left_of_ltW y' (y' + 1) _ (natLtSuccSelfW y')
      · intro q hGt
        rw [cnfCoeffAt_poolMeasure, hQueueSum q]
        dsimp only
        rw [tasksWeightAt_append, tasksWeightAt_append]
        have hGe : Nat.ble (hd.rank + hd.rank) q = true :=
          natBle_transW (hd.rank + hd.rank) (hd.rank + hd.rank + 1) q
            (natBle_succ_rightW _ _ (natBle_reflW _)) hGt
        have hCh0 := tasksWeightAt_mkRankedTasks_zero_above q w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2
          hd.rank hAdm hGe
        rw [hCh0, natAdd_zero_leftW]
        have hSameHd :
            tasksWeightAt q [RankedTask.mk hd.taskId hd.rank y'] =
              taskWeightAt q hd := by
          dsimp only [tasksWeightAt, List.foldr, taskWeightAt]
          have hEvenFalse : Nat.beq (hd.rank + hd.rank) q = false :=
            natBeqFalseOfLtW hGt
          rw [hEvenFalse]
          cases Nat.beq (hd.rank + hd.rank + 1) q <;> rfl
        rw [hSameHd,
          natAdd_commW (tasksWeightAt q remFifo) (taskWeightAt q hd),
          natAdd_assocW (taskWeightAt q hd) (tasksWeightAt q remFifo)
            (tasksWeightAt q remSteal)]
    | zero =>
      rw [hy] at hStep
      injection hStep with hwOut
      rw [← hwOut]
      let q0 := hd.rank + hd.rank + 1
      apply cnfLt_of_coeff_drop _ _
        (poolMeasure_canonical _) (poolMeasure_canonical w) q0
      · rw [cnfCoeffAt_poolMeasure, hQueueSum q0]
        dsimp only
        rw [tasksWeightAt_append]
        have hGe : Nat.ble (hd.rank + hd.rank) q0 = true :=
          natBle_succ_rightW (hd.rank + hd.rank) (hd.rank + hd.rank)
            (natBle_reflW _)
        have hCh0 := tasksWeightAt_mkRankedTasks_zero_above q0 w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2
          hd.rank hAdm hGe
        rw [hCh0, natAdd_zero_leftW]
        dsimp only [q0]
        rw [taskWeightAt_self_odd hd]
        let R := tasksWeightAt (hd.rank + hd.rank + 1) remFifo +
          tasksWeightAt (hd.rank + hd.rank + 1) remSteal
        change natLt R (1 + R) = true
        rw [natAdd_commW 1 R]
        exact natLtSuccSelfW R
      · intro q hGt
        rw [cnfCoeffAt_poolMeasure, hQueueSum q]
        dsimp only
        rw [tasksWeightAt_append]
        have hGe : Nat.ble (hd.rank + hd.rank) q = true :=
          natBle_transW (hd.rank + hd.rank) q0 q
            (natBle_succ_rightW _ _ (natBle_reflW _))
            (natBle_transW q0 (q0 + 1) q
              (natBle_succ_rightW _ _ (natBle_reflW _)) hGt)
        have hCh0 := tasksWeightAt_mkRankedTasks_zero_above q w.nextTaskId
          (pol hd.rank).1 (pol hd.rank).2.1 (pol hd.rank).2.2
          hd.rank hAdm hGe
        rw [hCh0, natAdd_zero_leftW, taskWeightAt_zero_above_odd hd q hGt,
          natAdd_zero_leftW]

/-- Every successful `worklistStep` strictly decreases `poolMeasure` in `< ω^ω`.
-/
theorem worklistStep_strict_cnf_descent (pol : SpawnPolicy)
    (w wOut : WorklistPool)
    (hEval : worklistStep pol w = .returned wOut) :
    cnfLt (poolMeasure wOut) (poolMeasure w) = true := by
  dsimp only [worklistStep] at hEval
  cases hF : w.fifoQueue with
  | cons hd ft =>
    rw [hF] at hEval
    apply execWorklistPopped_strict_cnf_descent pol hd ft w.stealDeque w wOut _
      hEval
    intro q
    rw [cnfCoeffAt_poolMeasure, hF]
    dsimp only [tasksWeightAt, List.foldr]
    rw [natAdd_assocW]
  | nil =>
    rw [hF] at hEval
    cases hS : w.stealDeque with
    | nil => rw [hS] at hEval; nomatch hEval
    | cons hd stTail =>
      rw [hS] at hEval
      apply execWorklistPopped_strict_cnf_descent pol hd [] stTail w wOut _
        hEval
      intro q
      rw [cnfCoeffAt_poolMeasure, hF, hS]
      dsimp only [tasksWeightAt, List.foldr]
      rw [natAdd_zero_leftW, natAdd_zero_leftW]

/-- Progress on non-empty pools for admissible policies: `worklistStep` never
faults when `PolicyAdmissible pol` and `poolIsNonEmpty w = true`. -/
theorem nonEmptyPool_worklistStep_returns (pol : SpawnPolicy)
    (hPol : PolicyAdmissible pol) (w : WorklistPool)
    (hNonEmpty : poolIsNonEmpty w = true) :
    ∃ wOut : WorklistPool, worklistStep pol w = .returned wOut := by
  dsimp only [worklistStep]
  dsimp only [poolIsNonEmpty] at hNonEmpty
  cases hF : w.fifoQueue with
  | cons hd ft =>
    dsimp only [execWorklistPopped]
    rw [hPol hd.rank]
    dsimp only
    cases hd.remYields <;> exact ⟨_, rfl⟩
  | nil =>
    rw [hF] at hNonEmpty
    cases hS : w.stealDeque with
    | nil => rw [hS] at hNonEmpty; exact False.elim (boolFalseNeTrueW hNonEmpty)
    | cons hd stTail =>
      dsimp only [execWorklistPopped]
      rw [hPol hd.rank]
      dsimp only
      cases hd.remYields <;> exact ⟨_, rfl⟩

/-- Fuel-free inductive multi-rank worklist convergence judgment. -/
inductive WorklistConverges (pol : SpawnPolicy) :
    WorklistPool → WorklistPool → Prop where
  | quiescent (w : WorklistPool) (hEmpty : poolIsNonEmpty w = false) :
      WorklistConverges pol w w
  | step (w wNext wFinal : WorklistPool)
      (hNonEmpty : poolIsNonEmpty w = true)
      (hStep : worklistStep pol w = .returned wNext)
      (hLt : cnfLt (poolMeasure wNext) (poolMeasure w) = true)
      (hRest : WorklistConverges pol wNext wFinal) :
      WorklistConverges pol w wFinal

/-- Computable `@Nat.rec` multi-step runner for `worklistStep`. -/
def runWorklistSteps (fuel : Nat) (pol : SpawnPolicy) (w : WorklistPool) :
    Option WorklistPool :=
  @Nat.rec (fun _ => WorklistPool → Option WorklistPool)
    (fun _ => none)
    (fun _ ih cur =>
      match poolIsNonEmpty cur with
      | false => some cur
      | true =>
        match worklistStep pol cur with
        | .returned next => ih next
        | .faultInvalidSpawn => none)
    fuel w

/-- Extracts quiescent empty-queue invariants and finite execution `fuel` from
`WorklistConverges`. -/
theorem worklistConverges_extract_fuel (pol : SpawnPolicy)
    (w wFinal : WorklistPool)
    (hConv : WorklistConverges pol w wFinal) :
    wFinal.fifoQueue = [] ∧
    wFinal.stealDeque = [] ∧
    poolMeasure wFinal = [] ∧
    ∃ fuel : Nat, runWorklistSteps fuel pol w = some wFinal := by
  induction hConv with
  | quiescent w0 hEmp =>
    dsimp only [poolIsNonEmpty] at hEmp
    cases hF : w0.fifoQueue with
    | cons _ _ => rw [hF] at hEmp; exact False.elim (boolTrueNeFalseW hEmp)
    | nil =>
      rw [hF] at hEmp
      cases hS : w0.stealDeque with
      | cons _ _ => rw [hS] at hEmp; exact False.elim (boolTrueNeFalseW hEmp)
      | nil =>
        refine ⟨rfl, rfl, ?_, ⟨1, ?_⟩⟩
        · dsimp only [poolMeasure]; rw [hF, hS]; rfl
        · change (match poolIsNonEmpty w0 with
            | false => some w0 | true => _) = some w0
          dsimp only [poolIsNonEmpty]; rw [hF, hS]
  | step w0 w1 wf hNe hSt _ _ ih =>
    cases ih.2.2.2 with
    | intro f hf =>
      refine ⟨ih.1, ih.2.1, ih.2.2.1, ⟨f + 1, ?_⟩⟩
      change (match poolIsNonEmpty w0 with
        | false => some w0
        | true =>
          match worklistStep pol w0 with
          | .returned next => runWorklistSteps f pol next
          | .faultInvalidSpawn => none) = some wf
      rw [hNe, hSt]
      exact hf

/-- Universal `< ω^ω` worklist termination (`[]` zero axioms): every admissible
`SpawnPolicy` drains every initial `WorklistPool` to empty queues in finite
fuel. -/
theorem worklist_terminates_all (pol : SpawnPolicy)
    (hPol : PolicyAdmissible pol) (w0 : WorklistPool) :
    ∃ wFinal : WorklistPool,
      WorklistConverges pol w0 wFinal ∧
      wFinal.fifoQueue = [] ∧
      wFinal.stealDeque = [] ∧
      poolMeasure wFinal = [] ∧
      (∃ fuel : Nat, runWorklistSteps fuel pol w0 = some wFinal) := by
  have hUniv :
      ∀ (ord : CnfOrd), isCanonicalCnf ord = true →
      ∀ (w : WorklistPool), poolMeasure w = ord →
      ∃ wFinal : WorklistPool, WorklistConverges pol w wFinal := by
    intro ord hCan
    induction cnfAcc_all ord hCan with
    | intro x _ ih =>
      intro w hMeas
      cases hNe : poolIsNonEmpty w with
      | false => exact ⟨w, WorklistConverges.quiescent w hNe⟩
      | true =>
        cases nonEmptyPool_worklistStep_returns pol hPol w hNe with
        | intro wNext hStep =>
          have hLt0 := worklistStep_strict_cnf_descent pol w wNext hStep
          have hLtX : cnfLt (poolMeasure wNext) x = true := by
            rw [← hMeas]; exact hLt0
          have hCanNext := poolMeasure_canonical wNext
          cases ih (poolMeasure wNext) hCanNext hLtX hCanNext wNext rfl with
          | intro wFinal hRest =>
            exact ⟨wFinal,
              WorklistConverges.step w wNext wFinal hNe hStep hLt0 hRest⟩
  cases hUniv (poolMeasure w0) (poolMeasure_canonical w0) w0 rfl with
  | intro wFinal hConv =>
    have hEx := worklistConverges_extract_fuel pol w0 wFinal hConv
    exact ⟨wFinal, hConv, hEx.1, hEx.2.1, hEx.2.2.1, hEx.2.2.2⟩

/-- `true` iff `ranks` is a strictly descending rank tower
`r_0 > r_1 > ... > r_d`. -/
def isStrictlyDescendingTower (ranks : List Nat) : Bool :=
  listFoldW true
    (fun r tl ih =>
      match tl with
      | [] => true
      | nextR :: _ => natLt nextR r && ih)
    ranks

/-- Builds a multi-tier `SpawnPolicy` stepping down a strictly descending rank
tower `ranks` with uniform `(fanout, childYields)` at each hop. -/
def towerLookupNext (ranks : List Nat) (fanout childYields qRank : Nat) :
    Nat × Nat × Nat :=
  listFoldW (0, 0, 0)
    (fun r tl ih =>
      match tl with
      | [] => (0, 0, 0)
      | nextR :: _ =>
        match Nat.beq qRank r with
        | true => (fanout, nextR, childYields)
        | false => ih)
    ranks

/-- Every strictly descending rank tower defines an admissible `SpawnPolicy`. -/
theorem towerLookupNext_admissible (ranks : List Nat)
    (fanout childYields : Nat)
    (hDesc : isStrictlyDescendingTower ranks = true) :
    PolicyAdmissible (towerLookupNext ranks fanout childYields) := by
  intro qRank
  induction ranks with
  | nil =>
    dsimp only [towerLookupNext, listFoldW, listFoldAuxW, List.foldr,
      spawnAdmissible]
  | cons r tl ih =>
    dsimp only [isStrictlyDescendingTower] at hDesc
    rw [listFoldW_cons] at hDesc
    dsimp only [towerLookupNext]
    rw [listFoldW_cons]
    cases tl with
    | nil => dsimp only [spawnAdmissible]
    | cons nextR _ =>
      dsimp only at hDesc
      cases hEq : Nat.beq qRank r with
      | true =>
        dsimp only [spawnAdmissible]
        have hLtNext : natLt nextR qRank = true := by
          rw [natEq_of_beqW qRank r hEq]
          exact bandLeftW hDesc
        cases fanout with
        | zero => rfl
        | succ _ => exact hLtNext
      | false =>
        dsimp only
        exact ih (bandRightW hDesc)

end Anneal.CnfOrd
