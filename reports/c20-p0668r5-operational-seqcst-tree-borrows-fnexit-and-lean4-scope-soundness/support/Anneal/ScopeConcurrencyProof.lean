-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.ScopeModel

namespace Anneal

universe u

structure ViewPCM (α : Type u) where
  op : α → α → α
  unit : α
  op_unit_right : ∀ x : α, op x unit = x
  op_unit_left : ∀ x : α, op unit x = x

def memViewPCM : ViewPCM Trusted.MemView where
  op := Trusted.viewJoin
  unit := Trusted.viewBot
  op_unit_right := fun v => by
    funext t
    dsimp [Trusted.viewJoin, Trusted.viewBot]
    cases Decidable.em (v t ≤ 0) with
    | inl h =>
      have hz : v t = 0 := Nat.eq_zero_of_le_zero h
      simp [hz]
    | inr h =>
      simp [h]
  op_unit_left := fun _ => rfl

def higherTypePredPCM : ViewPCM (Type 0 → Prop) where
  op := fun P Q X => P X ∨ Q X
  unit := fun _ => False
  op_unit_right := fun P => by
    funext X
    exact propext ⟨fun h => match h with | Or.inl hp => hp | Or.inr hf => False.elim hf, Or.inl⟩
  op_unit_left := fun P => by
    funext X
    exact propext ⟨fun h => match h with | Or.inl hf => False.elim hf | Or.inr hp => hp, Or.inr⟩

abbrev StepPred := Nat → Trusted.MemView → Prop
abbrev FuncTable := Trusted.FuncId → StepPred

def child1SendInv : StepPred :=
  fun _ v => 1 ≤ v 1

def child2SendInv : StepPred :=
  fun _ v => 2 ≤ v 2

def scopeFuncTable : FuncTable :=
  fun fid =>
    if fid == 1 then child1SendInv
    else if fid == 2 then child2SendInv
    else fun _ _ => True

-- Defined via kernel `@Nat.rec` rather than equation-compiler pattern matching:
-- under `prelude` without `Init.WF`, equation-compiler recursion emits a hidden
-- `Anneal.SendSyncInv._unsafe_rec` auxiliary that `TrustedBoundary` `"audit"` rejects!
def SendSyncInv (fuel : Nat) (tbl : FuncTable) (fid : Trusted.FuncId)
    (v : Trusted.MemView) : Prop :=
  @Nat.rec (fun _ => Prop) True (fun k ih => tbl fid k v ∧ ih) fuel

theorem viewJoin_ge_left (v1 v2 : Trusted.MemView) (t : Trusted.Tid) :
    v1 t ≤ memViewPCM.op v1 v2 t := by
  dsimp [memViewPCM, Trusted.viewJoin]
  cases Decidable.em (v1 t ≤ v2 t) with
  | inl h => simp [h]
  | inr h => simp [h]

theorem viewJoin_ge_right (v1 v2 : Trusted.MemView) (t : Trusted.Tid) :
    v2 t ≤ memViewPCM.op v1 v2 t := by
  dsimp [memViewPCM, Trusted.viewJoin]
  cases Decidable.em (v1 t ≤ v2 t) with
  | inl h => simp [h]
  | inr h =>
    have hle : v2 t ≤ v1 t := Nat.le_of_not_ge h
    simp [h, hle]

theorem scope_join_preserves_sendSyncInv (k : Nat) (v1 v2 : Trusted.MemView)
    (h1 : SendSyncInv (Nat.succ k) scopeFuncTable 1 v1)
    (h2 : SendSyncInv (Nat.succ k) scopeFuncTable 2 v2) :
    scopeFuncTable 1 k (memViewPCM.op v1 v2) ∧
    scopeFuncTable 2 k (memViewPCM.op v1 v2) := by
  constructor
  · dsimp [scopeFuncTable, child1SendInv]
    exact Nat.le_trans h1.left (viewJoin_ge_left v1 v2 1)
  · dsimp [scopeFuncTable, child2SendInv]
    exact Nat.le_trans h2.left (viewJoin_ge_right v1 v2 2)

theorem scope_sound : Trusted.ScopeSoundClaim := by
  intro sched
  cases sched with
  | child1First => decide
  | child2First => decide

theorem scope_unsound_when_drop_relaxed : Trusted.ScopeRelaxedDropUnsoundClaim := by
  intro sched
  cases sched with
  | child1First => decide
  | child2First => decide

theorem scope_relaxed_refutes_soundness :
    ¬ (∀ sched : Trusted.ChildSchedule,
        Trusted.runScopeExecution Trusted.MemOrdering.relaxed sched = some 46) := by
  intro h
  have h1 := h Trusted.ChildSchedule.child1First
  have h2 := scope_unsound_when_drop_relaxed Trusted.ChildSchedule.child1First
  rw [h2] at h1
  nomatch h1

end Anneal
