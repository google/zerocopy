-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Trusted
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Anneal.Core.SepPCM

namespace Anneal.ConcurrentSeamsProof

open Anneal.Core

/-!
# Separation Algebra Seams for Concurrent Rust Verification in Anneal

Kernel-checked theorems over `Anneal.Core.SepPCM` establishing:
1. `explPCM_idempotent_eq_unit`: `ExplPCM.cancellative` collapses every
   idempotent/duplicable element (`pcm.op a a = some a`) to `pcm.unit`, proving
   that persistent concurrent resources (`Once` initialization agreement,
   duplicable `Arc` read knowledge, and monotonic weak-memory view bounds)
   cannot be represented directly as non-unit elements of `ExplPCM`.
2. `ResPCM`: Constructive non-cancellative resource algebra with persistent core
   `core : M → Option M` (`0` `Quot.sound`, `0` `Classical.choice`, `0`
   `_unsafe_rec`), conservatively embedding every `ExplPCM` via
   `explToResPCM` with identical `sepConj`/`sepWand`, while admitting
   nontrivial duplicable `AgreeElem` resources, `persistently` (`□ P`
   duplicability `□ P ⊢ □ P ∗ □ P`), and product composition with exclusive
   `Anneal.Core.ByteHeaplet` ownership.
-/

/-- In any cancellative `ExplPCM`, every idempotent element (`a • a = some a`)
is forced equal to `pcm.unit`. Consequently, non-trivial duplicable/persistent
ghost knowledge cannot inhabit `ExplPCM` directly. -/
theorem explPCM_idempotent_eq_unit {M : Type} (pcm : ExplPCM M) (a : M)
    (hIdem : pcm.op a a = some a) : a = pcm.unit := by
  have hUnit : pcm.op a pcm.unit = some a := pcm.unit_right a
  exact pcm.cancellative a a pcm.unit a hIdem hUnit

/-- Corollary: no non-unit element of `ExplPCM` can satisfy separating
self-duplication `h = a ⊢ (h = a) ∗ (h = a)` on the same state `a`. -/
theorem explPCM_no_nonunit_self_duplication {M : Type} (pcm : ExplPCM M)
    (a : M) (hNe : a ≠ pcm.unit) :
    ¬ sepConj pcm (fun h => h = a) (fun h => h = a) a := by
  intro hDup
  let ⟨h₁, h₂, hop, he₁, he₂⟩ := hDup
  rw [he₁, he₂] at hop
  exact hNe (explPCM_idempotent_eq_unit pcm a hop)

universe u

def resOptBind {α β : Type u} (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | none => none
  | some a => f a

/-- Constructive non-cancellative Resource Algebra (`ResPCM`) with partial
commutative associative composition `op`, unit `unit`, and persistent core
projection `core : M → Option M` capturing duplicable knowledge. -/
structure ResPCM (M : Type u) where
  unit : M
  op : M → M → Option M
  core : M → Option M
  op_comm : ∀ a b : M, op a b = op b a
  op_assoc : ∀ a b c : M,
    resOptBind (op a b) (fun ab => op ab c) =
      resOptBind (op b c) (fun bc => op a bc)
  unit_left : ∀ a : M, op unit a = some a
  core_unit : core unit = some unit
  core_id : ∀ a ca : M, core a = some ca → op ca a = some a
  core_idem : ∀ a ca : M, core a = some ca → core ca = some ca

theorem ResPCM.unit_right {M : Type u} (rpcm : ResPCM M) (a : M) :
    rpcm.op a rpcm.unit = some a := by
  rw [rpcm.op_comm, rpcm.unit_left]

theorem ResPCM.core_duplicable {M : Type u} (rpcm : ResPCM M) {a ca : M}
    (hCore : rpcm.core a = some ca) : rpcm.op ca ca = some ca := by
  have hIdem : rpcm.core ca = some ca := rpcm.core_idem a ca hCore
  exact rpcm.core_id ca ca hIdem

/-- Pointwise assertions over `ResPCM`. -/
abbrev ResProp (M : Type u) : Type u := M → Prop

def ResEntails {M : Type u} (P Q : ResProp M) : Prop :=
  ∀ h : M, P h → Q h

def ResEquiv {M : Type u} (P Q : ResProp M) : Prop :=
  ∀ h : M, P h ↔ Q h

def resConj {M : Type u} (rpcm : ResPCM M) (P Q : ResProp M) : ResProp M :=
  fun h => ∃ h₁ h₂ : M, rpcm.op h₁ h₂ = some h ∧ P h₁ ∧ Q h₂

def resWand {M : Type u} (rpcm : ResPCM M) (P Q : ResProp M) : ResProp M :=
  fun h => ∀ h' hCombined : M,
    rpcm.op h h' = some hCombined → P h' → Q hCombined

/-- Persistent modality `□ P`: holds at `h` iff `h` has a persistent core `ch`
satisfying `P ch`. -/
def persistently {M : Type u} (rpcm : ResPCM M) (P : ResProp M) : ResProp M :=
  fun h => ∃ ch : M, rpcm.core h = some ch ∧ P ch

/-- Key concurrency law: `□ P` is separatingly duplicable (`□ P ⊢ □ P ∗ □ P`)
even when `M` also carries linear/exclusive ownership! -/
theorem persistently_duplicable {M : Type u} (rpcm : ResPCM M) (P : ResProp M) :
    ResEntails (persistently rpcm P)
      (resConj rpcm (persistently rpcm P) (persistently rpcm P)) := by
  intro h hPers
  let ⟨ch, hCore, hP⟩ := hPers
  have hId : rpcm.op ch h = some h := rpcm.core_id h ch hCore
  have hChCore : rpcm.core ch = some ch := rpcm.core_idem h ch hCore
  exact ⟨ch, h, hId, ⟨ch, hChCore, hP⟩, ⟨ch, hCore, hP⟩⟩

/-- Every cancellative `ExplPCM` embeds conservatively into `ResPCM` with
trivial unit core and definitionally identical `sepConj` / `sepWand`. -/
def explToResPCM {M : Type} (pcm : ExplPCM M) : ResPCM M where
  unit := pcm.unit
  op := pcm.op
  core := fun _ => some pcm.unit
  op_comm := pcm.op_comm
  op_assoc := by
    intro a b c
    have h := pcm.op_assoc a b c
    cases hab : pcm.op a b <;> cases hbc : pcm.op b c <;>
      (rw [hab, hbc] at h; exact h)
  unit_left := pcm.unit_left
  core_unit := rfl
  core_id := by
    intro a ca hEq
    injection hEq with hCa
    subst hCa
    exact pcm.unit_left a
  core_idem := by
    intro _ ca hEq
    injection hEq with hCa
    subst hCa
    rfl

theorem toResPCM_conj_iff {M : Type} (pcm : ExplPCM M) (P Q : SepProp M) :
    ResEquiv (resConj (explToResPCM pcm) P Q) (sepConj pcm P Q) :=
  fun _ => Iff.rfl

theorem toResPCM_wand_iff {M : Type} (pcm : ExplPCM M) (P Q : SepProp M) :
    ResEquiv (resWand (explToResPCM pcm) P Q) (sepWand pcm P Q) :=
  fun _ => Iff.rfl

/-- Constructive persistent agreement carrier (`Once` / `OnceLock` / immutable
shared snapshot knowledge) over `Nat` values. -/
inductive AgreeNat where
  | unit
  | agree (val : Nat)

def agreeNatOp : AgreeNat → AgreeNat → Option AgreeNat
  | .unit, b => some b
  | a, .unit => some a
  | .agree v₁, .agree v₂ =>
    if Nat.beq v₁ v₂ then some (.agree v₁) else none

theorem agreeNatOp_comm (a b : AgreeNat) : agreeNatOp a b = agreeNatOp b a := by
  cases a with
  | unit =>
    cases b with
    | unit => rfl
    | agree _ => rfl
  | agree v₁ =>
    cases b with
    | unit => rfl
    | agree v₂ =>
      dsimp [agreeNatOp]
      cases h₁ : Nat.beq v₁ v₂ with
      | true =>
        have hEq := Nat.eq_of_beq_eq_true h₁
        subst hEq
        rw [Nat.beq_refl]
      | false =>
        cases h₂ : Nat.beq v₂ v₁ with
        | false => rfl
        | true =>
          have hEq := Nat.eq_of_beq_eq_true h₂
          subst hEq
          rw [Nat.beq_refl] at h₁
          cases h₁

theorem agreeNatOp_assoc (a b c : AgreeNat) :
    resOptBind (agreeNatOp a b) (fun ab => agreeNatOp ab c) =
      resOptBind (agreeNatOp b c) (fun bc => agreeNatOp a bc) := by
  cases a with
  | unit =>
    cases b with
    | unit => cases c <;> rfl
    | agree v₁ =>
      cases c with
      | unit => rfl
      | agree v₂ =>
        dsimp [agreeNatOp, resOptBind]
        cases Nat.beq v₁ v₂ <;> rfl
  | agree v₁ =>
    cases b with
    | unit =>
      cases c <;> rfl
    | agree v₂ =>
      cases c with
      | unit =>
        dsimp [agreeNatOp, resOptBind]
        cases Nat.beq v₁ v₂ <;> rfl
      | agree v₃ =>
        dsimp [agreeNatOp, resOptBind]
        cases h₁₂ : Nat.beq v₁ v₂ with
        | true =>
          have e₁₂ := Nat.eq_of_beq_eq_true h₁₂
          subst e₁₂
          dsimp [resOptBind, agreeNatOp]
          cases h₁₃ : Nat.beq v₁ v₃ with
          | true =>
            have e₁₃ := Nat.eq_of_beq_eq_true h₁₃
            subst e₁₃
            dsimp [resOptBind, agreeNatOp]
            rw [Nat.beq_refl]
            rfl
          | false =>
            dsimp [resOptBind]
        | false =>
          dsimp [resOptBind]
          cases h₂₃ : Nat.beq v₂ v₃ with
          | false => rfl
          | true =>
            have e₂₃ := Nat.eq_of_beq_eq_true h₂₃
            subst e₂₃
            dsimp [resOptBind, agreeNatOp]
            rw [h₁₂]
            rfl

def agreeNatResPCM : ResPCM AgreeNat where
  unit := .unit
  op := agreeNatOp
  core := fun a => some a
  op_comm := agreeNatOp_comm
  op_assoc := agreeNatOp_assoc
  unit_left := fun _ => rfl
  core_unit := rfl
  core_id := by
    intro a ca hCore
    injection hCore with hEq
    subst hEq
    cases a with
    | unit => rfl
    | agree v =>
      dsimp [agreeNatOp]
      rw [Nat.beq_refl]
      rfl
  core_idem := by
    intro a ca hCore
    injection hCore with hEq
    subst hEq
    rfl

/-- Non-vacuity witness: `agreeNatResPCM` admits non-unit idempotent elements
and therefore genuinely refutes `ExplPCM`'s cancellativity axiom. -/
theorem agreeNat_refutes_cancellativity :
    agreeNatResPCM.op (.agree 7) (.agree 7) = some (.agree 7) ∧
    agreeNatResPCM.op (.agree 7) .unit = some (.agree 7) ∧
    AgreeNat.agree 7 ≠ AgreeNat.unit := by
  refine ⟨?_, rfl, fun h => nomatch h⟩
  dsimp [agreeNatResPCM, agreeNatOp]

/-- Product of two `ResPCM`s: combines exclusive cancellative ownership
(`explToResPCM byteHeapletPCM`) with persistent non-cancellative agreement
(`agreeNatResPCM`) in one unified resource algebra. -/
def prodResPCM {M₁ M₂ : Type} (r₁ : ResPCM M₁) (r₂ : ResPCM M₂) :
    ResPCM (M₁ × M₂) where
  unit := (r₁.unit, r₂.unit)
  op := fun p q =>
    resOptBind (r₁.op p.1 q.1) (fun x =>
      resOptBind (r₂.op p.2 q.2) (fun y => some (x, y)))
  core := fun p =>
    resOptBind (r₁.core p.1) (fun c₁ =>
      resOptBind (r₂.core p.2) (fun c₂ => some (c₁, c₂)))
  op_comm := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    dsimp [resOptBind]
    rw [r₁.op_comm a₁ b₁, r₂.op_comm a₂ b₂]
  op_assoc := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    have h₁ := r₁.op_assoc a₁ b₁ c₁
    have h₂ := r₂.op_assoc a₂ b₂ c₂
    cases hab₁ : r₁.op a₁ b₁ with
    | none =>
      rw [hab₁] at h₁
      cases hbc₁ : r₁.op b₁ c₁ with
      | none =>
        dsimp [resOptBind]
      | some bc₁ =>
        rw [hbc₁] at h₁
        dsimp [resOptBind] at h₁
        cases hbc₂ : r₂.op b₂ c₂ with
        | none =>
          dsimp [resOptBind]
        | some bc₂ =>
          dsimp [resOptBind]
          rw [← h₁]
    | some ab₁ =>
      rw [hab₁] at h₁
      dsimp [resOptBind] at h₁
      cases hab₂ : r₂.op a₂ b₂ with
      | none =>
        rw [hab₂] at h₂
        cases hbc₁ : r₁.op b₁ c₁ with
        | none =>
          dsimp [resOptBind]
        | some bc₁ =>
          cases hbc₂ : r₂.op b₂ c₂ with
          | none =>
            dsimp [resOptBind]
          | some bc₂ =>
            rw [hbc₂] at h₂
            dsimp [resOptBind] at h₂
            dsimp [resOptBind]
            rw [← h₂]
            cases r₁.op a₁ bc₁ <;> rfl
      | some ab₂ =>
        rw [hab₂] at h₂
        dsimp [resOptBind] at h₂
        cases hbc₁ : r₁.op b₁ c₁ with
        | none =>
          rw [hbc₁] at h₁
          dsimp [resOptBind] at h₁
          dsimp [resOptBind]
          rw [h₁]
        | some bc₁ =>
          rw [hbc₁] at h₁
          dsimp [resOptBind] at h₁
          cases hbc₂ : r₂.op b₂ c₂ with
          | none =>
            rw [hbc₂] at h₂
            dsimp [resOptBind] at h₂
            dsimp [resOptBind]
            rw [h₂]
            cases r₁.op ab₁ c₁ <;> rfl
          | some bc₂ =>
            rw [hbc₂] at h₂
            dsimp [resOptBind] at h₂
            dsimp [resOptBind]
            rw [h₁, h₂]
  unit_left := by
    intro ⟨a₁, a₂⟩
    dsimp [resOptBind]
    rw [r₁.unit_left a₁, r₂.unit_left a₂]
  core_unit := by
    dsimp [resOptBind]
    rw [r₁.core_unit, r₂.core_unit]
  core_id := by
    intro ⟨a₁, a₂⟩ ⟨c₁, c₂⟩ hCore
    dsimp [resOptBind] at hCore
    dsimp [resOptBind]
    cases hc₁ : r₁.core a₁ with
    | none => rw [hc₁] at hCore; cases hCore
    | some x₁ =>
      rw [hc₁] at hCore
      cases hc₂ : r₂.core a₂ with
      | none => rw [hc₂] at hCore; cases hCore
      | some x₂ =>
        rw [hc₂] at hCore
        dsimp [resOptBind] at hCore
        injection hCore with hPair
        injection hPair with e₁ e₂
        subst e₁; subst e₂
        rw [r₁.core_id a₁ x₁ hc₁, r₂.core_id a₂ x₂ hc₂]
  core_idem := by
    intro ⟨a₁, a₂⟩ ⟨c₁, c₂⟩ hCore
    dsimp [resOptBind] at hCore
    dsimp [resOptBind]
    cases hc₁ : r₁.core a₁ with
    | none => rw [hc₁] at hCore; cases hCore
    | some x₁ =>
      rw [hc₁] at hCore
      cases hc₂ : r₂.core a₂ with
      | none => rw [hc₂] at hCore; cases hCore
      | some x₂ =>
        rw [hc₂] at hCore
        dsimp [resOptBind] at hCore
        injection hCore with hPair
        injection hPair with e₁ e₂
        subst e₁; subst e₂
        rw [r₁.core_idem a₁ x₁ hc₁, r₂.core_idem a₂ x₂ hc₂]

/-- Concrete product resource algebra pairing Anneal's live `byteHeapletPCM`
(`ExplPCM ByteHeaplet`) with persistent `agreeNatResPCM`. -/
def heapletWithAgreePCM : ResPCM (ByteHeaplet × AgreeNat) :=
  prodResPCM (explToResPCM byteHeapletPCM) agreeNatResPCM

/-- Non-vacuity witness: persistent agreement duplicates cleanly alongside a
non-empty exclusive `ByteHeaplet` without losing exclusive byte ownership. -/
theorem heaplet_and_persistent_agreement_coexist (bh : ByteHeaplet) (v : Nat) :
    ∃ c : ByteHeaplet × AgreeNat,
      heapletWithAgreePCM.core (bh, AgreeNat.agree v) = some c ∧
      c = (byteHeapletPCM.unit, AgreeNat.agree v) ∧
      heapletWithAgreePCM.op c (bh, AgreeNat.agree v) = some (bh, AgreeNat.agree v) := by
  refine ⟨(byteHeapletPCM.unit, AgreeNat.agree v), rfl, rfl, ?_⟩
  dsimp [heapletWithAgreePCM, prodResPCM, explToResPCM, agreeNatResPCM,
    agreeNatOp, resOptBind]
  rw [byteHeapletPCM.unit_left bh, Nat.beq_refl]
  rfl

end Anneal.ConcurrentSeamsProof
