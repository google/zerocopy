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
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Init.Data.BitVec.BasicAux
import Trusted
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Anneal.Core.StageCut

namespace Anneal.Core

open Trusted.MirAst Trusted.MirSemantics

/-!
# Constructive Partial Commutative Monoids and Byte Heaplets (`Core.SepPCM`)

Provides a constructive, LCNF-computable (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `Quot.sound`) separation algebra core:

1. `ExplPCM M`: Explicit Partial Commutative Monoids with Kleene-associative
   partial composition `op : M → M → Option M` and partial cancellativity.
2. `SepProp M`, `sepEmp`, `sepConj`, `sepWand`, and `FramePreserving`:
   Pointwise separation assertions over `SepEntails`/`SepEquiv` without
   requiring function extensionality (`Quot.sound`), together with full AC,
   unit, magic-wand adjunction, and frame-preservation laws.
3. `SortedAssocMap V`, `ByteHeaplet`, and `MemDisjointFrame`: Canonical
   strictly sorted association lists indexed by `ByteAddr := (AllocId, offset)`
   satisfying `ExplPCM` by list-level structural equality for any value type
   `V`, together with allocation-metadata-preserving footprint framing
   (`ByteFootprint`, `MemDisjointFrame`) directly over `MemoryState`.
4. `SepAtomTree`, `SepExpr`, `AtomBag`, and reflective `SepAC` multiset-frame
   cancellation built on `BoolCertCut` (`O(log N)` Braun atom lookup plus
   `O(log N)` radix-2 multiplicity bag `add`/`cancel`/`beq`, `0`
   `noncomputable`, `hasIR = true`, zero extra axioms).
-/

/-! ## Option Combinators -/

/-- Monadic bind on `Option` (`0` typeclass overhead). -/
def optBind {α β : Type} (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | none => none
  | some a => f a

/-- Left-biased choice on `Option`. -/
def orElseOpt {α : Type} (x y : Option α) : Option α :=
  match x with
  | some a => some a
  | none => y

/-! ## Explicit Partial Commutative Monoid (`ExplPCM`) -/

/-- Constructive Partial Commutative Monoid with partial binary composition
`op : M → M → Option M`, identity `unit`, unconditional Kleene associativity,
and cancellativity. -/
structure ExplPCM (M : Type) where
  unit : M
  op : M → M → Option M
  op_comm : ∀ a b : M, op a b = op b a
  op_assoc : ∀ a b c : M,
    optBind (op a b) (fun ab => op ab c) =
      optBind (op b c) (fun bc => op a bc)
  unit_left : ∀ a : M, op unit a = some a
  cancellative : ∀ a b₁ b₂ c : M,
    op a b₁ = some c → op a b₂ = some c → b₁ = b₂

/-- Right identity law derived from `op_comm` and `unit_left`. -/
theorem ExplPCM.unit_right {M : Type} (pcm : ExplPCM M) (a : M) :
    pcm.op a pcm.unit = some a := by
  rw [pcm.op_comm, pcm.unit_left]

/-- Right cancellativity derived from `op_comm` and `cancellative`. -/
theorem ExplPCM.cancellative_right {M : Type} (pcm : ExplPCM M)
    {a₁ a₂ b c : M} (h₁ : pcm.op a₁ b = some c) (h₂ : pcm.op a₂ b = some c) :
    a₁ = a₂ := by
  rw [pcm.op_comm] at h₁ h₂
  exact pcm.cancellative b a₁ a₂ c h₁ h₂

/-- Forward reassociation `(a • b) • c = abc → ∃ bc, b • c = bc ∧ a • bc = abc`.
-/
theorem ExplPCM.assoc_forward {M : Type} (pcm : ExplPCM M)
    {a b c ab abc : M}
    (hab : pcm.op a b = some ab) (habc : pcm.op ab c = some abc) :
    ∃ bc : M, pcm.op b c = some bc ∧ pcm.op a bc = some abc := by
  have h := pcm.op_assoc a b c
  rw [hab] at h
  dsimp only [optBind] at h
  rw [habc] at h
  cases hbc : pcm.op b c with
  | none =>
    rw [hbc] at h
    cases h
  | some bc =>
    rw [hbc] at h
    exact ⟨bc, rfl, h.symm⟩

/-- Backward reassociation `b • c = bc → a • bc = abc → ∃ ab, a • b = ab ∧
ab • c = abc`. -/
theorem ExplPCM.assoc_backward {M : Type} (pcm : ExplPCM M)
    {a b c bc abc : M}
    (hbc : pcm.op b c = some bc) (habc : pcm.op a bc = some abc) :
    ∃ ab : M, pcm.op a b = some ab ∧ pcm.op ab c = some abc := by
  have h := pcm.op_assoc a b c
  rw [hbc] at h
  dsimp only [optBind] at h
  rw [habc] at h
  cases hab : pcm.op a b with
  | none =>
    rw [hab] at h
    cases h
  | some ab =>
    rw [hab] at h
    exact ⟨ab, rfl, h⟩

/-- Compatibility / disjointness relation `∃ c, pcm.op a b = some c`. -/
def PCMDisjoint {M : Type} (pcm : ExplPCM M) (a b : M) : Prop :=
  ∃ c : M, pcm.op a b = some c

/-- Symmetry of `PCMDisjoint`. -/
theorem PCMDisjoint.symm {M : Type} {pcm : ExplPCM M} {a b : M}
    (h : PCMDisjoint pcm a b) : PCMDisjoint pcm b a := by
  let ⟨c, hc⟩ := h
  rw [pcm.op_comm] at hc
  exact ⟨c, hc⟩

/-! ## Pointwise Separation Logic Assertions (`SepProp`) -/

/-- Predicates over a PCM carrier `M`. -/
abbrev SepProp (M : Type) : Type := M → Prop

/-- Semantic entailment `∀ h, P h → Q h`. -/
def SepEntails {M : Type} (P Q : SepProp M) : Prop :=
  ∀ h : M, P h → Q h

/-- Pointwise logical equivalence `∀ h, P h ↔ Q h` (`0` `funext`). -/
def SepEquiv {M : Type} (P Q : SepProp M) : Prop :=
  ∀ h : M, P h ↔ Q h

/-- Empty-resource assertion `h = pcm.unit`. -/
def sepEmp {M : Type} (pcm : ExplPCM M) : SepProp M :=
  fun h => h = pcm.unit

/-- Pure proposition lifted to `SepProp M` alongside `h = pcm.unit`. -/
def sepPureEmp {M : Type} (pcm : ExplPCM M) (P : Prop) : SepProp M :=
  fun h => P ∧ h = pcm.unit

/-- Separating conjunction `P ∗ Q`. -/
def sepConj {M : Type} (pcm : ExplPCM M) (P Q : SepProp M) : SepProp M :=
  fun h => ∃ h₁ h₂ : M, pcm.op h₁ h₂ = some h ∧ P h₁ ∧ Q h₂

/-- Separating implication (magic wand) `P −∗ Q`. -/
def sepWand {M : Type} (pcm : ExplPCM M) (P Q : SepProp M) : SepProp M :=
  fun h => ∀ h' hCombined : M,
    pcm.op h h' = some hCombined → P h' → Q hCombined

/-- Reflexivity of `SepEntails`. -/
theorem SepEntails.refl {M : Type} (P : SepProp M) : SepEntails P P :=
  fun _ hp => hp

/-- Transitivity of `SepEntails`. -/
theorem SepEntails.trans {M : Type} {P Q R : SepProp M}
    (h₁ : SepEntails P Q) (h₂ : SepEntails Q R) : SepEntails P R :=
  fun h hp => h₂ h (h₁ h hp)

/-- Commutativity `P ∗ Q ↔ Q ∗ P`. -/
theorem sepConj_comm {M : Type} (pcm : ExplPCM M) (P Q : SepProp M) :
    SepEquiv (sepConj pcm P Q) (sepConj pcm Q P) := by
  intro h
  constructor
  · intro hPQ
    let ⟨h₁, h₂, hop, hp, hq⟩ := hPQ
    rw [pcm.op_comm] at hop
    exact ⟨h₂, h₁, hop, hq, hp⟩
  · intro hQP
    let ⟨h₂, h₁, hop, hq, hp⟩ := hQP
    rw [pcm.op_comm] at hop
    exact ⟨h₁, h₂, hop, hp, hq⟩

/-- Associativity `(P ∗ Q) ∗ R ↔ P ∗ (Q ∗ R)`. -/
theorem sepConj_assoc {M : Type} (pcm : ExplPCM M) (P Q R : SepProp M) :
    SepEquiv (sepConj pcm (sepConj pcm P Q) R)
      (sepConj pcm P (sepConj pcm Q R)) := by
  intro h
  constructor
  · intro hL
    let ⟨hpq, hr, hopPQR, hPQ, hR⟩ := hL
    let ⟨hp, hq, hopPQ, hP, hQ⟩ := hPQ
    let ⟨hqr, hopQR, hopP_QR⟩ := pcm.assoc_forward hopPQ hopPQR
    exact ⟨hp, hqr, hopP_QR, hP, ⟨hq, hr, hopQR, hQ, hR⟩⟩
  · intro hR0
    let ⟨hp, hqr, hopP_QR, hP, hQR⟩ := hR0
    let ⟨hq, hr, hopQR, hQ, hR⟩ := hQR
    let ⟨hpq, hopPQ, hopPQ_R⟩ := pcm.assoc_backward hopQR hopP_QR
    exact ⟨hpq, hr, hopPQ_R, ⟨hp, hq, hopPQ, hP, hQ⟩, hR⟩

/-- Left unit law `emp ∗ P ↔ P`. -/
theorem sepConj_emp_left {M : Type} (pcm : ExplPCM M) (P : SepProp M) :
    SepEquiv (sepConj pcm (sepEmp pcm) P) P := by
  intro h
  constructor
  · intro hEP
    let ⟨h₁, h₂, hop, hEmp, hP⟩ := hEP
    unfold sepEmp at hEmp
    subst hEmp
    rw [pcm.unit_left] at hop
    injection hop with hEq
    subst hEq
    exact hP
  · intro hP
    exact ⟨pcm.unit, h, pcm.unit_left h, rfl, hP⟩

/-- Right unit law `P ∗ emp ↔ P`. -/
theorem sepConj_emp_right {M : Type} (pcm : ExplPCM M) (P : SepProp M) :
    SepEquiv (sepConj pcm P (sepEmp pcm)) P := by
  intro h
  exact (sepConj_comm pcm P (sepEmp pcm) h).trans (sepConj_emp_left pcm P h)

/-- Monotonicity of `sepConj` in both arguments. -/
theorem sepConj_mono {M : Type} (pcm : ExplPCM M) {P₁ P₂ Q₁ Q₂ : SepProp M}
    (hP : SepEntails P₁ P₂) (hQ : SepEntails Q₁ Q₂) :
    SepEntails (sepConj pcm P₁ Q₁) (sepConj pcm P₂ Q₂) := by
  intro h h1
  let ⟨ha, hb, hop, hp, hq⟩ := h1
  exact ⟨ha, hb, hop, hP ha hp, hQ hb hq⟩

/-- Magic-wand residuation adjunction `(P ∗ Q ⊢ R) ↔ (P ⊢ Q −∗ R)`. -/
theorem sepWand_adj {M : Type} (pcm : ExplPCM M) (P Q R : SepProp M) :
    SepEntails (sepConj pcm P Q) R ↔ SepEntails P (sepWand pcm Q R) := by
  constructor
  · intro hL hp hP hq hComb hop hQ
    exact hL hComb ⟨hp, hq, hop, hP, hQ⟩
  · intro hR hComb hPQ
    let ⟨hp, hq, hop, hP, hQ⟩ := hPQ
    exact hR hp hP hq hComb hop hQ

/-- Modus ponens for magic wand `(P −∗ Q) ∗ P ⊢ Q`. -/
theorem sepWand_elim {M : Type} (pcm : ExplPCM M) (P Q : SepProp M) :
    SepEntails (sepConj pcm (sepWand pcm P Q) P) Q :=
  (sepWand_adj pcm (sepWand pcm P Q) P Q).mpr (SepEntails.refl _)

/-- Frame-preserving resource update from `P` to `Q` preserving compatibility
with every disjoint frame `hf`. -/
def FramePreserving {M : Type} (pcm : ExplPCM M) (P Q : SepProp M) : Prop :=
  ∀ h₁ hf hCombined : M,
    P h₁ → pcm.op h₁ hf = some hCombined →
    ∃ h₁' hCombined' : M, pcm.op h₁' hf = some hCombined' ∧ Q h₁'

/-- Abstract frame rule: a `FramePreserving` transition from `P` to `Q` lifts
across any invariant frame assertion `F`. -/
theorem FramePreserving.frame {M : Type} {pcm : ExplPCM M}
    {P Q : SepProp M} (F : SepProp M) (hFP : FramePreserving pcm P Q) :
    FramePreserving pcm (sepConj pcm P F) (sepConj pcm Q F) := by
  intro hPF hf hTotal hConj hopTotal
  let ⟨h₁, hF, hopPF, hP, hFProp⟩ := hConj
  let ⟨hFF, hopFF, hop1FF⟩ := pcm.assoc_forward hopPF hopTotal
  let ⟨h₁', hTotal', hop1'FF, hQ⟩ := hFP h₁ hFF hTotal hP hop1FF
  let ⟨hQF, hopQF, hopQF_f⟩ := pcm.assoc_backward hopFF hop1'FF
  exact ⟨hQF, hTotal', hopQF_f, ⟨h₁', hF, hopQF, hQ, hFProp⟩⟩

/-! ## Canonical Strictly Sorted Byte-Address Association Maps -/

/-- Byte address `(allocId, offset)` in `MemoryState`. -/
structure ByteAddr where
  allocId : AllocId
  offset : Nat

/-- Computable equality on `ByteAddr`. -/
def addrBeq (a b : ByteAddr) : Bool :=
  Nat.beq a.allocId b.allocId && Nat.beq a.offset b.offset

/-- Strict lexicographic ordering on `ByteAddr`. -/
def addrLt (a b : ByteAddr) : Bool :=
  Nat.blt a.allocId b.allocId ||
    (Nat.beq a.allocId b.allocId && Nat.blt a.offset b.offset)

/-- Logical characterization of `addrBeq`. -/
theorem addrBeq_iff (a b : ByteAddr) : addrBeq a b = true ↔ a = b := by
  unfold addrBeq
  cases a with
  | mk aId aOff =>
    cases b with
    | mk bId bOff =>
      dsimp only
      constructor
      · intro h
        cases hId : Nat.beq aId bId with
        | false =>
          rw [hId] at h
          cases h
        | true =>
          rw [hId, Bool.true_and] at h
          have e1 := Nat.eq_of_beq_eq_true hId
          have e2 := Nat.eq_of_beq_eq_true h
          subst e1; subst e2
          rfl
      · intro h
        injection h with e1 e2
        subst e1; subst e2
        rw [Nat.beq_refl aId, Nat.beq_refl aOff]
        rfl

private theorem addrBeq_refl (a : ByteAddr) : addrBeq a a = true :=
  (addrBeq_iff a a).mpr rfl

private theorem addrBeq_false_of_ne {a b : ByteAddr} (h : a ≠ b) :
    addrBeq a b = false := by
  cases hb : addrBeq a b with
  | false => rfl
  | true => exact False.elim (h ((addrBeq_iff a b).mp hb))

/-- Logical characterization of `addrLt`. -/
theorem addrLt_iff (a b : ByteAddr) :
    addrLt a b = true ↔
      (a.allocId < b.allocId ∨ (a.allocId = b.allocId ∧ a.offset < b.offset)) := by
  unfold addrLt
  cases h1 : Nat.blt a.allocId b.allocId with
  | true =>
    exact ⟨fun _ => .inl (Nat.ble_eq.mp h1), fun _ => rfl⟩
  | false =>
    have hNotLt1 : ¬ (a.allocId < b.allocId) :=
      fun hlt => by
        have ht : Nat.blt a.allocId b.allocId = true := Nat.ble_eq.mpr hlt
        rw [h1] at ht; cases ht
    cases hEq1 : Nat.beq a.allocId b.allocId with
    | false =>
      have hNe1 : a.allocId ≠ b.allocId :=
        fun he => by
          rw [he, Nat.beq_refl] at hEq1
          cases hEq1
      constructor
      · intro hf; cases hf
      · intro hOr
        cases hOr with
        | inl hlt => exact False.elim (hNotLt1 hlt)
        | inr hand => exact False.elim (hNe1 hand.1)
    | true =>
      have e1 : a.allocId = b.allocId := Nat.eq_of_beq_eq_true hEq1
      constructor
      · intro h2
        rw [Bool.true_and] at h2
        exact .inr ⟨e1, Nat.ble_eq.mp h2⟩
      · intro hOr
        cases hOr with
        | inl hlt => exact False.elim (hNotLt1 hlt)
        | inr hand =>
          rw [Bool.true_and]
          exact Nat.ble_eq.mpr hand.2

/-- Irreflexivity of `addrLt`. -/
theorem addrLt_irrefl (a : ByteAddr) : addrLt a a = false := by
  cases h : addrLt a a with
  | false => rfl
  | true =>
    cases (addrLt_iff a a).mp h with
    | inl h1 => exact False.elim (Nat.lt_irrefl a.allocId h1)
    | inr h2 => exact False.elim (Nat.lt_irrefl a.offset h2.2)

/-- Transitivity of `addrLt`. -/
theorem addrLt_trans {a b c : ByteAddr}
    (hab : addrLt a b = true) (hbc : addrLt b c = true) :
    addrLt a c = true := by
  refine (addrLt_iff a c).mpr ?_
  cases (addrLt_iff a b).mp hab with
  | inl h1 =>
    cases (addrLt_iff b c).mp hbc with
    | inl h2 => exact .inl (Nat.lt_trans h1 h2)
    | inr h2 => rw [← h2.1]; exact .inl h1
  | inr h1 =>
    cases (addrLt_iff b c).mp hbc with
    | inl h2 => rw [h1.1]; exact .inl h2
    | inr h2 =>
      exact .inr ⟨h1.1.trans h2.1, Nat.lt_trans h1.2 h2.2⟩

/-- Strict order implies disequality. -/
theorem addrLt_ne {a b : ByteAddr} (h : addrLt a b = true) : a ≠ b := by
  intro heq
  subst heq
  rw [addrLt_irrefl] at h
  cases h

/-- Asymmetry of `addrLt`. -/
theorem addrLt_asymm {a b : ByteAddr} (h : addrLt a b = true) :
    addrLt b a = false := by
  cases hba : addrLt b a with
  | false => rfl
  | true =>
    have haa := addrLt_trans h hba
    rw [addrLt_irrefl] at haa
    cases haa

/-- Trichotomy of `addrLt` on `ByteAddr`. -/
theorem addrLt_trichotomy (a b : ByteAddr) :
    addrLt a b = true ∨ a = b ∨ addrLt b a = true := by
  cases a with
  | mk aId aOff =>
    cases b with
    | mk bId bOff =>
      cases Nat.lt_or_ge aId bId with
      | inl hlt => exact .inl ((addrLt_iff _ _).mpr (.inl hlt))
      | inr hge =>
        cases Nat.lt_or_ge bId aId with
        | inl hgt => exact .inr (.inr ((addrLt_iff _ _).mpr (.inl hgt)))
        | inr hle =>
          have eId : aId = bId := Nat.le_antisymm hle hge
          subst eId
          cases Nat.lt_or_ge aOff bOff with
          | inl hltO =>
            exact .inl ((addrLt_iff _ _).mpr (.inr ⟨rfl, hltO⟩))
          | inr hgeO =>
            cases Nat.lt_or_ge bOff aOff with
            | inl hgtO =>
              exact .inr (.inr ((addrLt_iff _ _).mpr (.inr ⟨rfl, hgtO⟩)))
            | inr hleO =>
              have eOff : aOff = bOff := Nat.le_antisymm hleO hgeO
              subst eOff
              exact .inr (.inl rfl)

/-- Association-list lookup over `ByteAddr` keys (`0` `noncomputable`). -/
def lookupEntries {V : Type} (xs : List (ByteAddr × V)) (k : ByteAddr) :
    Option V :=
  List.foldr
    (fun (kv : ByteAddr × V) (rest : Option V) =>
      if addrBeq kv.1 k then some kv.2 else rest)
    none
    xs

/-- Strictly ascending lower-bounded key predicate `lo < k₀ < k₁ < ...`. -/
def BoundedEntries {V : Type} (xs : List (ByteAddr × V)) : ByteAddr → Prop :=
  List.foldr
    (fun (kv : ByteAddr × V) (ih : ByteAddr → Prop) (lo : ByteAddr) =>
      addrLt lo kv.1 = true ∧ ih kv.1)
    (fun _ => True)
    xs

/-- Strictly ascending key invariant on `List (ByteAddr × V)`. -/
def IsStrictlySorted {V : Type} (xs : List (ByteAddr × V)) : Prop :=
  match xs with
  | [] => True
  | kv :: tl => BoundedEntries tl kv.1

private theorem boundedEntries_mono {V : Type} {xs : List (ByteAddr × V)}
    {lo₁ lo₂ : ByteAddr} (hLt : addrLt lo₁ lo₂ = true)
    (hB : BoundedEntries xs lo₂) : BoundedEntries xs lo₁ := by
  cases xs with
  | nil => exact True.intro
  | cons kv tl =>
    exact ⟨addrLt_trans hLt hB.1, hB.2⟩

private theorem lookupEntries_none_of_bounded {V : Type}
    {xs : List (ByteAddr × V)} {lo k : ByteAddr}
    (hB : BoundedEntries xs lo) (hLe : k = lo ∨ addrLt k lo = true) :
    lookupEntries xs k = none := by
  induction xs generalizing lo with
  | nil => rfl
  | cons kv tl ih =>
    have hLtK : addrLt k kv.1 = true := by
      cases hLe with
      | inl hEq => subst hEq; exact hB.1
      | inr hLt0 => exact addrLt_trans hLt0 hB.1
    have hBeqF : addrBeq kv.1 k = false :=
      addrBeq_false_of_ne (fun he => addrLt_ne hLtK he.symm)
    change (if addrBeq kv.1 k then some kv.2 else lookupEntries tl k) = none
    rw [hBeqF]
    exact ih hB.2 (.inr hLtK)

/-- Canonical representation theorem: two strictly sorted entry lists with
identical pointwise `lookupEntries` are structurally equal (`=`, `0`
`Quot.sound` / `0` `Classical.choice`). -/
theorem sorted_entries_ext {V : Type} {xs ys : List (ByteAddr × V)}
    (hSx : IsStrictlySorted xs) (hSy : IsStrictlySorted ys)
    (hEq : ∀ k : ByteAddr, lookupEntries xs k = lookupEntries ys k) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons kvy ytl =>
      have hk := hEq kvy.1
      change none = (if addrBeq kvy.1 kvy.1 then some kvy.2
        else lookupEntries ytl kvy.1) at hk
      rw [addrBeq_refl] at hk
      cases hk
  | cons kvx xtl ih =>
    cases ys with
    | nil =>
      have hk := hEq kvx.1
      change (if addrBeq kvx.1 kvx.1 then some kvx.2
        else lookupEntries xtl kvx.1) = none at hk
      rw [addrBeq_refl] at hk
      cases hk
    | cons kvy ytl =>
      cases addrLt_trichotomy kvx.1 kvy.1 with
      | inl hLtXY =>
        have hk := hEq kvx.1
        change (if addrBeq kvx.1 kvx.1 then some kvx.2
          else lookupEntries xtl kvx.1) =
          (if addrBeq kvy.1 kvx.1 then some kvy.2
          else lookupEntries ytl kvx.1) at hk
        have hNeYX : kvy.1 ≠ kvx.1 := fun he => addrLt_ne hLtXY he.symm
        rw [addrBeq_refl, addrBeq_false_of_ne hNeYX] at hk
        rw [lookupEntries_none_of_bounded hSy (.inr hLtXY)] at hk
        cases hk
      | inr hRest =>
        cases hRest with
        | inr hLtYX =>
          have hk := hEq kvy.1
          change (if addrBeq kvx.1 kvy.1 then some kvx.2
            else lookupEntries xtl kvy.1) =
            (if addrBeq kvy.1 kvy.1 then some kvy.2
            else lookupEntries ytl kvy.1) at hk
          have hNeXY : kvx.1 ≠ kvy.1 := fun he => addrLt_ne hLtYX he.symm
          rw [addrBeq_false_of_ne hNeXY, addrBeq_refl] at hk
          rw [lookupEntries_none_of_bounded hSx (.inr hLtYX)] at hk
          cases hk
        | inl hKeyEq =>
          have hk := hEq kvx.1
          change (if addrBeq kvx.1 kvx.1 then some kvx.2
            else lookupEntries xtl kvx.1) =
            (if addrBeq kvy.1 kvx.1 then some kvy.2
            else lookupEntries ytl kvx.1) at hk
          cases kvx with
          | mk kx vx =>
            cases kvy with
            | mk ky vy =>
              dsimp only at hKeyEq
              subst hKeyEq
              rw [addrBeq_refl] at hk
              injection hk with hValEq
              subst hValEq
              have hTailEq : ∀ k : ByteAddr,
                  lookupEntries xtl k = lookupEntries ytl k := by
                intro k
                cases hb : addrBeq kx k with
                | true =>
                  have he : kx = k := (addrBeq_iff kx k).mp hb
                  subst he
                  rw [lookupEntries_none_of_bounded hSx (.inl rfl),
                    lookupEntries_none_of_bounded hSy (.inl rfl)]
                | false =>
                  have hkc := hEq k
                  change (if addrBeq kx k then some vx
                    else lookupEntries xtl k) =
                    (if addrBeq kx k then some vx
                    else lookupEntries ytl k) at hkc
                  rw [hb] at hkc
                  exact hkc
              have hSx' : IsStrictlySorted xtl := by
                cases xtl with
                | nil => exact True.intro
                | cons _ _ => exact hSx.2
              have hSy' : IsStrictlySorted ytl := by
                cases ytl with
                | nil => exact True.intro
                | cons _ _ => exact hSy.2
              exact congrArg (List.cons (kx, vx)) (ih hSx' hSy' hTailEq)

/-! ## Disjoint Linear-Time Merge via Fuel-Bounded `@Nat.rec` -/

private def mergeDisjointFuel {V : Type} (fuel : Nat) :
    List (ByteAddr × V) → List (ByteAddr × V) → Option (List (ByteAddr × V)) :=
  @Nat.rec
    (fun _ =>
      List (ByteAddr × V) → List (ByteAddr × V) → Option (List (ByteAddr × V)))
    (fun _ _ => none)
    (fun _ go xs ys =>
      match xs with
      | [] => some ys
      | kvx :: xtl =>
        match ys with
        | [] => some (kvx :: xtl)
        | kvy :: ytl =>
          if addrLt kvx.1 kvy.1 then
            match go xtl (kvy :: ytl) with
            | some r => some (kvx :: r)
            | none => none
          else if addrLt kvy.1 kvx.1 then
            match go (kvx :: xtl) ytl with
            | some r => some (kvy :: r)
            | none => none
          else
            none)
    fuel

private theorem mergeDisjointFuel_eq {V : Type} :
    ∀ {f₁ f₂ : Nat} (xs ys : List (ByteAddr × V)),
      xs.length + ys.length < f₁ →
      xs.length + ys.length < f₂ →
      mergeDisjointFuel f₁ xs ys = mergeDisjointFuel f₂ xs ys
  | 0, _, _, _, h₁, _ => False.elim (Nat.not_lt_zero _ h₁)
  | _ + 1, 0, _, _, _, h₂ => False.elim (Nat.not_lt_zero _ h₂)
  | f₁ + 1, f₂ + 1, [], ys, _, _ => rfl
  | f₁ + 1, f₂ + 1, kvx :: xtl, [], _, _ => rfl
  | f₁ + 1, f₂ + 1, kvx :: xtl, kvy :: ytl, h₁, h₂ => by
    have hSubX₁ : xtl.length + (kvy :: ytl).length < f₁ := by
      have hEq : (kvx :: xtl).length + (kvy :: ytl).length =
          (xtl.length + (kvy :: ytl).length) + 1 := by
        change (xtl.length + 1) + (ytl.length + 1) =
          (xtl.length + (ytl.length + 1)) + 1
        rw [Nat.add_assoc, Nat.add_comm 1 (ytl.length + 1), ← Nat.add_assoc]
      rw [hEq] at h₁
      exact Nat.lt_of_succ_lt_succ h₁
    have hSubX₂ : xtl.length + (kvy :: ytl).length < f₂ := by
      have hEq : (kvx :: xtl).length + (kvy :: ytl).length =
          (xtl.length + (kvy :: ytl).length) + 1 := by
        change (xtl.length + 1) + (ytl.length + 1) =
          (xtl.length + (ytl.length + 1)) + 1
        rw [Nat.add_assoc, Nat.add_comm 1 (ytl.length + 1), ← Nat.add_assoc]
      rw [hEq] at h₂
      exact Nat.lt_of_succ_lt_succ h₂
    have hSubY₁ : (kvx :: xtl).length + ytl.length < f₁ :=
      Nat.lt_of_succ_lt_succ h₁
    have hSubY₂ : (kvx :: xtl).length + ytl.length < f₂ :=
      Nat.lt_of_succ_lt_succ h₂
    change (if addrLt kvx.1 kvy.1 then
        match mergeDisjointFuel f₁ xtl (kvy :: ytl) with
        | some r => some (kvx :: r)
        | none => none
      else if addrLt kvy.1 kvx.1 then
        match mergeDisjointFuel f₁ (kvx :: xtl) ytl with
        | some r => some (kvy :: r)
        | none => none
      else none) =
      (if addrLt kvx.1 kvy.1 then
        match mergeDisjointFuel f₂ xtl (kvy :: ytl) with
        | some r => some (kvx :: r)
        | none => none
      else if addrLt kvy.1 kvx.1 then
        match mergeDisjointFuel f₂ (kvx :: xtl) ytl with
        | some r => some (kvy :: r)
        | none => none
      else none)
    rw [mergeDisjointFuel_eq xtl (kvy :: ytl) hSubX₁ hSubX₂,
      mergeDisjointFuel_eq (kvx :: xtl) ytl hSubY₁ hSubY₂]

/-- Merges two strictly sorted `ByteAddr` entry lists in linear `O(|xs| + |ys|)`
time (in both LCNF and WHNF), returning `none` on any key collision (`0`
`noncomputable`, `0` `._unsafe_rec`). -/
def mergeDisjointEntries {V : Type} (xs ys : List (ByteAddr × V)) :
    Option (List (ByteAddr × V)) :=
  mergeDisjointFuel (xs.length + ys.length + 1) xs ys

private theorem mergeDisjointEntries_nil_left {V : Type}
    (ys : List (ByteAddr × V)) :
    mergeDisjointEntries [] ys = some ys := by
  unfold mergeDisjointEntries
  change mergeDisjointFuel (0 + ys.length + 1) [] ys = some ys
  rw [Nat.zero_add]
  rfl

private theorem mergeDisjointEntries_nil_right {V : Type}
    (kvx : ByteAddr × V) (xtl : List (ByteAddr × V)) :
    mergeDisjointEntries (kvx :: xtl) [] = some (kvx :: xtl) := rfl

private theorem mergeDisjointEntries_cons_cons {V : Type}
    (kvx kvy : ByteAddr × V) (xtl ytl : List (ByteAddr × V)) :
    mergeDisjointEntries (kvx :: xtl) (kvy :: ytl) =
      if addrLt kvx.1 kvy.1 then
        match mergeDisjointEntries xtl (kvy :: ytl) with
        | some r => some (kvx :: r)
        | none => none
      else if addrLt kvy.1 kvx.1 then
        match mergeDisjointEntries (kvx :: xtl) ytl with
        | some r => some (kvy :: r)
        | none => none
      else
        none := by
  have hStep :
      mergeDisjointEntries (kvx :: xtl) (kvy :: ytl) =
        if addrLt kvx.1 kvy.1 then
          match mergeDisjointFuel ((kvx :: xtl).length + (kvy :: ytl).length)
              xtl (kvy :: ytl) with
          | some r => some (kvx :: r)
          | none => none
        else if addrLt kvy.1 kvx.1 then
          match mergeDisjointFuel ((kvx :: xtl).length + (kvy :: ytl).length)
              (kvx :: xtl) ytl with
          | some r => some (kvy :: r)
          | none => none
        else none := rfl
  have hLtX :
      xtl.length + (kvy :: ytl).length <
        (kvx :: xtl).length + (kvy :: ytl).length := by
    change xtl.length + (ytl.length + 1) < (xtl.length + 1) + (ytl.length + 1)
    rw [Nat.add_assoc xtl.length 1 (ytl.length + 1),
      Nat.add_comm 1 (ytl.length + 1), ← Nat.add_assoc]
    exact Nat.lt_succ_self _
  have hLtY :
      (kvx :: xtl).length + ytl.length <
        (kvx :: xtl).length + (kvy :: ytl).length :=
    Nat.lt_succ_self _
  have hEqX :
      mergeDisjointFuel ((kvx :: xtl).length + (kvy :: ytl).length)
        xtl (kvy :: ytl) = mergeDisjointEntries xtl (kvy :: ytl) :=
    mergeDisjointFuel_eq xtl (kvy :: ytl) hLtX (Nat.lt_succ_self _)
  have hEqY :
      mergeDisjointFuel ((kvx :: xtl).length + (kvy :: ytl).length)
        (kvx :: xtl) ytl = mergeDisjointEntries (kvx :: xtl) ytl :=
    mergeDisjointFuel_eq (kvx :: xtl) ytl hLtY (Nat.lt_succ_self _)
  rw [hStep, hEqX, hEqY]

private theorem mergeDisjointEntries_bounded {V : Type}
    (xs : List (ByteAddr × V)) :
    ∀ (ys zs : List (ByteAddr × V)) (lo : ByteAddr),
      BoundedEntries xs lo → BoundedEntries ys lo →
      mergeDisjointEntries xs ys = some zs →
      BoundedEntries zs lo := by
  induction xs with
  | nil =>
    intro ys zs lo _ hBy hM
    injection hM with hEq
    subst hEq
    exact hBy
  | cons kvx xtl ihX =>
    intro ys
    induction ys with
    | nil =>
      intro zs lo hBx _ hM
      rw [mergeDisjointEntries_nil_right] at hM
      injection hM with hEq
      subst hEq
      exact hBx
    | cons kvy ytl ihY =>
      intro zs lo hBx hBy hM
      rw [mergeDisjointEntries_cons_cons] at hM
      cases hXY : addrLt kvx.1 kvy.1 with
      | true =>
        rw [hXY] at hM
        cases hSub : mergeDisjointEntries xtl (kvy :: ytl) with
        | none => rw [hSub] at hM; cases hM
        | some r =>
          rw [hSub] at hM
          injection hM with hEq
          subst hEq
          exact ⟨hBx.1, ihX (kvy :: ytl) r kvx.1 hBx.2 ⟨hXY, hBy.2⟩ hSub⟩
      | false =>
        rw [hXY] at hM
        cases hYX : addrLt kvy.1 kvx.1 with
        | false => rw [hYX] at hM; cases hM
        | true =>
          rw [hYX] at hM
          cases hSub : mergeDisjointEntries (kvx :: xtl) ytl with
          | none => rw [hSub] at hM; cases hM
          | some r =>
            rw [hSub] at hM
            injection hM with hEq
            subst hEq
            exact ⟨hBy.1, ihY r kvy.1 ⟨hYX, hBx.2⟩ hBy.2 hSub⟩

/-- `mergeDisjointEntries` preserves `IsStrictlySorted`. -/
theorem mergeDisjointEntries_sorted {V : Type}
    {xs ys zs : List (ByteAddr × V)}
    (hSx : IsStrictlySorted xs) (hSy : IsStrictlySorted ys)
    (hM : mergeDisjointEntries xs ys = some zs) :
    IsStrictlySorted zs := by
  cases xs with
  | nil =>
    injection hM with hEq
    subst hEq
    exact hSy
  | cons kvx xtl =>
    cases ys with
    | nil =>
      rw [mergeDisjointEntries_nil_right] at hM
      injection hM with hEq
      subst hEq
      exact hSx
    | cons kvy ytl =>
      rw [mergeDisjointEntries_cons_cons] at hM
      cases hXY : addrLt kvx.1 kvy.1 with
      | true =>
        rw [hXY] at hM
        cases hSub : mergeDisjointEntries xtl (kvy :: ytl) with
        | none => rw [hSub] at hM; cases hM
        | some r =>
          rw [hSub] at hM
          injection hM with hEq
          subst hEq
          exact mergeDisjointEntries_bounded xtl (kvy :: ytl) r kvx.1
            hSx ⟨hXY, hSy⟩ hSub
      | false =>
        rw [hXY] at hM
        cases hYX : addrLt kvy.1 kvx.1 with
        | false => rw [hYX] at hM; cases hM
        | true =>
          rw [hYX] at hM
          cases hSub : mergeDisjointEntries (kvx :: xtl) ytl with
          | none => rw [hSub] at hM; cases hM
          | some r =>
            rw [hSub] at hM
            injection hM with hEq
            subst hEq
            exact mergeDisjointEntries_bounded (kvx :: xtl) ytl r kvy.1
              ⟨hYX, hSx⟩ hSy hSub

/-- Pointwise key-disjointness of two association lists. -/
def DisjointEntries {V : Type} (xs ys : List (ByteAddr × V)) : Prop :=
  ∀ k : ByteAddr, lookupEntries xs k = none ∨ lookupEntries ys k = none

private theorem mergeDisjointEntries_sound {V : Type}
    (xs : List (ByteAddr × V)) :
    ∀ (ys zs : List (ByteAddr × V)),
      IsStrictlySorted xs → IsStrictlySorted ys →
      mergeDisjointEntries xs ys = some zs →
      DisjointEntries xs ys ∧
      ∀ k : ByteAddr,
        lookupEntries zs k = orElseOpt (lookupEntries xs k) (lookupEntries ys k) := by
  induction xs with
  | nil =>
    intro ys zs _ _ hM
    injection hM with hEq
    subst hEq
    exact ⟨fun _ => .inl rfl, fun _ => rfl⟩
  | cons kvx xtl ihX =>
    intro ys
    induction ys with
    | nil =>
      intro zs _ _ hM
      rw [mergeDisjointEntries_nil_right] at hM
      injection hM with hEq
      subst hEq
      refine ⟨fun _ => .inr rfl, fun k => ?_⟩
      cases lookupEntries (kvx :: xtl) k <;> rfl
    | cons kvy ytl ihY =>
      intro zs hSx hSy hM
      rw [mergeDisjointEntries_cons_cons] at hM
      have hSx' : IsStrictlySorted xtl := by
        cases xtl with
        | nil => exact True.intro
        | cons _ _ => exact hSx.2
      have hSy' : IsStrictlySorted ytl := by
        cases ytl with
        | nil => exact True.intro
        | cons _ _ => exact hSy.2
      cases hXY : addrLt kvx.1 kvy.1 with
      | true =>
        rw [hXY] at hM
        cases hSub : mergeDisjointEntries xtl (kvy :: ytl) with
        | none => rw [hSub] at hM; cases hM
        | some r =>
          rw [hSub] at hM
          injection hM with hEq
          subst hEq
          have hSubSpec := ihX (kvy :: ytl) r hSx' hSy hSub
          have hNoneYAtX : lookupEntries (kvy :: ytl) kvx.1 = none := by
            have hNe : kvy.1 ≠ kvx.1 := fun he => addrLt_ne hXY he.symm
            change (if addrBeq kvy.1 kvx.1 then some kvy.2
              else lookupEntries ytl kvx.1) = none
            rw [addrBeq_false_of_ne hNe]
            exact lookupEntries_none_of_bounded hSy (.inr hXY)
          refine ⟨fun k => ?_, fun k => ?_⟩
          · cases hb : addrBeq kvx.1 k with
            | true =>
              have he : kvx.1 = k := (addrBeq_iff kvx.1 k).mp hb
              subst he
              exact .inr hNoneYAtX
            | false =>
              change (if addrBeq kvx.1 k then some kvx.2
                else lookupEntries xtl k) = none ∨ _
              rw [hb]
              exact hSubSpec.1 k
          · change (if addrBeq kvx.1 k then some kvx.2 else lookupEntries r k) =
              orElseOpt (if addrBeq kvx.1 k then some kvx.2
                else lookupEntries xtl k)
                (lookupEntries (kvy :: ytl) k)
            cases hb : addrBeq kvx.1 k with
            | true => rfl
            | false => exact hSubSpec.2 k
      | false =>
        rw [hXY] at hM
        cases hYX : addrLt kvy.1 kvx.1 with
        | false => rw [hYX] at hM; cases hM
        | true =>
          rw [hYX] at hM
          cases hSub : mergeDisjointEntries (kvx :: xtl) ytl with
          | none => rw [hSub] at hM; cases hM
          | some r =>
            rw [hSub] at hM
            injection hM with hEq
            subst hEq
            have hSubSpec := ihY r hSx hSy' hSub
            have hNoneXAtY : lookupEntries (kvx :: xtl) kvy.1 = none := by
              have hNe : kvx.1 ≠ kvy.1 := fun he => addrLt_ne hYX he.symm
              change (if addrBeq kvx.1 kvy.1 then some kvx.2
                else lookupEntries xtl kvy.1) = none
              rw [addrBeq_false_of_ne hNe]
              exact lookupEntries_none_of_bounded hSx (.inr hYX)
            refine ⟨fun k => ?_, fun k => ?_⟩
            · cases hb : addrBeq kvy.1 k with
              | true =>
                have he : kvy.1 = k := (addrBeq_iff kvy.1 k).mp hb
                subst he
                exact .inl hNoneXAtY
              | false =>
                change _ ∨ (if addrBeq kvy.1 k then some kvy.2
                  else lookupEntries ytl k) = none
                rw [hb]
                exact hSubSpec.1 k
            · change (if addrBeq kvy.1 k then some kvy.2 else lookupEntries r k) =
                orElseOpt (lookupEntries (kvx :: xtl) k)
                  (if addrBeq kvy.1 k then some kvy.2 else lookupEntries ytl k)
              cases hb : addrBeq kvy.1 k with
              | true =>
                have he : kvy.1 = k := (addrBeq_iff kvy.1 k).mp hb
                subst he
                rw [hNoneXAtY]
                rfl
              | false => exact hSubSpec.2 k

private theorem mergeDisjointEntries_complete {V : Type}
    (xs : List (ByteAddr × V)) :
    ∀ (ys : List (ByteAddr × V)),
      IsStrictlySorted xs → IsStrictlySorted ys →
      DisjointEntries xs ys →
      ∃ zs : List (ByteAddr × V), mergeDisjointEntries xs ys = some zs := by
  induction xs with
  | nil =>
    intro ys _ _ _
    exact ⟨ys, rfl⟩
  | cons kvx xtl ihX =>
    intro ys
    induction ys with
    | nil =>
      intro _ _ _
      exact ⟨kvx :: xtl, mergeDisjointEntries_nil_right kvx xtl⟩
    | cons kvy ytl ihY =>
      intro hSx hSy hDisj
      have hSx' : IsStrictlySorted xtl := by
        cases xtl with
        | nil => exact True.intro
        | cons _ _ => exact hSx.2
      have hSy' : IsStrictlySorted ytl := by
        cases ytl with
        | nil => exact True.intro
        | cons _ _ => exact hSy.2
      rw [mergeDisjointEntries_cons_cons]
      cases addrLt_trichotomy kvx.1 kvy.1 with
      | inl hXY =>
        rw [hXY]
        have hDisjSub : DisjointEntries xtl (kvy :: ytl) := by
          intro k
          cases hb : addrBeq kvx.1 k with
          | true =>
            have he : kvx.1 = k := (addrBeq_iff kvx.1 k).mp hb
            subst he
            exact .inl (lookupEntries_none_of_bounded hSx (.inl rfl))
          | false =>
            have hd := hDisj k
            change (if addrBeq kvx.1 k then some kvx.2
              else lookupEntries xtl k) = none ∨ _ at hd
            rw [hb] at hd
            exact hd
        let ⟨r, hr⟩ := ihX (kvy :: ytl) hSx' hSy hDisjSub
        rw [hr]
        exact ⟨kvx :: r, rfl⟩
      | inr hRest =>
        cases hRest with
        | inl hEq =>
          have hd := hDisj kvx.1
          change (if addrBeq kvx.1 kvx.1 then some kvx.2
            else lookupEntries xtl kvx.1) = none ∨
            (if addrBeq kvy.1 kvx.1 then some kvy.2
            else lookupEntries ytl kvx.1) = none at hd
          rw [← hEq, addrBeq_refl] at hd
          cases hd with
          | inl hN => cases hN
          | inr hN => cases hN
        | inr hYX =>
          rw [addrLt_asymm hYX, hYX]
          have hDisjSub : DisjointEntries (kvx :: xtl) ytl := by
            intro k
            cases hb : addrBeq kvy.1 k with
            | true =>
              have he : kvy.1 = k := (addrBeq_iff kvy.1 k).mp hb
              subst he
              exact .inr (lookupEntries_none_of_bounded hSy (.inl rfl))
            | false =>
              have hd := hDisj k
              change _ ∨ (if addrBeq kvy.1 k then some kvy.2
                else lookupEntries ytl k) = none at hd
              rw [hb] at hd
              exact hd
          let ⟨r, hr⟩ := ihY hSx hSy' hDisjSub
          rw [hr]
          exact ⟨kvy :: r, rfl⟩

/-! ## `SortedAssocMap V` and `ByteHeaplet` PCM Instances -/

/-- Boolean strictly-ascending lower-bounded key check (`0` `noncomputable`). -/
def boundedEntriesBool {V : Type} (xs : List (ByteAddr × V)) :
    ByteAddr → Bool :=
  List.foldr
    (fun (kv : ByteAddr × V) (ih : ByteAddr → Bool) (lo : ByteAddr) =>
      addrLt lo kv.1 && ih kv.1)
    (fun _ => true)
    xs

private theorem boundedEntriesBool_iff {V : Type}
    (xs : List (ByteAddr × V)) (lo : ByteAddr) :
    boundedEntriesBool xs lo = true ↔ BoundedEntries xs lo := by
  induction xs generalizing lo with
  | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | cons kv tl ih =>
    change (addrLt lo kv.1 && boundedEntriesBool tl kv.1) = true ↔
      (addrLt lo kv.1 = true ∧ BoundedEntries tl kv.1)
    cases hLt : addrLt lo kv.1 with
    | false =>
      constructor
      · intro hf; rw [Bool.false_and] at hf; cases hf
      · intro h; cases h.1
    | true =>
      rw [Bool.true_and]
      exact ⟨fun hb => ⟨rfl, (ih kv.1).mp hb⟩,
             fun h => (ih kv.1).mpr h.2⟩

/-- Boolean strictly-ascending key check (`0` `noncomputable`). -/
def isStrictlySortedBool {V : Type} (xs : List (ByteAddr × V)) : Bool :=
  match xs with
  | [] => true
  | kv :: tl => boundedEntriesBool tl kv.1

private theorem isStrictlySortedBool_iff {V : Type}
    (xs : List (ByteAddr × V)) :
    isStrictlySortedBool xs = true ↔ IsStrictlySorted xs := by
  cases xs with
  | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | cons kv tl => exact boundedEntriesBool_iff tl kv.1

/-- Canonical strictly sorted map over `ByteAddr` keys (`0` `noncomputable`). -/
structure SortedAssocMap (V : Type) where
  entries : List (ByteAddr × V)
  sorted : IsStrictlySorted entries

private theorem sortedAssocMap_ext {V : Type} {a b : SortedAssocMap V}
    (h : a.entries = b.entries) : a = b := by
  cases a with
  | mk ea sa =>
    cases b with
    | mk eb sb =>
      dsimp only at h
      subst h
      rfl

/-- Empty `SortedAssocMap V`. -/
def SortedAssocMap.empty (V : Type) : SortedAssocMap V :=
  { entries := [], sorted := True.intro }

/-- Singleton `SortedAssocMap V` at `addr`. -/
def SortedAssocMap.singleton {V : Type} (addr : ByteAddr) (val : V) :
    SortedAssocMap V :=
  { entries := [(addr, val)], sorted := True.intro }

/-- Key lookup on `SortedAssocMap V`. -/
def SortedAssocMap.lookup {V : Type} (m : SortedAssocMap V) (addr : ByteAddr) :
    Option V :=
  lookupEntries m.entries addr

private def mkSortedFromFlag {V : Type} (zs : List (ByteAddr × V)) :
    ∀ b : Bool, (isStrictlySortedBool zs = b) → Option (SortedAssocMap V)
  | true, h => some ⟨zs, (isStrictlySortedBool_iff zs).mp h⟩
  | false, _ => none

private def mkSortedAssocMap? {V : Type}
    (opt : Option (List (ByteAddr × V))) : Option (SortedAssocMap V) :=
  match opt with
  | none => none
  | some zs => mkSortedFromFlag zs (isStrictlySortedBool zs) rfl

private theorem mkSortedAssocMap?_none {V : Type} :
    (@mkSortedAssocMap? V none) = none := rfl

private theorem mkSortedFromFlag_true {V : Type} (zs : List (ByteAddr × V))
    (hs : IsStrictlySorted zs) :
    ∀ (flag : Bool) (hEq : isStrictlySortedBool zs = flag),
      flag = true →
      mkSortedFromFlag zs flag hEq = some ⟨zs, hs⟩
  | true, _, _ => congrArg some (sortedAssocMap_ext rfl)
  | false, _, h => by cases h

private theorem mkSortedAssocMap?_some {V : Type}
    {zs : List (ByteAddr × V)} (hs : IsStrictlySorted zs) :
    mkSortedAssocMap? (some zs) = some ⟨zs, hs⟩ :=
  mkSortedFromFlag_true zs hs (isStrictlySortedBool zs) rfl
    ((isStrictlySortedBool_iff zs).mpr hs)

/-- Disjoint merge on `SortedAssocMap V` (`0` `noncomputable`). -/
def SortedAssocMap.merge {V : Type} (a b : SortedAssocMap V) :
    Option (SortedAssocMap V) :=
  mkSortedAssocMap? (mergeDisjointEntries a.entries b.entries)

private theorem orElseOpt_comm_of_disjoint {V : Type} (x y : Option V)
    (h : x = none ∨ y = none) : orElseOpt x y = orElseOpt y x := by
  cases h with
  | inl hx => rw [hx]; cases y <;> rfl
  | inr hy => rw [hy]; cases x <;> rfl

private theorem orElseOpt_assoc {V : Type} (x y z : Option V) :
    orElseOpt (orElseOpt x y) z = orElseOpt x (orElseOpt y z) := by
  cases x <;> rfl

/-- Constructive `ExplPCM` instance on `SortedAssocMap V` (`propext`-only; `0`
`Quot.sound`, `0` `Classical.choice`). -/
def sortedAssocPCM (V : Type) : ExplPCM (SortedAssocMap V) where
  unit := SortedAssocMap.empty V
  op := SortedAssocMap.merge
  op_comm := fun a b => by
    unfold SortedAssocMap.merge
    cases hAB : mergeDisjointEntries a.entries b.entries with
    | none =>
      cases hBA : mergeDisjointEntries b.entries a.entries with
      | none => rfl
      | some zsBA =>
        have hS := mergeDisjointEntries_sound b.entries a.entries zsBA
          b.sorted a.sorted hBA
        have hDisjAB : DisjointEntries a.entries b.entries :=
          fun k => (hS.1 k).symm
        let ⟨_, hEx⟩ :=
          mergeDisjointEntries_complete a.entries b.entries a.sorted b.sorted hDisjAB
        rw [hAB] at hEx
        cases hEx
    | some zsAB =>
      have hS := mergeDisjointEntries_sound a.entries b.entries zsAB
        a.sorted b.sorted hAB
      have hDisjBA : DisjointEntries b.entries a.entries :=
        fun k => (hS.1 k).symm
      let ⟨zsBA, hBA⟩ :=
        mergeDisjointEntries_complete b.entries a.entries b.sorted a.sorted hDisjBA
      rw [hBA]
      have hS2 := mergeDisjointEntries_sound b.entries a.entries zsBA
        b.sorted a.sorted hBA
      have sAB := mergeDisjointEntries_sorted a.sorted b.sorted hAB
      have sBA := mergeDisjointEntries_sorted b.sorted a.sorted hBA
      have hEqEntries : zsAB = zsBA :=
        sorted_entries_ext sAB sBA (fun k => by
          rw [hS.2 k, hS2.2 k]
          exact orElseOpt_comm_of_disjoint _ _ (hS.1 k))
      rw [mkSortedAssocMap?_some sAB, mkSortedAssocMap?_some sBA]
      exact congrArg some (sortedAssocMap_ext hEqEntries)
  op_assoc := fun a b c => by
    unfold SortedAssocMap.merge
    cases hAB : mergeDisjointEntries a.entries b.entries with
    | none =>
      rw [mkSortedAssocMap?_none]
      dsimp only [optBind]
      cases hBC : mergeDisjointEntries b.entries c.entries with
      | none => rfl
      | some zsBC =>
        have sBC := mergeDisjointEntries_sorted b.sorted c.sorted hBC
        rw [mkSortedAssocMap?_some sBC]
        dsimp only [optBind]
        cases hA_BC : mergeDisjointEntries a.entries zsBC with
        | none => rfl
        | some zsABC =>
          have spBC := mergeDisjointEntries_sound b.entries c.entries zsBC
            b.sorted c.sorted hBC
          have spABC := mergeDisjointEntries_sound a.entries zsBC zsABC
            a.sorted sBC hA_BC
          have hDisjAB : DisjointEntries a.entries b.entries := by
            intro k
            cases spABC.1 k with
            | inl ha => exact .inl ha
            | inr hbcNone =>
              rw [spBC.2 k] at hbcNone
              cases hb : lookupEntries b.entries k with
              | none => exact .inr rfl
              | some _ => rw [hb] at hbcNone; cases hbcNone
          let ⟨_, hEx⟩ :=
            mergeDisjointEntries_complete a.entries b.entries a.sorted b.sorted hDisjAB
          rw [hAB] at hEx
          cases hEx
    | some zsAB =>
      have sAB := mergeDisjointEntries_sorted a.sorted b.sorted hAB
      have spAB := mergeDisjointEntries_sound a.entries b.entries zsAB
        a.sorted b.sorted hAB
      rw [mkSortedAssocMap?_some sAB]
      dsimp only [optBind]
      cases hAB_C : mergeDisjointEntries zsAB c.entries with
      | none =>
        rw [mkSortedAssocMap?_none]
        cases hBC : mergeDisjointEntries b.entries c.entries with
        | none => rfl
        | some zsBC =>
          have sBC := mergeDisjointEntries_sorted b.sorted c.sorted hBC
          rw [mkSortedAssocMap?_some sBC]
          dsimp only [optBind]
          cases hA_BC : mergeDisjointEntries a.entries zsBC with
          | none => rfl
          | some zsABC =>
            have spBC := mergeDisjointEntries_sound b.entries c.entries zsBC
              b.sorted c.sorted hBC
            have spABC := mergeDisjointEntries_sound a.entries zsBC zsABC
              a.sorted sBC hA_BC
            have hDisjAB_C : DisjointEntries zsAB c.entries := by
              intro k
              rw [spAB.2 k]
              cases hc : lookupEntries c.entries k with
              | none => exact .inr rfl
              | some vc =>
                have hNoneB : lookupEntries b.entries k = none := by
                  cases spBC.1 k with
                  | inl hb0 => exact hb0
                  | inr hc0 => rw [hc] at hc0; cases hc0
                have hSomeBC : lookupEntries zsBC k = some vc := by
                  rw [spBC.2 k, hNoneB, hc]; rfl
                have hNoneA : lookupEntries a.entries k = none := by
                  cases spABC.1 k with
                  | inl ha0 => exact ha0
                  | inr hbc0 => rw [hSomeBC] at hbc0; cases hbc0
                rw [hNoneA, hNoneB]
                exact .inl rfl
            let ⟨_, hEx⟩ :=
              mergeDisjointEntries_complete zsAB c.entries sAB c.sorted hDisjAB_C
            rw [hAB_C] at hEx
            cases hEx
      | some zsABC1 =>
        have sABC1 := mergeDisjointEntries_sorted sAB c.sorted hAB_C
        have spABC1 := mergeDisjointEntries_sound zsAB c.entries zsABC1
          sAB c.sorted hAB_C
        rw [mkSortedAssocMap?_some sABC1]
        have hDisjBC : DisjointEntries b.entries c.entries := by
          intro k
          cases spABC1.1 k with
          | inr hc0 => exact .inr hc0
          | inl hab0 =>
            rw [spAB.2 k] at hab0
            cases ha : lookupEntries a.entries k with
            | some _ => rw [ha] at hab0; cases hab0
            | none =>
              rw [ha] at hab0
              exact .inl hab0
        let ⟨zsBC, hBC⟩ :=
          mergeDisjointEntries_complete b.entries c.entries b.sorted c.sorted hDisjBC
        have sBC := mergeDisjointEntries_sorted b.sorted c.sorted hBC
        have spBC := mergeDisjointEntries_sound b.entries c.entries zsBC
          b.sorted c.sorted hBC
        rw [hBC, mkSortedAssocMap?_some sBC]
        dsimp only [optBind]
        have hDisjA_BC : DisjointEntries a.entries zsBC := by
          intro k
          cases ha : lookupEntries a.entries k with
          | none => exact .inl rfl
          | some va =>
            have hNoneB : lookupEntries b.entries k = none := by
              cases spAB.1 k with
              | inl ha0 => rw [ha] at ha0; cases ha0
              | inr hb0 => exact hb0
            have hSomeAB : lookupEntries zsAB k = some va := by
              rw [spAB.2 k, ha]; rfl
            have hNoneC : lookupEntries c.entries k = none := by
              cases spABC1.1 k with
              | inl hab0 => rw [hSomeAB] at hab0; cases hab0
              | inr hc0 => exact hc0
            rw [spBC.2 k, hNoneB, hNoneC]
            exact .inr rfl
        let ⟨zsABC2, hA_BC⟩ :=
          mergeDisjointEntries_complete a.entries zsBC a.sorted sBC hDisjA_BC
        have sABC2 := mergeDisjointEntries_sorted a.sorted sBC hA_BC
        have spABC2 := mergeDisjointEntries_sound a.entries zsBC zsABC2
          a.sorted sBC hA_BC
        rw [hA_BC, mkSortedAssocMap?_some sABC2]
        have hEqEntries : zsABC1 = zsABC2 :=
          sorted_entries_ext sABC1 sABC2 (fun k => by
            rw [spABC1.2 k, spAB.2 k, spABC2.2 k, spBC.2 k]
            exact orElseOpt_assoc _ _ _)
        exact congrArg some (sortedAssocMap_ext hEqEntries)
  unit_left := fun a => by
    unfold SortedAssocMap.merge SortedAssocMap.empty
    dsimp only
    rw [mergeDisjointEntries_nil_left, mkSortedAssocMap?_some a.sorted]
  cancellative := fun a b₁ b₂ c h1 h2 => by
    unfold SortedAssocMap.merge at h1 h2
    cases hM1 : mergeDisjointEntries a.entries b₁.entries with
    | none => rw [hM1] at h1; cases h1
    | some zs1 =>
      have s1 := mergeDisjointEntries_sorted a.sorted b₁.sorted hM1
      rw [hM1, mkSortedAssocMap?_some s1] at h1
      injection h1 with hc1
      cases hM2 : mergeDisjointEntries a.entries b₂.entries with
      | none => rw [hM2] at h2; cases h2
      | some zs2 =>
        have s2 := mergeDisjointEntries_sorted a.sorted b₂.sorted hM2
        rw [hM2, mkSortedAssocMap?_some s2] at h2
        injection h2 with hc2
        have hZsEq : zs1 = zs2 := by
          have e1 : zs1 = c.entries := congrArg SortedAssocMap.entries hc1
          have e2 : zs2 = c.entries := congrArg SortedAssocMap.entries hc2
          exact e1.trans e2.symm
        subst hZsEq
        have sp1 := mergeDisjointEntries_sound a.entries b₁.entries zs1
          a.sorted b₁.sorted hM1
        have sp2 := mergeDisjointEntries_sound a.entries b₂.entries zs1
          a.sorted b₂.sorted hM2
        refine sortedAssocMap_ext (sorted_entries_ext b₁.sorted b₂.sorted (fun k => ?_))
        cases ha : lookupEntries a.entries k with
        | some _ =>
          have hb1 : lookupEntries b₁.entries k = none := by
            cases sp1.1 k with
            | inl ha0 => rw [ha] at ha0; cases ha0
            | inr hb0 => exact hb0
          have hb2 : lookupEntries b₂.entries k = none := by
            cases sp2.1 k with
            | inl ha0 => rw [ha] at ha0; cases ha0
            | inr hb0 => exact hb0
          rw [hb1, hb2]
        | none =>
          have e1 := sp1.2 k
          have e2 := sp2.2 k
          rw [ha] at e1 e2
          dsimp only [orElseOpt] at e1 e2
          exact e1.symm.trans e2

/-- Canonical spatial heaplet mapping `ByteAddr` to `AllocByte`
(`sortedAssocPCM` remains polymorphic over any `V : Type`). -/
abbrev ByteHeaplet : Type := SortedAssocMap AllocByte

/-- Constructive `ExplPCM` over `ByteHeaplet` (`propext`-only; `0` `Quot.sound`,
`0` `Classical.choice`). -/
def byteHeapletPCM : ExplPCM ByteHeaplet := sortedAssocPCM AllocByte

/-- Singleton byte points-to assertion `addr ↦ val`. -/
def bytePointsTo (addr : ByteAddr) (val : AllocByte) :
    SepProp ByteHeaplet :=
  fun h => h = SortedAssocMap.singleton addr val

/-- Two `bytePointsTo` assertions at distinct addresses are disjoint and
compose in `byteHeapletPCM`. -/
theorem bytePointsTo_disjoint_of_ne {a₁ a₂ : ByteAddr}
    {v₁ v₂ : AllocByte} (hNe : a₁ ≠ a₂) :
    ∃ h : ByteHeaplet,
      sepConj byteHeapletPCM (bytePointsTo a₁ v₁) (bytePointsTo a₂ v₂) h := by
  have hS1 : IsStrictlySorted [(a₁, v₁)] := True.intro
  have hS2 : IsStrictlySorted [(a₂, v₂)] := True.intro
  have hDisj : DisjointEntries [(a₁, v₁)] [(a₂, v₂)] := by
    intro k
    cases hb1 : addrBeq a₁ k with
    | false =>
      change (if addrBeq a₁ k then some v₁ else none) = none ∨ _
      rw [hb1]
      exact .inl rfl
    | true =>
      have he1 : a₁ = k := (addrBeq_iff a₁ k).mp hb1
      subst he1
      have hb2 : addrBeq a₂ a₁ = false :=
        addrBeq_false_of_ne (fun he2 => hNe he2.symm)
      change _ ∨ (if addrBeq a₂ a₁ then some v₂ else none) = none
      rw [hb2]
      exact .inr rfl
  let ⟨zs, hM⟩ := mergeDisjointEntries_complete [(a₁, v₁)] [(a₂, v₂)]
    hS1 hS2 hDisj
  have hSz : IsStrictlySorted zs := mergeDisjointEntries_sorted hS1 hS2 hM
  refine ⟨{ entries := zs, sorted := hSz },
          SortedAssocMap.singleton a₁ v₁,
          SortedAssocMap.singleton a₂ v₂, ?_, rfl, rfl⟩
  unfold byteHeapletPCM sortedAssocPCM SortedAssocMap.merge
    SortedAssocMap.singleton
  dsimp only
  rw [hM, mkSortedAssocMap?_some hSz]

/-- Same-address `bytePointsTo` assertions are mutually incompatible. -/
theorem bytePointsTo_conflict (addr : ByteAddr) (v₁ v₂ : AllocByte)
    (h : ByteHeaplet) :
    ¬ sepConj byteHeapletPCM (bytePointsTo addr v₁) (bytePointsTo addr v₂) h := by
  intro hConj
  let ⟨h₁, h₂, hop, hp₁, hp₂⟩ := hConj
  unfold bytePointsTo at hp₁ hp₂
  subst hp₁; subst hp₂
  unfold byteHeapletPCM sortedAssocPCM SortedAssocMap.merge
    SortedAssocMap.singleton at hop
  dsimp only at hop
  rw [mergeDisjointEntries_cons_cons, addrLt_irrefl] at hop
  cases hop

/-- Single-address `bytePointsTo` update `addr ↦ v₁` to `addr ↦ v₂` is
`FramePreserving` in `byteHeapletPCM`: any frame `hf` disjoint from
`SortedAssocMap.singleton addr v₁` is also disjoint from
`SortedAssocMap.singleton addr v₂`. -/
theorem bytePointsTo_framePreserving_update (addr : ByteAddr)
    (v₁ v₂ : AllocByte) :
    FramePreserving byteHeapletPCM
      (bytePointsTo addr v₁) (bytePointsTo addr v₂) := by
  intro h₁ hf h hp₁ hop
  unfold bytePointsTo at hp₁
  subst hp₁
  unfold byteHeapletPCM sortedAssocPCM SortedAssocMap.merge
    SortedAssocMap.singleton at hop
  dsimp only at hop
  cases hM1 : mergeDisjointEntries [(addr, v₁)] hf.entries with
  | none =>
    rw [hM1] at hop
    cases hop
  | some zs1 =>
    have hSp1 :=
      mergeDisjointEntries_sound [(addr, v₁)] hf.entries zs1 True.intro
        hf.sorted hM1
    have hDisj2 : DisjointEntries [(addr, v₂)] hf.entries := by
      intro k
      cases hb : addrBeq addr k with
      | false =>
        change (if addrBeq addr k then some v₂ else none) = none ∨ _
        rw [hb]
        exact .inl rfl
      | true =>
        have hd1 := hSp1.1 k
        change (if addrBeq addr k then some v₁ else none) = none ∨
          lookupEntries hf.entries k = none at hd1
        rw [hb] at hd1
        cases hd1 with
        | inl hN => cases hN
        | inr hNoneF => exact .inr hNoneF
    let ⟨zs2, hM2⟩ :=
      mergeDisjointEntries_complete [(addr, v₂)] hf.entries
        (True.intro : IsStrictlySorted [(addr, v₂)]) hf.sorted hDisj2
    have hS2 : IsStrictlySorted [(addr, v₂)] := True.intro
    have hSz2 : IsStrictlySorted zs2 :=
      mergeDisjointEntries_sorted hS2 hf.sorted hM2
    refine ⟨SortedAssocMap.singleton addr v₂,
            { entries := zs2, sorted := hSz2 }, ?_, rfl⟩
    unfold byteHeapletPCM sortedAssocPCM SortedAssocMap.merge
      SortedAssocMap.singleton
    dsimp only
    rw [hM2, mkSortedAssocMap?_some hSz2]

/-! ## Allocation-Metadata-Preserving Footprint Framing (`MemDisjointFrame`) -/

/-- Half-open byte range `[offset, offset + len)` inside `allocId`. -/
structure ByteRange where
  allocId : AllocId
  offset : Nat
  len : Nat

/-- Computable membership test for `addr` inside `[r.offset, r.offset + r.len)`.
-/
def ByteRange.contains (r : ByteRange) (addr : ByteAddr) : Bool :=
  Nat.beq r.allocId addr.allocId &&
    Nat.ble r.offset addr.offset &&
    Nat.blt addr.offset (r.offset + r.len)

/-- Finite write footprint represented as a list of `ByteRange`s. -/
abbrev ByteFootprint : Type := List ByteRange

/-- Computable footprint membership test (`0` `noncomputable`). -/
def ByteFootprint.contains (fp : ByteFootprint) (addr : ByteAddr) : Bool :=
  fp.any (fun r => r.contains addr)

/-- Allocation-metadata-preserving memory frame relation: from `mem` to `mem'`,
`nextAllocId` grows monotonically, every pre-existing allocation `aid <
mem.nextAllocId` retains its `live`, `alignLog2`, `mutability`, and byte
length, and every byte outside `fp` retains its exact `AllocByte`. -/
def MemDisjointFrame (fp : ByteFootprint) (mem mem' : MemoryState) : Prop :=
  mem.nextAllocId ≤ mem'.nextAllocId ∧
  ∀ aid : AllocId, aid < mem.nextAllocId →
    match findAllocation aid mem.allocations,
          findAllocation aid mem'.allocations with
    | none, none => True
    | some a, some a' =>
      a'.allocId = a.allocId ∧
      a'.alignLog2 = a.alignLog2 ∧
      a'.mutability = a.mutability ∧
      a'.live = a.live ∧
      a'.bytes.length = a.bytes.length ∧
      ∀ off : Nat, ByteFootprint.contains fp ⟨aid, off⟩ = false →
        Trusted.MirSemantics.getElem? a'.bytes off =
          Trusted.MirSemantics.getElem? a.bytes off
    | _, _ => False

/-- Reflexivity of `MemDisjointFrame`. -/
theorem MemDisjointFrame.refl (fp : ByteFootprint) (mem : MemoryState) :
    MemDisjointFrame fp mem mem := by
  refine ⟨Nat.le_refl mem.nextAllocId, fun aid _ => ?_⟩
  cases findAllocation aid mem.allocations with
  | none => exact True.intro
  | some _ => exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Transitivity of `MemDisjointFrame` over a fixed footprint `fp`. -/
theorem MemDisjointFrame.trans {fp : ByteFootprint}
    {m₁ m₂ m₃ : MemoryState}
    (h₁₂ : MemDisjointFrame fp m₁ m₂)
    (h₂₃ : MemDisjointFrame fp m₂ m₃) :
    MemDisjointFrame fp m₁ m₃ := by
  refine ⟨Nat.le_trans h₁₂.1 h₂₃.1, fun aid hLt1 => ?_⟩
  have h1 := h₁₂.2 aid hLt1
  have h2 := h₂₃.2 aid (Nat.lt_of_lt_of_le hLt1 h₁₂.1)
  cases f1 : findAllocation aid m₁.allocations with
  | none =>
    rw [f1] at h1
    cases f2 : findAllocation aid m₂.allocations with
    | some _ => rw [f2] at h1; exact False.elim h1
    | none =>
      rw [f2] at h2
      cases f3 : findAllocation aid m₃.allocations with
      | none => exact True.intro
      | some _ => rw [f3] at h2; exact False.elim h2
  | some a1 =>
    rw [f1] at h1
    cases f2 : findAllocation aid m₂.allocations with
    | none => rw [f2] at h1; exact False.elim h1
    | some a2 =>
      rw [f2] at h1 h2
      cases f3 : findAllocation aid m₃.allocations with
      | none => rw [f3] at h2; exact False.elim h2
      | some a3 =>
        rw [f3] at h2
        exact ⟨h2.1.trans h1.1,
               h2.2.1.trans h1.2.1,
               h2.2.2.1.trans h1.2.2.1,
               h2.2.2.2.1.trans h1.2.2.2.1,
               h2.2.2.2.2.1.trans h1.2.2.2.2.1,
               fun off hOut =>
                 (h2.2.2.2.2.2 off hOut).trans (h1.2.2.2.2.2 off hOut)⟩

/-! ## Constructive Reflective `SepAC` Frame Canceler (`BoolCertCut`) -/

/-- Balanced Braun binary tree mapping `Nat` atom indices to `SepProp M`
assertions (`O(log N)` lookup, `0` `noncomputable`).

Inspired by `SepAtomTree` in Apache-2.0 `google-deepmind/code-verification`
(`arm64-semantics/ProofLib/SepLogic.lean`), using single-argument structural
recursion on `SepAtomTree` and `cond` so Lean compiles directly with
`hasIR = true` and zero `noncomputable` definitions. -/
inductive SepAtomTree (M : Type) : Type where
  | empty : SepAtomTree M
  | node (val : SepProp M) (left right : SepAtomTree M) : SepAtomTree M

/-- `O(depth)` Braun-tree lookup via `@Nat.rec` (`0` `noncomputable`, `0`
`._unsafe_rec`, `hasIR = true`): index `0` at root, `2*k + 1` in `left` at `k`,
`2*k + 2` in `right` at `k`; out-of-bounds returns `sepEmp pcm`. -/
def SepAtomTree.getAt {M : Type} (pcm : ExplPCM M) (depth : Nat) :
    SepAtomTree M → Nat → SepProp M :=
  @Nat.rec (fun _ => SepAtomTree M → Nat → SepProp M)
    (fun t idx =>
      match t, idx with
      | .node v _ _, 0 => v
      | _, _ => sepEmp pcm)
    (fun _ ih t idx =>
      match t with
      | .empty => sepEmp pcm
      | .node v l r =>
        match idx with
        | 0 => v
        | n + 1 =>
          cond (Nat.beq (Nat.mod n 2) 0)
            (ih l (Nat.div n 2))
            (ih r (Nat.div n 2)))
    depth

/-- `O(log N)` Braun-tree lookup covering up to `2^20` atoms (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`). -/
def SepAtomTree.get {M : Type} (pcm : ExplPCM M) (t : SepAtomTree M)
    (idx : Nat) : SepProp M :=
  SepAtomTree.getAt pcm 20 t idx

private def sepUnzipEvenOdd {α : Type} (xs : List α) : List α × List α :=
  List.foldr (fun x eo => (x :: eo.2, eo.1)) ([], []) xs

private def sepAtomTreeOfListFuel {M : Type} (fuel : Nat) :
    List (SepProp M) → SepAtomTree M :=
  @Nat.rec (fun _ => List (SepProp M) → SepAtomTree M)
    (fun _ => .empty)
    (fun _ ih xs =>
      match xs with
      | [] => .empty
      | v :: rest =>
        let eo := sepUnzipEvenOdd rest
        .node v (ih eo.1) (ih eo.2))
    fuel

/-- Builds a balanced `SepAtomTree M` from a list of separation assertions. -/
def SepAtomTree.ofList {M : Type} (xs : List (SepProp M)) : SepAtomTree M :=
  sepAtomTreeOfListFuel xs.length xs

/-- Reflected separation-logic formula AST over `Nat` atom indices. -/
inductive SepExpr : Type where
  | emp : SepExpr
  | atom (idx : Nat) : SepExpr
  | star (lhs rhs : SepExpr) : SepExpr

/-- Propositional denotation of `SepExpr` against `env : SepAtomTree M` over
`pcm`. Marked `noncomputable` solely to avoid emitting compiler `._unsafe_rec`
auxiliaries; all reflective checkers below are computable (`hasIR = true`). -/
noncomputable def SepExpr.eval {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) : SepExpr → SepProp M
  | .emp => sepEmp pcm
  | .atom i => env.get pcm i
  | .star a b => sepConj pcm (a.eval pcm env) (b.eval pcm env)

private theorem sepEquiv_refl {M : Type} (P : SepProp M) : SepEquiv P P :=
  fun _ => Iff.rfl

private theorem sepEquiv_symm {M : Type} {P Q : SepProp M}
    (h : SepEquiv P Q) : SepEquiv Q P :=
  fun m => (h m).symm

private theorem sepEquiv_trans {M : Type} {P Q R : SepProp M}
    (h₁ : SepEquiv P Q) (h₂ : SepEquiv Q R) : SepEquiv P R :=
  fun m => (h₁ m).trans (h₂ m)

private theorem sepEquiv_conj_congr {M : Type} (pcm : ExplPCM M)
    {P₁ P₂ Q₁ Q₂ : SepProp M}
    (hP : SepEquiv P₁ P₂) (hQ : SepEquiv Q₁ Q₂) :
    SepEquiv (sepConj pcm P₁ Q₁) (sepConj pcm P₂ Q₂) := by
  intro m
  constructor
  · exact sepConj_mono pcm (fun h hp => (hP h).mp hp)
      (fun h hq => (hQ h).mp hq) m
  · exact sepConj_mono pcm (fun h hp => (hP h).mpr hp)
      (fun h hq => (hQ h).mpr hq) m

private theorem sepConj_left_comm {M : Type} (pcm : ExplPCM M)
    (P Q R : SepProp M) :
    SepEquiv (sepConj pcm P (sepConj pcm Q R))
      (sepConj pcm Q (sepConj pcm P R)) :=
  sepEquiv_trans
    (sepEquiv_symm (sepConj_assoc pcm P Q R))
    (sepEquiv_trans
      (sepEquiv_conj_congr pcm (sepConj_comm pcm P Q) (sepEquiv_refl R))
      (sepConj_assoc pcm Q P R))

/-- Canonical binary radix-2 atom-multiplicity bag (`0` `noncomputable`,
`0` `._unsafe_rec`, `hasIR = true`).

Why a radix-2 multiplicity bag instead of a sorted linked list: comparing or
merging 256-element `List Nat`s reaches Lean's default `maxRecDepth = 512`
inside kernel `whnf`/`isDefEq`. Indexing atom multiplicities by the bits of
`idx + 1` bounds every `add`, `cancel`, and `beq` recursion to depth
`log2(maxIdx + 1)` (`≤ 9` at `N = 256`, `≤ 13` at `N = 4,096`), discharging
256-atom AC equivalence and partial frame cancellation by `rfl` well under
default `maxRecDepth`. -/
inductive AtomBag : Type where
  | empty : AtomBag
  | node (left : AtomBag) (count : Nat) (right : AtomBag) : AtomBag

/-- Smart constructor collapsing `.node .empty 0 .empty` back to `.empty` so
canceled bags compare equal to `.empty` structurally. -/
def AtomBag.make (l : AtomBag) (c : Nat) (r : AtomBag) : AtomBag :=
  match c with
  | 0 =>
    match l, r with
    | .empty, .empty => .empty
    | _, _ => .node l 0 r
  | _ + 1 => .node l c r

/-- Fuel-bounded structural equality on `AtomBag` via `@Nat.rec` (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`). Returns `false` on any
`.node` at fuel `0` so `beqAt fuel a b = true` unconditionally implies `a = b`.
-/
def AtomBag.beqAt (fuel : Nat) : AtomBag → AtomBag → Bool :=
  @Nat.rec (fun _ => AtomBag → AtomBag → Bool)
    (fun a b =>
      match a, b with
      | .empty, .empty => true
      | _, _ => false)
    (fun _ ih a b =>
      match a, b with
      | .empty, .empty => true
      | .node l1 c1 r1, .node l2 c2 r2 =>
        cond (Nat.beq c1 c2) (cond (ih l1 l2) (ih r1 r2) false) false
      | _, _ => false)
    fuel

/-- Structural equality on `AtomBag` up to radix depth `21`. -/
def AtomBag.beq (a b : AtomBag) : Bool :=
  AtomBag.beqAt 21 a b

private theorem atomBag_eq_of_beqAt :
    ∀ {fuel : Nat} {a b : AtomBag}, AtomBag.beqAt fuel a b = true → a = b
  | 0, .empty, .empty, _ => rfl
  | 0, .empty, .node _ _ _, h => by cases h
  | 0, .node _ _ _, .empty, h => by cases h
  | 0, .node _ _ _, .node _ _ _, h => by cases h
  | _ + 1, .empty, .empty, _ => rfl
  | _ + 1, .empty, .node _ _ _, h => by cases h
  | _ + 1, .node _ _ _, .empty, h => by cases h
  | d + 1, .node l1 c1 r1, .node l2 c2 r2, h => by
    change cond (Nat.beq c1 c2)
      (cond (AtomBag.beqAt d l1 l2) (AtomBag.beqAt d r1 r2) false) false = true at h
    cases hc : Nat.beq c1 c2 with
    | false => rw [hc] at h; cases h
    | true =>
      rw [hc] at h; dsimp only [cond] at h
      cases hl : AtomBag.beqAt d l1 l2 with
      | false => rw [hl] at h; cases h
      | true =>
        rw [hl] at h; dsimp only [cond] at h
        rw [Nat.eq_of_beq_eq_true hc, atomBag_eq_of_beqAt hl,
          atomBag_eq_of_beqAt h]

/-- Fuel-bounded pointwise multiset addition on `AtomBag` via `@Nat.rec` (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`), failing closed (`none`)
if two `.node`s exceed `fuel`. -/
def AtomBag.addAt (fuel : Nat) : AtomBag → AtomBag → Option AtomBag :=
  @Nat.rec (fun _ => AtomBag → AtomBag → Option AtomBag)
    (fun a b =>
      match a, b with
      | .empty, b => some b
      | a, .empty => some a
      | .node _ _ _, .node _ _ _ => none)
    (fun _ ih a b =>
      match a, b with
      | .empty, b => some b
      | a, .empty => some a
      | .node l1 c1 r1, .node l2 c2 r2 =>
        match ih l1 l2 with
        | none => none
        | some l =>
          match ih r1 r2 with
          | none => none
          | some r => some (AtomBag.make l (c1 + c2) r))
    fuel

/-- Fuel-bounded pointwise multiset common-atom cancellation on `AtomBag` via
`@Nat.rec` (`0` `noncomputable`, `0` `._unsafe_rec`, `hasIR = true`), returning
`some (lhsRem, rhsRem)` with all shared multiplicities canceled. -/
def AtomBag.cancelAt (fuel : Nat) :
    AtomBag → AtomBag → Option (AtomBag × AtomBag) :=
  @Nat.rec (fun _ => AtomBag → AtomBag → Option (AtomBag × AtomBag))
    (fun a b =>
      match a, b with
      | .empty, b => some (.empty, b)
      | a, .empty => some (a, .empty)
      | .node _ _ _, .node _ _ _ => none)
    (fun _ ih a b =>
      match a, b with
      | .empty, b => some (.empty, b)
      | a, .empty => some (a, .empty)
      | .node l1 c1 r1, .node l2 c2 r2 =>
        match ih l1 l2 with
        | none => none
        | some rl =>
          match ih r1 r2 with
          | none => none
          | some rr =>
            let d1 := cond (Nat.ble c1 c2) 0 (c1 - c2)
            let d2 := cond (Nat.ble c1 c2) (c2 - c1) 0
            some (AtomBag.make rl.1 d1 rr.1, AtomBag.make rl.2 d2 rr.2))
    fuel

private def bagPow2 (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => 2 * ih) n

private def bagSingletonFuel (fuel : Nat) : Nat → AtomBag :=
  @Nat.rec (fun _ => Nat → AtomBag)
    (fun _ => .node .empty 1 .empty)
    (fun _ ih m =>
      cond (Nat.ble m 1)
        (.node .empty 1 .empty)
        (cond (Nat.beq (Nat.mod m 2) 0)
          (.node (ih (Nat.div m 2)) 0 .empty)
          (.node .empty 0 (ih (Nat.div m 2)))))
    fuel

/-- Builds the singleton `AtomBag` for atom index `idx` (exact for all
`idx < 2^20 - 1 = 1,048,575`, `0` `noncomputable`, `0` `._unsafe_rec`). -/
def AtomBag.singleton (idx : Nat) : AtomBag :=
  bagSingletonFuel 20 (idx + 1)

/-- Compiles a `SepExpr` into its canonical `AtomBag` multiset via `@Nat.rec`
up to AST depth `fuel` (`0` `noncomputable`, `0` `._unsafe_rec`,
`hasIR = true`), failing closed (`none`) if AST depth exceeds `fuel` or any
atom index reaches `2^20 - 1`. -/
def SepExpr.toBagAt (fuel : Nat) : SepExpr → Option AtomBag :=
  @Nat.rec (fun _ => SepExpr → Option AtomBag)
    (fun _ => none)
    (fun _ ih e =>
      match e with
      | .emp => some .empty
      | .atom i =>
        cond (Nat.blt (i + 1) 1048576) (some (AtomBag.singleton i)) none
      | .star a b =>
        match ih a with
        | none => none
        | some ba =>
          match ih b with
          | none => none
          | some bb => AtomBag.addAt 21 ba bb)
    fuel

/-- `n`-fold separating conjunction of `P` (`sepRepeat pcm 0 P = sepEmp pcm`).
-/
def sepRepeat {M : Type} (pcm : ExplPCM M) (n : Nat) (P : SepProp M) :
    SepProp M :=
  @Nat.rec (fun _ => SepProp M) (sepEmp pcm) (fun _ ih => sepConj pcm P ih) n

private theorem sepRepeat_add {M : Type} (pcm : ExplPCM M) (P : SepProp M) :
    ∀ (a b : Nat),
      SepEquiv (sepRepeat pcm (a + b) P)
        (sepConj pcm (sepRepeat pcm a P) (sepRepeat pcm b P))
  | 0, b => by
    rw [Nat.zero_add]
    exact sepEquiv_symm (sepConj_emp_left pcm (sepRepeat pcm b P))
  | a + 1, b => by
    rw [Nat.succ_add]
    exact sepEquiv_trans
      (sepEquiv_conj_congr pcm (sepEquiv_refl P) (sepRepeat_add pcm P a b))
      (sepEquiv_symm (sepConj_assoc pcm P _ _))

/-- Propositional denotation of `AtomBag` against `env : SepAtomTree M` at
affine positive key coordinates `(base, stride)`. Marked `noncomputable` solely
to suppress compiler `._unsafe_rec` auxiliaries (never called by computable
checkers). -/
noncomputable def evalBagAt {M : Type} (pcm : ExplPCM M) (env : SepAtomTree M) :
    Nat → Nat → AtomBag → SepProp M
  | _, _, .empty => sepEmp pcm
  | base, stride, .node l c r =>
    sepConj pcm (sepRepeat pcm c (env.get pcm (base + stride - 1)))
      (sepConj pcm
        (evalBagAt pcm env base (2 * stride) l)
        (evalBagAt pcm env (base + stride) (2 * stride) r))

/-- Top-level `AtomBag` semantics at root `(base := 0, stride := 1)`. -/
noncomputable def evalBag {M : Type} (pcm : ExplPCM M) (env : SepAtomTree M)
    (b : AtomBag) : SepProp M :=
  evalBagAt pcm env 0 1 b

private theorem evalBagAt_make {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) (base stride : Nat) (l : AtomBag) (c : Nat)
    (r : AtomBag) :
    SepEquiv (evalBagAt pcm env base stride (AtomBag.make l c r))
      (evalBagAt pcm env base stride (.node l c r)) := by
  cases c with
  | succ _ => exact sepEquiv_refl _
  | zero =>
    cases l with
    | node _ _ _ => exact sepEquiv_refl _
    | empty =>
      cases r with
      | node _ _ _ => exact sepEquiv_refl _
      | empty =>
        change SepEquiv (sepEmp pcm)
          (sepConj pcm (sepEmp pcm) (sepConj pcm (sepEmp pcm) (sepEmp pcm)))
        exact sepEquiv_symm
          (sepEquiv_trans
            (sepConj_emp_left pcm (sepConj pcm (sepEmp pcm) (sepEmp pcm)))
            (sepConj_emp_left pcm (sepEmp pcm)))

private theorem sepConj_interchange {M : Type} (pcm : ExplPCM M)
    (A B C D : SepProp M) :
    SepEquiv (sepConj pcm (sepConj pcm A B) (sepConj pcm C D))
      (sepConj pcm (sepConj pcm A C) (sepConj pcm B D)) :=
  sepEquiv_trans (sepConj_assoc pcm A B (sepConj pcm C D))
    (sepEquiv_trans
      (sepEquiv_conj_congr pcm (sepEquiv_refl A) (sepConj_left_comm pcm B C D))
      (sepEquiv_symm (sepConj_assoc pcm A C (sepConj pcm B D))))

private theorem evalBagAt_addAt {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) :
    ∀ (fuel : Nat) (a b ab : AtomBag) (base stride : Nat),
      AtomBag.addAt fuel a b = some ab →
      SepEquiv (evalBagAt pcm env base stride ab)
        (sepConj pcm (evalBagAt pcm env base stride a)
          (evalBagAt pcm env base stride b))
  | 0, .empty, b, ab, base, stride, h => by
    injection h with hEq; subst hEq
    exact sepEquiv_symm (sepConj_emp_left pcm (evalBagAt pcm env base stride b))
  | 0, .node l1 c1 r1, .empty, ab, base, stride, h => by
    injection h with hEq; subst hEq
    exact sepEquiv_symm
      (sepConj_emp_right pcm (evalBagAt pcm env base stride (.node l1 c1 r1)))
  | 0, .node _ _ _, .node _ _ _, _, _, _, h => by cases h
  | _ + 1, .empty, b, ab, base, stride, h => by
    injection h with hEq; subst hEq
    exact sepEquiv_symm (sepConj_emp_left pcm (evalBagAt pcm env base stride b))
  | _ + 1, .node l1 c1 r1, .empty, ab, base, stride, h => by
    injection h with hEq; subst hEq
    exact sepEquiv_symm
      (sepConj_emp_right pcm (evalBagAt pcm env base stride (.node l1 c1 r1)))
  | d + 1, .node l1 c1 r1, .node l2 c2 r2, ab, base, stride, h => by
    change (match AtomBag.addAt d l1 l2 with
        | none => none
        | some l =>
          match AtomBag.addAt d r1 r2 with
          | none => none
          | some r => some (AtomBag.make l (c1 + c2) r)) = some ab at h
    cases hl : AtomBag.addAt d l1 l2 with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      cases hr : AtomBag.addAt d r1 r2 with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        injection h with hEq; subst hEq
        refine sepEquiv_trans (evalBagAt_make pcm env base stride l (c1 + c2) r) ?_
        exact sepEquiv_trans
          (sepEquiv_conj_congr pcm
            (sepRepeat_add pcm (env.get pcm (base + stride - 1)) c1 c2)
            (sepEquiv_trans
              (sepEquiv_conj_congr pcm
                (evalBagAt_addAt pcm env d l1 l2 l base (2 * stride) hl)
                (evalBagAt_addAt pcm env d r1 r2 r (base + stride) (2 * stride) hr))
              (sepEquiv_symm (sepConj_interchange pcm _ _ _ _))))
          (sepEquiv_symm (sepConj_interchange pcm _ _ _ _))

private theorem evalBagAt_cancelAt {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) :
    ∀ (fuel : Nat) (a b r1 r2 : AtomBag) (base stride : Nat),
      AtomBag.cancelAt fuel a b = some (r1, r2) →
      ∃ common : AtomBag,
        SepEquiv (evalBagAt pcm env base stride a)
          (sepConj pcm (evalBagAt pcm env base stride common)
            (evalBagAt pcm env base stride r1)) ∧
        SepEquiv (evalBagAt pcm env base stride b)
          (sepConj pcm (evalBagAt pcm env base stride common)
            (evalBagAt pcm env base stride r2))
  | 0, .empty, b, r1, r2, base, stride, h => by
    injection h with hEq
    cases hEq
    exact ⟨.empty, sepEquiv_symm (sepConj_emp_left pcm _),
      sepEquiv_symm (sepConj_emp_left pcm (evalBagAt pcm env base stride b))⟩
  | 0, .node _ _ _, .empty, r1, r2, _, _, h => by
    injection h with hEq
    cases hEq
    exact ⟨.empty, sepEquiv_symm (sepConj_emp_left pcm _),
      sepEquiv_symm (sepConj_emp_left pcm _)⟩
  | 0, .node _ _ _, .node _ _ _, _, _, _, _, h => by cases h
  | _ + 1, .empty, b, r1, r2, base, stride, h => by
    injection h with hEq
    cases hEq
    exact ⟨.empty, sepEquiv_symm (sepConj_emp_left pcm _),
      sepEquiv_symm (sepConj_emp_left pcm (evalBagAt pcm env base stride b))⟩
  | _ + 1, .node _ _ _, .empty, r1, r2, _, _, h => by
    injection h with hEq
    cases hEq
    exact ⟨.empty, sepEquiv_symm (sepConj_emp_left pcm _),
      sepEquiv_symm (sepConj_emp_left pcm _)⟩
  | d + 1, .node l1 c1 r1, .node l2 c2 r2, out1, out2, base, stride, h => by
    change (match AtomBag.cancelAt d l1 l2 with
        | none => none
        | some rl =>
          match AtomBag.cancelAt d r1 r2 with
          | none => none
          | some rr =>
            some (AtomBag.make rl.1 (cond (Nat.ble c1 c2) 0 (c1 - c2)) rr.1,
                  AtomBag.make rl.2 (cond (Nat.ble c1 c2) (c2 - c1) 0) rr.2)) =
      some (out1, out2) at h
    cases hl : AtomBag.cancelAt d l1 l2 with
    | none => rw [hl] at h; cases h
    | some rl =>
      rw [hl] at h
      cases hr : AtomBag.cancelAt d r1 r2 with
      | none => rw [hr] at h; cases h
      | some rr =>
        rw [hr] at h
        injection h with hPair
        let ⟨cl, hL1, hL2⟩ :=
          evalBagAt_cancelAt pcm env d l1 l2 rl.1 rl.2 base (2 * stride) hl
        let ⟨cr, hR1, hR2⟩ :=
          evalBagAt_cancelAt pcm env d r1 r2 rr.1 rr.2 (base + stride) (2 * stride) hr
        cases hle : Nat.ble c1 c2 with
        | true =>
          rw [hle] at hPair
          dsimp only [cond] at hPair
          have hOut1 : AtomBag.make rl.1 0 rr.1 = out1 := congrArg Prod.fst hPair
          have hOut2 : AtomBag.make rl.2 (c2 - c1) rr.2 = out2 :=
            congrArg Prod.snd hPair
          subst hOut1; subst hOut2
          have hLe : c1 ≤ c2 := Nat.le_of_ble_eq_true hle
          have hSub : c1 + (c2 - c1) = c2 := by
            rw [Nat.add_comm]
            exact Nat.sub_add_cancel hLe
          have hRep := sepRepeat_add pcm (env.get pcm (base + stride - 1)) c1 (c2 - c1)
          rw [hSub] at hRep
          refine ⟨.node cl c1 cr, ?_, ?_⟩
          · refine sepEquiv_trans ?_
              (sepEquiv_conj_congr pcm (sepEquiv_refl _)
                (sepEquiv_symm (evalBagAt_make pcm env base stride rl.1 0 rr.1)))
            exact sepEquiv_trans
              (sepEquiv_conj_congr pcm
                (sepEquiv_symm (sepConj_emp_right pcm _))
                (sepEquiv_trans
                  (sepEquiv_conj_congr pcm hL1 hR1)
                  (sepConj_interchange pcm _ _ _ _)))
              (sepConj_interchange pcm _ _ _ _)
          · refine sepEquiv_trans ?_
              (sepEquiv_conj_congr pcm (sepEquiv_refl _)
                (sepEquiv_symm (evalBagAt_make pcm env base stride rl.2 (c2 - c1) rr.2)))
            exact sepEquiv_trans
              (sepEquiv_conj_congr pcm hRep
                (sepEquiv_trans
                  (sepEquiv_conj_congr pcm hL2 hR2)
                  (sepConj_interchange pcm _ _ _ _)))
              (sepConj_interchange pcm _ _ _ _)
        | false =>
          rw [hle] at hPair
          dsimp only [cond] at hPair
          have hOut1 : AtomBag.make rl.1 (c1 - c2) rr.1 = out1 :=
            congrArg Prod.fst hPair
          have hOut2 : AtomBag.make rl.2 0 rr.2 = out2 := congrArg Prod.snd hPair
          subst hOut1; subst hOut2
          have hGe : c2 ≤ c1 := by
            cases Nat.lt_or_ge c2 c1 with
            | inl hlt => exact Nat.le_of_lt hlt
            | inr hge =>
              have hbt := Nat.ble_eq_true_of_le hge
              rw [hle] at hbt; cases hbt
          have hSub : c2 + (c1 - c2) = c1 := by
            rw [Nat.add_comm]
            exact Nat.sub_add_cancel hGe
          have hRep := sepRepeat_add pcm (env.get pcm (base + stride - 1)) c2 (c1 - c2)
          rw [hSub] at hRep
          refine ⟨.node cl c2 cr, ?_, ?_⟩
          · refine sepEquiv_trans ?_
              (sepEquiv_conj_congr pcm (sepEquiv_refl _)
                (sepEquiv_symm (evalBagAt_make pcm env base stride rl.1 (c1 - c2) rr.1)))
            exact sepEquiv_trans
              (sepEquiv_conj_congr pcm hRep
                (sepEquiv_trans
                  (sepEquiv_conj_congr pcm hL1 hR1)
                  (sepConj_interchange pcm _ _ _ _)))
              (sepConj_interchange pcm _ _ _ _)
          · refine sepEquiv_trans ?_
              (sepEquiv_conj_congr pcm (sepEquiv_refl _)
                (sepEquiv_symm (evalBagAt_make pcm env base stride rl.2 0 rr.2)))
            exact sepEquiv_trans
              (sepEquiv_conj_congr pcm
                (sepEquiv_symm (sepConj_emp_right pcm _))
                (sepEquiv_trans
                  (sepEquiv_conj_congr pcm hL2 hR2)
                  (sepConj_interchange pcm _ _ _ _)))
              (sepConj_interchange pcm _ _ _ _)

private theorem evalBagAt_singletonFuel {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) :
    ∀ (fuel base stride m : Nat),
      0 < m → m < bagPow2 fuel →
      SepEquiv (evalBagAt pcm env base stride (bagSingletonFuel fuel m))
        (env.get pcm (base + stride * m - 1))
  | 0, _, _, m, hPos, hLt => False.elim (Nat.not_lt_of_ge hPos hLt)
  | d + 1, base, stride, m, hPos, hLt => by
    change SepEquiv
      (evalBagAt pcm env base stride
        (cond (Nat.ble m 1)
          (.node .empty 1 .empty)
          (cond (Nat.beq (Nat.mod m 2) 0)
            (.node (bagSingletonFuel d (Nat.div m 2)) 0 .empty)
            (.node .empty 0 (bagSingletonFuel d (Nat.div m 2))))))
      (env.get pcm (base + stride * m - 1))
    cases h1 : Nat.ble m 1 with
    | true =>
      have hm1 : m = 1 := Nat.le_antisymm (Nat.le_of_ble_eq_true h1) hPos
      subst hm1
      dsimp only [cond, evalBagAt, sepRepeat]
      rw [Nat.mul_one]
      exact sepEquiv_trans
        (sepEquiv_conj_congr pcm (sepConj_emp_right pcm _)
          (sepConj_emp_left pcm (sepEmp pcm)))
        (sepConj_emp_right pcm _)
    | false =>
      dsimp only [cond]
      have hGe2 : 2 ≤ m := by
        cases Nat.lt_or_ge m 2 with
        | inr hg => exact hg
        | inl hl =>
          have hbt := Nat.ble_eq_true_of_le (Nat.le_of_lt_succ hl)
          rw [h1] at hbt; cases hbt
      have hHalfPos : 0 < Nat.div m 2 :=
        (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hGe2
      have hHalfLt : Nat.div m 2 < bagPow2 d := by
        change m < 2 * bagPow2 d at hLt
        rw [Nat.mul_comm 2 (bagPow2 d)] at hLt
        exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hLt
      have hdm : 2 * Nat.div m 2 + Nat.mod m 2 = m := Nat.div_add_mod m 2
      have hModLt : Nat.mod m 2 < 2 := Nat.mod_lt m (Nat.succ_pos 1)
      cases hp : Nat.beq (Nat.mod m 2) 0 with
      | true =>
        have hz := Nat.eq_of_beq_eq_true hp
        rw [hz, Nat.add_zero] at hdm
        dsimp only [cond, evalBagAt, sepRepeat]
        have hStep :
            SepEquiv
              (sepConj pcm (sepEmp pcm)
                (sepConj pcm
                  (evalBagAt pcm env base (2 * stride)
                    (bagSingletonFuel d (Nat.div m 2)))
                  (sepEmp pcm)))
              (evalBagAt pcm env base (2 * stride)
                (bagSingletonFuel d (Nat.div m 2))) :=
          sepEquiv_trans (sepConj_emp_left pcm _) (sepConj_emp_right pcm _)
        have hIh := evalBagAt_singletonFuel pcm env d base (2 * stride)
          (Nat.div m 2) hHalfPos hHalfLt
        have hArith : base + (2 * stride) * Nat.div m 2 = base + stride * m := by
          rw [Nat.mul_comm 2 stride, Nat.mul_assoc stride 2 (Nat.div m 2), hdm]
        rw [hArith] at hIh
        exact sepEquiv_trans hStep hIh
      | false =>
        have hm1 : Nat.mod m 2 = 1 := by
          cases hmv : Nat.mod m 2 with
          | zero => rw [hmv] at hp; cases hp
          | succ r =>
            cases r with
            | zero => rfl
            | succ r' =>
              rw [hmv] at hModLt
              exact False.elim
                (Nat.not_lt_of_ge (Nat.le_add_left 2 r') hModLt)
        rw [hm1] at hdm
        dsimp only [cond, evalBagAt, sepRepeat]
        have hStep :
            SepEquiv
              (sepConj pcm (sepEmp pcm)
                (sepConj pcm (sepEmp pcm)
                  (evalBagAt pcm env (base + stride) (2 * stride)
                    (bagSingletonFuel d (Nat.div m 2)))))
              (evalBagAt pcm env (base + stride) (2 * stride)
                (bagSingletonFuel d (Nat.div m 2))) :=
          sepEquiv_trans (sepConj_emp_left pcm _) (sepConj_emp_left pcm _)
        have hIh := evalBagAt_singletonFuel pcm env d (base + stride) (2 * stride)
          (Nat.div m 2) hHalfPos hHalfLt
        have hArith :
            (base + stride) + (2 * stride) * Nat.div m 2 = base + stride * m := by
          rw [Nat.mul_comm 2 stride, Nat.mul_assoc stride 2 (Nat.div m 2),
            Nat.add_assoc base stride (stride * (2 * Nat.div m 2))]
          have hs :
              stride + stride * (2 * Nat.div m 2) =
                stride * (2 * Nat.div m 2 + 1) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          rw [hs, hdm]
        rw [hArith] at hIh
        exact sepEquiv_trans hStep hIh

private theorem bagPow2_20 : bagPow2 20 = 1048576 := rfl

private theorem sepExpr_eval_toBagAt {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) :
    ∀ (fuel : Nat) (e : SepExpr) (b : AtomBag),
      e.toBagAt fuel = some b →
      SepEquiv (e.eval pcm env) (evalBag pcm env b)
  | 0, _, _, h => by cases h
  | _ + 1, .emp, b, h => by
    injection h with hEq; subst hEq
    exact sepEquiv_refl _
  | _ + 1, .atom i, b, h => by
    change cond (Nat.blt (i + 1) 1048576) (some (AtomBag.singleton i)) none =
      some b at h
    cases hb : Nat.blt (i + 1) 1048576 with
    | false => rw [hb] at h; cases h
    | true =>
      rw [hb] at h; dsimp only [cond] at h
      injection h with hEq; subst hEq
      have hLt : i + 1 < bagPow2 20 := by
        rw [bagPow2_20]
        exact Nat.le_of_ble_eq_true hb
      have hSing := evalBagAt_singletonFuel pcm env 20 0 1 (i + 1)
        (Nat.succ_pos i) hLt
      rw [Nat.one_mul, Nat.zero_add] at hSing
      exact sepEquiv_symm hSing
  | d + 1, .star a b, out, h => by
    change (match a.toBagAt d with
        | none => none
        | some ba =>
          match b.toBagAt d with
          | none => none
          | some bb => AtomBag.addAt 21 ba bb) = some out at h
    cases ha : a.toBagAt d with
    | none => rw [ha] at h; cases h
    | some ba =>
      rw [ha] at h
      cases hb : b.toBagAt d with
      | none => rw [hb] at h; cases h
      | some bb =>
        rw [hb] at h
        exact sepEquiv_trans
          (sepEquiv_conj_congr pcm
            (sepExpr_eval_toBagAt pcm env d a ba ha)
            (sepExpr_eval_toBagAt pcm env d b bb hb))
          (sepEquiv_symm (evalBagAt_addAt pcm env 21 ba bb out 0 1 h))

/-- Certificate asserting AC-equivalence `lhs ≡ rhs` of two `SepExpr` formulas.
-/
structure SepACEquivCert where
  lhs : SepExpr
  rhs : SepExpr

/-- Computable reflective AC-equivalence checker for `SepExpr` (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`, `O(log N)` radix-bag
depth). -/
def sepACCheckEquiv (cert : SepACEquivCert) : Bool :=
  match cert.lhs.toBagAt 32 with
  | none => false
  | some bl =>
    match cert.rhs.toBagAt 32 with
    | none => false
    | some br => AtomBag.beq bl br

/-- Reflective AC-equivalence soundness sealed behind zero-`Prop`-argument
`BoolCertCut`. -/
theorem sepAC_equiv_of_boolCertCut {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) (lhs rhs : SepExpr)
    (hCert : BoolCertCut sepACCheckEquiv ⟨lhs, rhs⟩) :
    SepEquiv (lhs.eval pcm env) (rhs.eval pcm env) := by
  have hRaw : sepACCheckEquiv ⟨lhs, rhs⟩ = true := BoolCertCut.unseal hCert
  unfold sepACCheckEquiv at hRaw
  dsimp only at hRaw
  cases hl : lhs.toBagAt 32 with
  | none => rw [hl] at hRaw; cases hRaw
  | some bl =>
    rw [hl] at hRaw
    cases hr : rhs.toBagAt 32 with
    | none => rw [hr] at hRaw; cases hRaw
    | some br =>
      rw [hr] at hRaw
      have hEq : bl = br := atomBag_eq_of_beqAt hRaw
      subst hEq
      exact sepEquiv_trans (sepExpr_eval_toBagAt pcm env 32 lhs bl hl)
        (sepEquiv_symm (sepExpr_eval_toBagAt pcm env 32 rhs bl hr))

/-- Certificate asserting that canceling shared atoms from `lhs` and `rhs`
leaves residual formulas `lhsRem` and `rhsRem` up to AC permutation. -/
structure SepACCancelCert where
  lhs : SepExpr
  rhs : SepExpr
  lhsRem : SepExpr
  rhsRem : SepExpr

/-- Computable reflective multiset-frame canceler checker (`0` `noncomputable`,
`0` `._unsafe_rec`, `hasIR = true`, `O(log N)` radix-bag depth). -/
def sepACCheckCancel (cert : SepACCancelCert) : Bool :=
  match cert.lhs.toBagAt 32 with
  | none => false
  | some bl =>
    match cert.rhs.toBagAt 32 with
    | none => false
    | some br =>
      match cert.lhsRem.toBagAt 32 with
      | none => false
      | some blr =>
        match cert.rhsRem.toBagAt 32 with
        | none => false
        | some brr =>
          match AtomBag.cancelAt 21 bl br with
          | none => false
          | some res =>
            cond (AtomBag.beq res.1 blr) (AtomBag.beq res.2 brr) false

private theorem sepACCancel_decompose {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) (cert : SepACCancelCert)
    (hCert : BoolCertCut sepACCheckCancel cert) :
    ∃ common : AtomBag,
      SepEquiv (cert.lhs.eval pcm env)
        (sepConj pcm (evalBag pcm env common) (cert.lhsRem.eval pcm env)) ∧
      SepEquiv (cert.rhs.eval pcm env)
        (sepConj pcm (evalBag pcm env common) (cert.rhsRem.eval pcm env)) := by
  have hRaw : sepACCheckCancel cert = true := BoolCertCut.unseal hCert
  unfold sepACCheckCancel at hRaw
  cases hl : cert.lhs.toBagAt 32 with
  | none => rw [hl] at hRaw; cases hRaw
  | some bl =>
    rw [hl] at hRaw; dsimp only at hRaw
    cases hr : cert.rhs.toBagAt 32 with
    | none => rw [hr] at hRaw; cases hRaw
    | some br =>
      rw [hr] at hRaw; dsimp only at hRaw
      cases hlr : cert.lhsRem.toBagAt 32 with
      | none => rw [hlr] at hRaw; cases hRaw
      | some blr =>
        rw [hlr] at hRaw; dsimp only at hRaw
        cases hrr : cert.rhsRem.toBagAt 32 with
        | none => rw [hrr] at hRaw; cases hRaw
        | some brr =>
          rw [hrr] at hRaw; dsimp only at hRaw
          cases hc : AtomBag.cancelAt 21 bl br with
          | none => rw [hc] at hRaw; cases hRaw
          | some res =>
            rw [hc] at hRaw; dsimp only at hRaw
            cases h1 : AtomBag.beq res.1 blr with
            | false => rw [h1] at hRaw; cases hRaw
            | true =>
              rw [h1] at hRaw; dsimp only [cond] at hRaw
              have hEq1 : res.1 = blr := atomBag_eq_of_beqAt h1
              have hEq2 : res.2 = brr := atomBag_eq_of_beqAt hRaw
              let ⟨c, hcL, hcR⟩ :=
                evalBagAt_cancelAt pcm env 21 bl br res.1 res.2 0 1 hc
              rw [hEq1] at hcL
              rw [hEq2] at hcR
              refine ⟨c, ?_, ?_⟩
              · exact sepEquiv_trans
                  (sepExpr_eval_toBagAt pcm env 32 cert.lhs bl hl)
                  (sepEquiv_trans hcL
                    (sepEquiv_conj_congr pcm (sepEquiv_refl _)
                      (sepEquiv_symm
                        (sepExpr_eval_toBagAt pcm env 32 cert.lhsRem blr hlr))))
              · exact sepEquiv_trans
                  (sepExpr_eval_toBagAt pcm env 32 cert.rhs br hr)
                  (sepEquiv_trans hcR
                    (sepEquiv_conj_congr pcm (sepEquiv_refl _)
                      (sepEquiv_symm
                        (sepExpr_eval_toBagAt pcm env 32 cert.rhsRem brr hrr))))

/-- Reflective multiset-frame entailment cancellation sealed behind
`BoolCertCut`: reduces `lhs ⊢ rhs` to the residual obligation
`lhsRem ⊢ rhsRem` after canceling all shared atoms. -/
theorem sepAC_entails_of_boolCertCut {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) (lhs rhs lhsRem rhsRem : SepExpr)
    (hCert : BoolCertCut sepACCheckCancel ⟨lhs, rhs, lhsRem, rhsRem⟩)
    (hRem : SepEntails (lhsRem.eval pcm env) (rhsRem.eval pcm env)) :
    SepEntails (lhs.eval pcm env) (rhs.eval pcm env) := by
  let ⟨c, hcL, hcR⟩ :=
    sepACCancel_decompose pcm env ⟨lhs, rhs, lhsRem, rhsRem⟩ hCert
  intro m hm
  exact (hcR m).mpr
    (sepConj_mono pcm (SepEntails.refl _) hRem m ((hcL m).mp hm))

/-- Reflective frame-preserving update cancellation sealed behind
`BoolCertCut`: lifts any `FramePreserving pcm lhsRem rhsRem` update across all
canceled frame atoms in `lhs` and `rhs`. -/
theorem sepAC_framePreserving_of_boolCertCut {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) (lhs rhs lhsRem rhsRem : SepExpr)
    (hCert : BoolCertCut sepACCheckCancel ⟨lhs, rhs, lhsRem, rhsRem⟩)
    (hFP : FramePreserving pcm (lhsRem.eval pcm env) (rhsRem.eval pcm env)) :
    FramePreserving pcm (lhs.eval pcm env) (rhs.eval pcm env) := by
  let ⟨c, hcL, hcR⟩ :=
    sepACCancel_decompose pcm env ⟨lhs, rhs, lhsRem, rhsRem⟩ hCert
  have hFramed := FramePreserving.frame (evalBag pcm env c) hFP
  intro h₁ hf hComb hL hop
  have hSwapped : sepConj pcm (lhsRem.eval pcm env) (evalBag pcm env c) h₁ :=
    (sepConj_comm pcm _ _ h₁).mp ((hcL h₁).mp hL)
  let ⟨h₁', hComb', hop', hPost⟩ := hFramed h₁ hf hComb hSwapped hop
  exact ⟨h₁', hComb', hop', (hcR h₁').mpr ((sepConj_comm pcm _ _ h₁').mp hPost)⟩

/-- Certificate asserting that `avail` splits up to AC into `req ∗ frame`. -/
structure SepACFrameCert where
  avail : SepExpr
  req : SepExpr
  frame : SepExpr

/-- Computable reflective frame-split checker (`avail ≡ req ∗ frame`). -/
def sepACCheckFrame (cert : SepACFrameCert) : Bool :=
  sepACCheckEquiv ⟨cert.avail, .star cert.req cert.frame⟩

/-- Extracts a `SepEquiv` frame split `avail ≡ req ∗ frame` from a sealed
`BoolCertCut sepACCheckFrame` certificate. -/
theorem sepAC_frame_split_of_boolCertCut {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) (avail req frame : SepExpr)
    (hCert : BoolCertCut sepACCheckFrame ⟨avail, req, frame⟩) :
    SepEquiv (avail.eval pcm env)
      (sepConj pcm (req.eval pcm env) (frame.eval pcm env)) := by
  have hRaw : sepACCheckFrame ⟨avail, req, frame⟩ = true :=
    BoolCertCut.unseal hCert
  exact sepAC_equiv_of_boolCertCut pcm env avail (.star req frame)
    (BoolCertCut.seal sepACCheckEquiv ⟨avail, .star req frame⟩ hRaw)

private def mkSepTreeAsc : Nat → Nat → Nat → SepExpr :=
  @Nat.rec (fun _ => Nat → Nat → SepExpr)
    (fun start _ => .atom start)
    (fun _ ih start half =>
      .star (ih start (Nat.div half 2)) (ih (start + half) (Nat.div half 2)))

private def mkSepTreeDesc : Nat → Nat → Nat → SepExpr :=
  @Nat.rec (fun _ => Nat → Nat → SepExpr)
    (fun start _ => .atom start)
    (fun _ ih start half =>
      .star (ih (start + half) (Nat.div half 2)) (ih start (Nat.div half 2)))

/-- 256-atom balanced reversed-tree `SepAC` AC-equivalence canary discharged by
`BoolCertCut` + `rfl`. -/
theorem sepAC_256_equiv_canary {M : Type} (pcm : ExplPCM M)
    (env : SepAtomTree M) :
    SepEquiv ((mkSepTreeAsc 8 0 128).eval pcm env)
      ((mkSepTreeDesc 8 0 128).eval pcm env) :=
  sepAC_equiv_of_boolCertCut pcm env
    (mkSepTreeAsc 8 0 128) (mkSepTreeDesc 8 0 128)
    (BoolCertCut.seal sepACCheckEquiv
      ⟨mkSepTreeAsc 8 0 128, mkSepTreeDesc 8 0 128⟩ rfl)

/-- Positive and negative `SepAC` partial frame-cancellation canaries: 256-atom
shared frame cancellation, concrete `byteHeapletPCM` framed byte update, and
fail-closed rejection on mismatched multisets. -/
theorem sepAC_frame_cancel_canary :
    (∀ {M : Type} (pcm : ExplPCM M) (env : SepAtomTree M),
      SepEntails (env.get pcm 300) (env.get pcm 301) →
      SepEntails
        ((SepExpr.star (mkSepTreeAsc 8 0 128) (.atom 300)).eval pcm env)
        ((SepExpr.star (.atom 301) (mkSepTreeDesc 8 0 128)).eval pcm env)) ∧
    FramePreserving byteHeapletPCM
      (sepConj byteHeapletPCM
        (sepConj byteHeapletPCM
          (bytePointsTo ⟨1, 0⟩ (.init 0x33 none))
          (bytePointsTo ⟨0, 0⟩ (.init 0x11 none)))
        (bytePointsTo ⟨2, 0⟩ (.init 0x44 none)))
      (sepConj byteHeapletPCM
        (bytePointsTo ⟨2, 0⟩ (.init 0x44 none))
        (sepConj byteHeapletPCM
          (bytePointsTo ⟨0, 0⟩ (.init 0x7a none))
          (bytePointsTo ⟨1, 0⟩ (.init 0x33 none)))) ∧
    sepACCheckEquiv ⟨.star (.atom 0) (.atom 1), .star (.atom 0) (.atom 2)⟩ =
      false := by
  refine ⟨fun pcm env hEnt =>
      sepAC_entails_of_boolCertCut pcm env
        (.star (mkSepTreeAsc 8 0 128) (.atom 300))
        (.star (.atom 301) (mkSepTreeDesc 8 0 128))
        (.atom 300) (.atom 301)
        (BoolCertCut.seal sepACCheckCancel
          ⟨.star (mkSepTreeAsc 8 0 128) (.atom 300),
           .star (.atom 301) (mkSepTreeDesc 8 0 128),
           .atom 300, .atom 301⟩ rfl)
        hEnt,
    ?_, rfl⟩
  let env : SepAtomTree ByteHeaplet :=
    SepAtomTree.ofList
      [bytePointsTo ⟨0, 0⟩ (.init 0x11 none),
       bytePointsTo ⟨1, 0⟩ (.init 0x33 none),
       bytePointsTo ⟨2, 0⟩ (.init 0x44 none),
       bytePointsTo ⟨0, 0⟩ (.init 0x7a none)]
  exact sepAC_framePreserving_of_boolCertCut byteHeapletPCM env
    (.star (.star (.atom 1) (.atom 0)) (.atom 2))
    (.star (.atom 2) (.star (.atom 3) (.atom 1)))
    (.atom 0) (.atom 3)
    (BoolCertCut.seal sepACCheckCancel
      ⟨.star (.star (.atom 1) (.atom 0)) (.atom 2),
       .star (.atom 2) (.star (.atom 3) (.atom 1)),
       .atom 0, .atom 3⟩ rfl)
    (bytePointsTo_framePreserving_update ⟨0, 0⟩
      (.init 0x11 none) (.init 0x7a none))

end Anneal.Core
