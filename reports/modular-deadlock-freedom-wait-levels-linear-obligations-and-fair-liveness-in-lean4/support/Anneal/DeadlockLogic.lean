-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.SimpLemmas
import Init.Tactics

namespace Anneal.DeadlockLogic

noncomputable def chooseBool (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : Bool :=
  (Classical.choice h).1

theorem chooseBool_spec (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : P (chooseBool P h) :=
  (Classical.choice h).2

theorem chooseBool_congr {P Q : Bool → Prop} (hPQ : P = Q)
    (hP : Nonempty (Subtype P))
    (hQ : Nonempty (Subtype Q)) :
    chooseBool P hP = chooseBool Q hQ := by
  subst hPQ
  rfl

theorem prop_em (p : Prop) : p ∨ ¬ p := by
  let U (x : Bool) : Prop := x = true ∨ p
  let V (x : Bool) : Prop := x = false ∨ p
  have exU : Nonempty (Subtype U) := ⟨⟨true, Or.inl rfl⟩⟩
  have exV : Nonempty (Subtype V) := ⟨⟨false, Or.inl rfl⟩⟩
  have hu : U (chooseBool U exU) := chooseBool_spec U exU
  have hv : V (chooseBool V exV) := chooseBool_spec V exV
  cases Decidable.em (chooseBool U exU = chooseBool V exV) with
  | inr hne =>
    refine Or.inr ?_
    intro hp
    have hUV : U = V := by
      funext x
      exact propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    exact hne (chooseBool_congr hUV exU exV)
  | inl heq =>
    cases hu with
    | inr hp => exact Or.inl hp
    | inl hut =>
      cases hv with
      | inr hp => exact Or.inl hp
      | inl hvf =>
        rw [hut, hvf] at heq
        nomatch heq

abbrev ObjId : Type := Nat
abbrev UnitId : Type := Nat
abbrev CarrierId : Type := Nat

structure StrictDAG (Level : Type) (prec : Level → Level → Prop) : Prop where
  irrefl : ∀ l : Level, ¬ prec l l
  trans : ∀ {a b c : Level}, prec a b → prec b c → prec a c

theorem strictDAG_asymm {Level : Type} {prec : Level → Level → Prop}
    (dag : StrictDAG Level prec) {a b : Level}
    (hab : prec a b) (hba : prec b a) : False :=
  dag.irrefl a (dag.trans hab hba)

theorem strictDAG_has_maximal {Level : Type} {prec : Level → Level → Prop}
    (dag : StrictDAG Level prec) :
    ∀ (hd : Level) (tl : List Level),
      ∃ m : Level, m ∈ (hd :: tl) ∧ ∀ x : Level, x ∈ (hd :: tl) → ¬ prec m x := by
  intro hd tl
  induction tl generalizing hd with
  | nil =>
    refine ⟨hd, List.Mem.head [], ?_⟩
    intro x hx
    cases hx with
    | head => exact dag.irrefl hd
    | tail _ hnil => nomatch hnil
  | cons b rest ih =>
    cases ih b with
    | intro m hm =>
      cases prop_em (prec m hd) with
      | inl hmhd =>
        refine ⟨hd, List.Mem.head _, ?_⟩
        intro x hx
        cases hx with
        | head => exact dag.irrefl hd
        | tail _ hxb =>
          intro hhd_x
          exact hm.2 x hxb (dag.trans hmhd hhd_x)
      | inr hnmhd =>
        refine ⟨m, List.Mem.tail hd hm.1, ?_⟩
        intro x hx
        cases hx with
        | head => exact hnmhd
        | tail _ hxb => exact hm.2 x hxb

inductive CarrierBinding where
  | osBound
  | taskMovable

/-- Channel mode: strictly partitions bounded channels into
`.creditManaged` (capacity slots conserved by `.chanCapSlot` linear tokens)
and `.levelOrdered` (blocking send/recv ordered by `AllBelow`, zero slots). -/
inductive ChannelMode where
  | creditManaged
  | levelOrdered

inductive TokenKind where
  | mutexGuard
  | rwWriteGuard
  | rwReadGuard
  | rwUpgradableGuard
  | onceInitGuard
  | condvarSignalOb
  | barrierTicket
  | chanCreditSendOb
  | chanCreditRecvOb
  | chanBlockingSendOb
  | chanBlockingRecvOb
  | joinExitOb
  | asyncMutexGuard

/-- Unified linear token: either a level-ordered guard/obligation
(`.ordered`) on which waiters may block, or a pure bounded-channel capacity-slot
credit (`.chanCapSlot id_ch`) certifying non-blocking buffer space in a
`.creditManaged` `sync_channel(C)`. -/
inductive LinearToken (Level : Type) where
  | ordered (obj : ObjId) (level : Level) (kind : TokenKind)
      (binding : CarrierBinding)
  | chanCapSlot (id_ch : ObjId)

noncomputable def tokensLevels {Level : Type} :
    List (LinearToken Level) → List Level
  | [] => []
  | .ordered _ lvl _ _ :: rest => lvl :: tokensLevels rest
  | .chanCapSlot _ :: rest => tokensLevels rest

noncomputable def tokensAmbient {Level : Type} :
    List (LinearToken Level) → List (Level × CarrierBinding)
  | [] => []
  | .ordered _ lvl _ b :: rest => (lvl, b) :: tokensAmbient rest
  | .chanCapSlot _ :: rest => tokensAmbient rest

noncomputable def ambientLevels {Level : Type} :
    List (Level × CarrierBinding) → List Level
  | [] => []
  | (lvl, _) :: rest => lvl :: ambientLevels rest

theorem ambientLevels_append {Level : Type}
    (xs ys : List (Level × CarrierBinding)) :
    ambientLevels (xs ++ ys) = ambientLevels xs ++ ambientLevels ys := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk lvl b =>
      dsimp [ambientLevels]
      rw [ih]

theorem ambientLevels_tokensAmbient {Level : Type}
    (ts : List (LinearToken Level)) :
    ambientLevels (tokensAmbient ts) = tokensLevels ts := by
  induction ts with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | ordered obj lvl k b =>
      dsimp [tokensAmbient, ambientLevels, tokensLevels]
      rw [ih]
    | chanCapSlot id =>
      dsimp [tokensAmbient, tokensLevels]
      exact ih

theorem tokensLevels_append {Level : Type}
    (xs ys : List (LinearToken Level)) :
    tokensLevels (xs ++ ys) = tokensLevels xs ++ tokensLevels ys := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | ordered _ _ _ _ =>
      dsimp [tokensLevels]
      rw [ih]
    | chanCapSlot _ =>
      dsimp [tokensLevels]
      exact ih

theorem ordered_mem_tokensLevels {Level : Type}
    {obj : ObjId} {lvl : Level} {k : TokenKind} {b : CarrierBinding}
    {held : List (LinearToken Level)}
    (hmem : LinearToken.ordered obj lvl k b ∈ held) :
    lvl ∈ tokensLevels held := by
  induction held with
  | nil => nomatch hmem
  | cons hd tl ih =>
    cases hd with
    | ordered _ _ _ _ =>
      cases hmem with
      | head => exact List.Mem.head _
      | tail _ htl => exact List.Mem.tail _ (ih htl)
    | chanCapSlot _ =>
      cases hmem with
      | tail _ htl => exact ih htl

def AllBelow {Level : Type} (prec : Level → Level → Prop)
    (lvls : List Level) (target : Level) : Prop :=
  ∀ l : Level, l ∈ lvls → prec l target

theorem mem_append_left {α : Type} {l : α} {xs ys : List α}
    (hl : l ∈ xs) : l ∈ xs ++ ys := by
  induction xs with
  | nil => nomatch hl
  | cons _ _ ih =>
    cases hl with
    | head => exact List.Mem.head _
    | tail _ htl => exact List.Mem.tail _ (ih htl)

theorem mem_append_right {α : Type} {l : α} {xs ys : List α}
    (hl : l ∈ ys) : l ∈ xs ++ ys := by
  induction xs with
  | nil => exact hl
  | cons _ _ ih => exact List.Mem.tail _ ih

theorem mem_append_or {α : Type} {x : α} {xs ys : List α}
    (h : x ∈ xs ++ ys) : x ∈ xs ∨ x ∈ ys := by
  induction xs with
  | nil => exact Or.inr h
  | cons a rest ih =>
    cases h with
    | head => exact Or.inl (List.Mem.head rest)
    | tail _ htl =>
      cases ih htl with
      | inl hl => exact Or.inl (List.Mem.tail a hl)
      | inr hr => exact Or.inr hr

theorem allBelow_of_append_left {Level : Type} {prec : Level → Level → Prop}
    {xs ys : List Level} {target : Level}
    (h : AllBelow prec (xs ++ ys) target) :
    AllBelow prec xs target :=
  fun l hl => h l (mem_append_left hl)

theorem allBelow_of_append_right {Level : Type} {prec : Level → Level → Prop}
    {xs ys : List Level} {target : Level}
    (h : AllBelow prec (xs ++ ys) target) :
    AllBelow prec ys target :=
  fun l hl => h l (mem_append_right hl)

theorem allBelow_append {Level : Type} {prec : Level → Level → Prop}
    {xs ys : List Level} {target : Level}
    (hx : AllBelow prec xs target) (hy : AllBelow prec ys target) :
    AllBelow prec (xs ++ ys) target := by
  intro l hl
  cases mem_append_or hl with
  | inl h1 => exact hx l h1
  | inr h2 => exact hy l h2

def HasNoOsBound {Level : Type} (tokens : List (LinearToken Level)) : Prop :=
  @List.rec (LinearToken Level) (fun _ => Prop)
    True
    (fun tok _ ih =>
      match tok with
      | .ordered _ _ _ b => b = .taskMovable ∧ ih
      | .chanCapSlot _ => ih)
    tokens

def HasNoOsBoundAmbient {Level : Type}
    (amb : List (Level × CarrierBinding)) : Prop :=
  @List.rec (Level × CarrierBinding) (fun _ => Prop)
    True
    (fun entry _ ih => entry.2 = .taskMovable ∧ ih)
    amb

theorem hasNoOsBound_append {Level : Type}
    {xs ys : List (LinearToken Level)}
    (hx : HasNoOsBound xs) (hy : HasNoOsBound ys) :
    HasNoOsBound (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons hd tl ih =>
    cases hd with
    | ordered _ _ _ _ => exact ⟨hx.1, ih hx.2⟩
    | chanCapSlot _ => exact ih hx

theorem hasNoOsBoundAmbient_append {Level : Type}
    {xs ys : List (Level × CarrierBinding)}
    (hx : HasNoOsBoundAmbient xs) (hy : HasNoOsBoundAmbient ys) :
    HasNoOsBoundAmbient (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons hd tl ih =>
    cases hd with
    | mk _ _ => exact ⟨hx.1, ih hx.2⟩

theorem hasNoOsBoundAmbient_right {Level : Type}
    {xs ys : List (Level × CarrierBinding)}
    (h : HasNoOsBoundAmbient (xs ++ ys)) : HasNoOsBoundAmbient ys := by
  induction xs with
  | nil => exact h
  | cons hd tl ih =>
    cases hd with
    | mk _ _ => exact ih h.2

theorem hasNoOsBound_implies_ambient {Level : Type}
    {ts : List (LinearToken Level)} (h : HasNoOsBound ts) :
    HasNoOsBoundAmbient (tokensAmbient ts) := by
  induction ts with
  | nil => exact True.intro
  | cons hd tl ih =>
    cases hd with
    | ordered _ _ _ _ => exact ⟨h.1, ih h.2⟩
    | chanCapSlot _ => exact ih h

def HasHeldTokenOfKind {Level : Type} (tokens : List (LinearToken Level))
    (id : ObjId) (kind : TokenKind) : Prop :=
  @List.rec (LinearToken Level) (fun _ => Prop)
    False
    (fun tok _ ih =>
      match tok with
      | .ordered obj _ k _ => (obj = id ∧ k = kind) ∨ ih
      | .chanCapSlot _ => ih)
    tokens

def HoldsSameRwRead {Level : Type} (id : ObjId)
    (tokens : List (LinearToken Level)) : Prop :=
  @List.rec (LinearToken Level) (fun _ => Prop)
    False
    (fun tok _ ih =>
      match tok with
      | .ordered obj _ k _ =>
          (obj = id ∧
            (k = .rwReadGuard ∨ k = .rwUpgradableGuard ∨
             k = .rwWriteGuard)) ∨
          ih
      | .chanCapSlot _ => ih)
    tokens

noncomputable def removeFirstToken {Level : Type}
    (pred : LinearToken Level → Bool) :
    List (LinearToken Level) →
      Option (LinearToken Level × List (LinearToken Level))
  | [] => none
  | tok :: rest =>
      if pred tok then some (tok, rest)
      else match removeFirstToken pred rest with
        | some (found, rem) => some (found, tok :: rem)
        | none => none

theorem removeFirstToken_sub {Level : Type}
    {pred : LinearToken Level → Bool}
    {xs rem : List (LinearToken Level)} {found : LinearToken Level}
    (h : removeFirstToken pred xs = some (found, rem)) :
    found ∈ xs ∧ ∀ y : LinearToken Level, y ∈ rem → y ∈ xs := by
  induction xs generalizing rem with
  | nil => nomatch h
  | cons hd tl ih =>
    unfold removeFirstToken at h
    cases hp : pred hd with
    | true =>
      rw [hp] at h
      dsimp at h
      injection h with hpair
      injection hpair with hf hrem
      subst hf; subst hrem
      exact ⟨List.Mem.head tl, fun y hy => List.Mem.tail hd hy⟩
    | false =>
      rw [hp] at h
      dsimp at h
      cases hr : removeFirstToken pred tl with
      | none => rw [hr] at h; nomatch h
      | some pr =>
        rw [hr] at h
        dsimp at h
        injection h with hpair
        injection hpair with hf hrem
        subst hf; subst hrem
        have sub := ih hr
        refine ⟨List.Mem.tail hd sub.1, ?_⟩
        intro y hy
        cases hy with
        | head => exact List.Mem.head tl
        | tail _ hytl => exact List.Mem.tail hd (sub.2 y hytl)

theorem removeFirstToken_other_mem_rem {Level : Type}
    {pred : LinearToken Level → Bool}
    {held rem : List (LinearToken Level)} {found tok : LinearToken Level}
    (hrem : removeFirstToken pred held = some (found, rem))
    (htok : tok ∈ held)
    (hne : tok ≠ found) :
    tok ∈ rem := by
  induction held generalizing rem with
  | nil => nomatch htok
  | cons hd tl ih =>
    unfold removeFirstToken at hrem
    cases hp : pred hd with
    | true =>
      rw [hp] at hrem
      dsimp at hrem
      injection hrem with hpair
      injection hpair with hf hr
      subst hf; subst hr
      cases htok with
      | head => exact False.elim (hne rfl)
      | tail _ htl => exact htl
    | false =>
      rw [hp] at hrem
      dsimp at hrem
      cases hrec : removeFirstToken pred tl with
      | none => rw [hrec] at hrem; nomatch hrem
      | some pr =>
        rw [hrec] at hrem
        dsimp at hrem
        injection hrem with hpair
        injection hpair with hf hr
        subst hf; subst hr
        cases htok with
        | head => exact List.Mem.head _
        | tail _ htl => exact List.Mem.tail hd (ih hrec htl)

/-! ### Algebraic Slot Conservation for `.creditManaged` `sync_channel(C)` -/

noncomputable def countCapSlotsInList {Level : Type} (id_ch : ObjId) :
    List (LinearToken Level) → Nat
  | [] => 0
  | .chanCapSlot id :: rest =>
      (if Nat.beq id id_ch then 1 else 0) + countCapSlotsInList id_ch rest
  | .ordered _ _ _ _ :: rest => countCapSlotsInList id_ch rest

theorem countCapSlotsInList_append {Level : Type} (id_ch : ObjId)
    (xs ys : List (LinearToken Level)) :
    countCapSlotsInList id_ch (xs ++ ys) =
      countCapSlotsInList id_ch xs + countCapSlotsInList id_ch ys := by
  induction xs with
  | nil =>
    dsimp [countCapSlotsInList]
    rw [Nat.zero_add]
  | cons hd tl ih =>
    cases hd with
    | ordered _ _ _ _ =>
      dsimp [countCapSlotsInList]
      exact ih
    | chanCapSlot id =>
      dsimp [countCapSlotsInList]
      rw [ih, Nat.add_assoc]

theorem countCapSlotsInList_removeOrdered {Level : Type}
    {pred : LinearToken Level → Bool}
    {xs rem : List (LinearToken Level)}
    {obj : ObjId} {lvl : Level} {k : TokenKind} {b : CarrierBinding}
    (id_ch : ObjId)
    (hrem : removeFirstToken pred xs = some (.ordered obj lvl k b, rem)) :
    countCapSlotsInList id_ch xs = countCapSlotsInList id_ch rem := by
  induction xs generalizing rem with
  | nil => nomatch hrem
  | cons hd tl ih =>
    unfold removeFirstToken at hrem
    cases hp : pred hd with
    | true =>
      rw [hp] at hrem; dsimp at hrem
      injection hrem with hpair
      injection hpair with hf hr
      subst hf; subst hr
      rfl
    | false =>
      rw [hp] at hrem; dsimp at hrem
      cases hrec : removeFirstToken pred tl with
      | none => rw [hrec] at hrem; nomatch hrem
      | some pr =>
        cases pr with
        | mk p1 p2 =>
          rw [hrec] at hrem; dsimp at hrem
          injection hrem with hpair
          injection hpair with hf hr
          subst hf; subst hr
          cases hd with
          | ordered _ _ _ _ =>
            dsimp [countCapSlotsInList]
            exact ih hrec
          | chanCapSlot id =>
            dsimp [countCapSlotsInList]
            rw [ih hrec]

theorem countCapSlotsInList_removeCapSlot {Level : Type}
    {pred : LinearToken Level → Bool}
    {xs rem : List (LinearToken Level)} {id_rm : ObjId}
    (id_ch : ObjId)
    (hrem : removeFirstToken pred xs = some (.chanCapSlot id_rm, rem)) :
    countCapSlotsInList id_ch xs =
      (if Nat.beq id_rm id_ch then 1 else 0) + countCapSlotsInList id_ch rem := by
  induction xs generalizing rem with
  | nil => nomatch hrem
  | cons hd tl ih =>
    unfold removeFirstToken at hrem
    cases hp : pred hd with
    | true =>
      rw [hp] at hrem; dsimp at hrem
      injection hrem with hpair
      injection hpair with hf hr
      subst hf; subst hr
      rfl
    | false =>
      rw [hp] at hrem; dsimp at hrem
      cases hrec : removeFirstToken pred tl with
      | none => rw [hrec] at hrem; nomatch hrem
      | some pr =>
        cases pr with
        | mk p1 p2 =>
          rw [hrec] at hrem; dsimp at hrem
          injection hrem with hpair
          injection hpair with hf hr
          subst hf; subst hr
          cases hd with
          | ordered _ _ _ _ =>
            dsimp [countCapSlotsInList]
            exact ih hrec
          | chanCapSlot id =>
            dsimp [countCapSlotsInList]
            rw [ih hrec, Nat.add_left_comm]

structure CreditChannelState where
  cap : Nat
  freeSlots : Nat
  bufferedMsgs : Nat

def CreditChannelInv (s : CreditChannelState) : Prop :=
  s.freeSlots + s.bufferedMsgs = s.cap

inductive CreditChannelStep : CreditChannelState → CreditChannelState → Prop where
  | chanCreditSend (cap f b : Nat) :
      CreditChannelStep ⟨cap, f + 1, b⟩ ⟨cap, f, b + 1⟩
  | chanCreditRecv (cap f b : Nat) :
      CreditChannelStep ⟨cap, f, b + 1⟩ ⟨cap, f + 1, b⟩

inductive CreditChannelSteps : CreditChannelState → CreditChannelState → Prop where
  | refl (s : CreditChannelState) : CreditChannelSteps s s
  | tail {s₁ s₂ s₃ : CreditChannelState} :
      CreditChannelSteps s₁ s₂ →
      CreditChannelStep s₂ s₃ →
      CreditChannelSteps s₁ s₃

/-- Explicit algebraic slot-conservation theorem:
for any `.creditManaged` `sync_channel(C)` initialized with `C` free slot
credits and `0` buffered messages (`⟨C, C, 0⟩`), EVERY sequence of
`chanCreditSend` (consuming 1 `.chanCapSlot`, enqueueing 1 message) and
`chanCreditRecv` (dequeueing 1 message, minting 1 `.chanCapSlot`) preserves
`freeSlots + bufferedMsgs = C`; moreover, holding at least 1 `.chanCapSlot`
(`freeSlots ≥ 1`) guarantees `bufferedMsgs < C` (strictly non-blocking send!). -/
theorem creditChannel_slot_conservation (C : Nat) :
    CreditChannelInv ⟨C, C, 0⟩ ∧
    (∀ s₁ s₂, CreditChannelInv s₁ → CreditChannelStep s₁ s₂ → CreditChannelInv s₂) ∧
    (∀ s, CreditChannelSteps ⟨C, C, 0⟩ s →
      s.freeSlots + s.bufferedMsgs = C ∧
      (1 ≤ s.freeSlots → s.bufferedMsgs < C)) := by
  have hstep : ∀ s₁ s₂, CreditChannelInv s₁ → CreditChannelStep s₁ s₂ →
      CreditChannelInv s₂ := by
    intro s₁ s₂ hinv hs
    cases hs with
    | chanCreditSend cap f b =>
      unfold CreditChannelInv at hinv
      unfold CreditChannelInv
      dsimp at hinv
      dsimp
      rw [Nat.add_right_comm f 1 b] at hinv
      rw [Nat.add_assoc f b 1] at hinv
      exact hinv
    | chanCreditRecv cap f b =>
      unfold CreditChannelInv at hinv
      unfold CreditChannelInv
      dsimp at hinv
      dsimp
      rw [Nat.add_right_comm f 1 b, Nat.add_assoc f b 1]
      exact hinv
  refine ⟨Nat.add_zero C, hstep, ?_⟩
  intro s hsteps
  have hinv : CreditChannelInv s ∧ s.cap = C := by
    induction hsteps with
    | refl => exact ⟨Nat.add_zero C, rfl⟩
    | tail _ hs ih =>
      refine ⟨hstep _ _ ih.1 hs, ?_⟩
      cases hs <;> exact ih.2
  have hsum : s.freeSlots + s.bufferedMsgs = C := Eq.trans hinv.1 hinv.2
  refine ⟨hsum, ?_⟩
  intro hge
  have hlt1 : s.bufferedMsgs < 1 + s.bufferedMsgs := by
    rw [Nat.add_comm 1 s.bufferedMsgs]
    exact Nat.lt_succ_self s.bufferedMsgs
  have hle : 1 + s.bufferedMsgs ≤ s.freeSlots + s.bufferedMsgs :=
    Nat.add_le_add_right hge s.bufferedMsgs
  rw [hsum] at hle
  exact Nat.lt_of_lt_of_le hlt1 hle

/-! ### Abstract World Deadlock-Freedom Foundation -/

inductive UnitWait (Level : Type) where
  | running (carrier : CarrierId)
  | readyQueue
  | osBlocked (carrier : CarrierId) (obj : ObjId) (waitLvl : Level)
  | coopBlocked (obj : ObjId) (waitLvl : Level)
  | finished

structure ExecUnit (Level : Type) where
  uid : UnitId
  held : List (LinearToken Level)
  wait : UnitWait Level

def unitWaitLevel? {Level : Type} (u : ExecUnit Level) : Option (ObjId × Level) :=
  match u.wait with
  | .osBlocked _ obj lvl => some (obj, lvl)
  | .coopBlocked obj lvl => some (obj, lvl)
  | _ => none

def unitIsBlocked {Level : Type} (u : ExecUnit Level) : Prop :=
  ∃ obj lvl, unitWaitLevel? u = some (obj, lvl)

def unitHoldsFor {Level : Type} (u : ExecUnit Level)
    (obj : ObjId) (lvl : Level) : Prop :=
  u.wait ≠ .finished ∧
  ∃ k : TokenKind, ∃ b : CarrierBinding,
    LinearToken.ordered obj lvl k b ∈ u.held

structure WellTypedWorld {Level : Type} (prec : Level → Level → Prop)
    (units : List (ExecUnit Level)) : Prop where
  finished_empty :
    ∀ u : ExecUnit Level, u ∈ units → u.wait = .finished → u.held = []
  live_fulfiller :
    ∀ (u : ExecUnit Level) (obj : ObjId) (lvl : Level),
      u ∈ units →
      unitWaitLevel? u = some (obj, lvl) →
      ∃ v : ExecUnit Level, v ∈ units ∧ unitHoldsFor v obj lvl
  strict_wait_order :
    ∀ (u : ExecUnit Level) (obj : ObjId) (lvl : Level),
      u ∈ units →
      unitWaitLevel? u = some (obj, lvl) →
      AllBelow prec (tokensLevels u.held) lvl
  clean_yield :
    ∀ u : ExecUnit Level, u ∈ units →
      (u.wait = .readyQueue ∨ ∃ obj lvl, u.wait = .coopBlocked obj lvl) →
      HasNoOsBound u.held

def IsClosedBlockedSet {Level : Type} (units : List (ExecUnit Level))
    (S : ExecUnit Level → Prop) : Prop :=
  (∃ u₀ : ExecUnit Level, u₀ ∈ units ∧ S u₀) ∧
  (∀ u : ExecUnit Level, u ∈ units → S u → unitIsBlocked u) ∧
  (∀ (u v : ExecUnit Level) (obj : ObjId) (lvl : Level),
    u ∈ units → S u →
    unitWaitLevel? u = some (obj, lvl) →
    v ∈ units → unitHoldsFor v obj lvl → S v)

theorem collect_S_waitLevels {Level : Type}
    (units : List (ExecUnit Level)) (S : ExecUnit Level → Prop)
    (h_blk : ∀ u : ExecUnit Level, u ∈ units → S u → unitIsBlocked u) :
    ∃ lvls : List Level,
      (∀ u obj lvl, u ∈ units → S u → unitWaitLevel? u = some (obj, lvl) → lvl ∈ lvls) ∧
      (∀ lvl, lvl ∈ lvls → ∃ u obj, u ∈ units ∧ S u ∧ unitWaitLevel? u = some (obj, lvl)) := by
  induction units with
  | nil =>
    refine ⟨[], ?_, ?_⟩
    · intro u _ _ hmem; nomatch hmem
    · intro lvl hmem; nomatch hmem
  | cons hd tl ih =>
    have h_blk_tl : ∀ u, u ∈ tl → S u → unitIsBlocked u :=
      fun u hu hs => h_blk u (List.Mem.tail hd hu) hs
    cases ih h_blk_tl with
    | intro lvlsTl hTl =>
      cases prop_em (S hd) with
      | inl hShd =>
        have hb : unitIsBlocked hd := h_blk hd (List.Mem.head tl) hShd
        cases hb with
        | intro obj₀ hrest =>
          cases hrest with
          | intro lvl₀ hw₀ =>
            refine ⟨lvl₀ :: lvlsTl, ?_, ?_⟩
            · intro u obj lvl hu hSu hwu
              cases hu with
              | head =>
                rw [hw₀] at hwu
                injection hwu with hpair
                injection hpair with _ hlvl
                subst hlvl
                exact List.Mem.head lvlsTl
              | tail _ hutl =>
                exact List.Mem.tail lvl₀ (hTl.1 u obj lvl hutl hSu hwu)
            · intro lvl hlvl
              cases hlvl with
              | head =>
                exact ⟨hd, obj₀, List.Mem.head tl, hShd, hw₀⟩
              | tail _ hltl =>
                cases hTl.2 lvl hltl with
                | intro u hrest2 =>
                  cases hrest2 with
                  | intro obj hu =>
                    exact ⟨u, obj, List.Mem.tail hd hu.1, hu.2.1, hu.2.2⟩
      | inr hnShd =>
        refine ⟨lvlsTl, ?_, ?_⟩
        · intro u obj lvl hu hSu hwu
          cases hu with
          | head => exact False.elim (hnShd hSu)
          | tail _ hutl => exact hTl.1 u obj lvl hutl hSu hwu
        · intro lvl hlvl
          cases hTl.2 lvl hlvl with
          | intro u hrest2 =>
            cases hrest2 with
            | intro obj hu =>
              exact ⟨u, obj, List.Mem.tail hd hu.1, hu.2.1, hu.2.2⟩

theorem wellTypedWorld_no_closedBlockedSet {Level : Type}
    {prec : Level → Level → Prop}
    (dag : StrictDAG Level prec)
    {units : List (ExecUnit Level)}
    (hwt : WellTypedWorld prec units) :
    ∀ S : ExecUnit Level → Prop, ¬ IsClosedBlockedSet units S := by
  intro S hclosed
  cases collect_S_waitLevels units S hclosed.2.1 with
  | intro lvls hlvls =>
    cases hclosed.1 with
    | intro u₀ hu₀ =>
      cases hclosed.2.1 u₀ hu₀.1 hu₀.2 with
      | intro obj₀ hrest₀ =>
        cases hrest₀ with
        | intro lvl₀ hw₀ =>
          have hmem₀ : lvl₀ ∈ lvls := hlvls.1 u₀ obj₀ lvl₀ hu₀.1 hu₀.2 hw₀
          cases lvls with
          | nil => nomatch hmem₀
          | cons lhd ltl =>
            cases strictDAG_has_maximal dag lhd ltl with
            | intro m hm =>
              cases hlvls.2 m hm.1 with
              | intro u_max hrestM =>
                cases hrestM with
                | intro obj_max huM =>
                  cases hwt.live_fulfiller u_max obj_max m huM.1 huM.2.2 with
                  | intro v hv =>
                    have hSv : S v :=
                      hclosed.2.2 u_max v obj_max m huM.1 huM.2.1 huM.2.2 hv.1 hv.2
                    cases hclosed.2.1 v hv.1 hSv with
                    | intro obj_v hrestV =>
                      cases hrestV with
                      | intro lvl_v hwV =>
                        have hlvl_v_mem : lvl_v ∈ (lhd :: ltl) :=
                          hlvls.1 v obj_v lvl_v hv.1 hSv hwV
                        cases hv.2.2 with
                        | intro k hrestB =>
                          cases hrestB with
                          | intro b htok =>
                            have hall := hwt.strict_wait_order v obj_v lvl_v hv.1 hwV
                            have hprec : prec m lvl_v :=
                              hall m (ordered_mem_tokensLevels htok)
                            exact hm.2 lvl_v hlvl_v_mem hprec

theorem wellTypedWorld_no_global_block {Level : Type}
    {prec : Level → Level → Prop}
    (dag : StrictDAG Level prec)
    {units : List (ExecUnit Level)}
    (hwt : WellTypedWorld prec units)
    (h_unfinished : ∃ u₀ : ExecUnit Level, u₀ ∈ units ∧ u₀.wait ≠ .finished)
    (h_all_stalled : ∀ u : ExecUnit Level, u ∈ units →
      u.wait ≠ .finished → unitIsBlocked u) :
    False := by
  refine wellTypedWorld_no_closedBlockedSet dag hwt (fun u => u.wait ≠ .finished) ?_
  refine ⟨h_unfinished, h_all_stalled, ?_⟩
  intro _ _ _ _ _ _ _ _ hvholds
  exact hvholds.1

/-! ### Carrier-Tagged `ambient`, Output-Safe `rayonJoin`, Mode-Disjoint Channels & Lock-Guarded `condvarNotify` -/

inductive CondvarWaitMode where
  | unguardedUnconditional
  | coupledMutexPredLoop (id_lock : ObjId)

inductive Stmt (Level : Type) where
  | skip
  | seq (s₁ s₂ : Stmt Level)
  | mutexLock (id : ObjId) (lvl : Level)
  | unlock (pred : LinearToken Level → Bool)
  | rwReadWriterPref (id : ObjId) (lvl : Level)
  | rwReadRecursive (id : ObjId) (lvl : Level)
  | rwWrite (id : ObjId) (lvl : Level)
  | rwUpgradableRead (id : ObjId) (lvl : Level)
  | rwUpgrade (pred : LinearToken Level → Bool) (id : ObjId) (lvl : Level)
  | condvarWait (pred : LinearToken Level → Bool)
      (id_lock : ObjId) (lvl_lock : Level)
      (id_cvar : ObjId) (lvl_cvar : Level)
      (mode : CondvarWaitMode)
  | condvarNotify (pred : LinearToken Level → Bool)
      (id_lock : ObjId) (id_cvar : ObjId) (lvl_cvar : Level)
  | onceCall (id_once : ObjId) (lvl_once : Level) (body : Stmt Level)
  | barrierWait (pred : LinearToken Level → Bool)
      (id_bar : ObjId) (lvl_bar : Level)
  | chanCreditSend (predOb predCap : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level)
  | chanCreditRecv (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level)
  | chanBlockingSend (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level)
  | chanBlockingRecv (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level)
  | chanTrySend (id_ch : ObjId)
  | dropCapSlot (predCap : LinearToken Level → Bool) (id_ch : ObjId)
  | joinWait (id_child : ObjId) (lvl_join : Level)
  | rayonJoin (held_f held_g : List (LinearToken Level)) (f g : Stmt Level)
  | asyncMutexLockAwait (id : ObjId) (lvl : Level)
  | asyncAwaitPoint (id_fut : ObjId) (lvl_fut : Level)

def IsUnlockableGuardKind (k : TokenKind) : Prop :=
  k = .mutexGuard ∨ k = .rwWriteGuard ∨ k = .rwReadGuard ∨
  k = .rwUpgradableGuard ∨ k = .asyncMutexGuard

/-- Final deadlock-freedom typing judgment:
1. Carrier-tagged read-only `ambient : List (Level × CarrierBinding)` checked
   with `HasNoOsBoundAmbient ambient` in `.asyncAwaitPoint`,
   `.asyncMutexLockAwait`, and `.rayonJoin`, and pushed as `(lvl_once, .osBound)`
   by `onceCall` (forbidding `.await`, `asyncMutexLockAwait`, and `rayonJoin`
   inside `Once::call_once`!).
2. Symmetric, output-safe `rayonJoin`: requires `HasNoOsBound` on all four of
   `held_f`, `held_g`, `held_f'`, `held_g'` AND `HasNoOsBoundAmbient ambient`,
   and checks `f` against `tokensAmbient held_g ++ tokensAmbient held_g' ++ ambient`
   and `g` against `tokensAmbient held_f ++ tokensAmbient held_f' ++ ambient`!
3. Mode-disjoint channels: `.creditManaged` (`chanCreditSend` / `chanCreditRecv`
   with `.chanCapSlot`) strictly disjoint from `.levelOrdered`
   (`chanBlockingSend` / `chanBlockingRecv`), plus non-blocking `chanTrySend`.
4. Lock-guarded `condvarNotify`: requires holding `Mutex(id_lock)`
   (`HasHeldTokenOfKind held id_lock .mutexGuard`)! -/
inductive TypedStmt {Level : Type} (prec : Level → Level → Prop) :
    List (Level × CarrierBinding) → Stmt Level →
      List (LinearToken Level) → List (LinearToken Level) → Prop where
  | skip (ambient : List (Level × CarrierBinding)) (held : List (LinearToken Level)) :
      TypedStmt prec ambient .skip held held
  | seq {ambient s₁ s₂ h₁ h₂ h₃} :
      TypedStmt prec ambient s₁ h₁ h₂ →
      TypedStmt prec ambient s₂ h₂ h₃ →
      TypedStmt prec ambient (.seq s₁ s₂) h₁ h₃
  | mutexLock {ambient held} (id : ObjId) (lvl : Level) :
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl →
      TypedStmt prec ambient (.mutexLock id lvl) held
        (.ordered id lvl .mutexGuard .osBound :: held)
  | unlockToken {ambient held rem} (pred : LinearToken Level → Bool)
      (id : ObjId) (lvl : Level) (k : TokenKind) (b : CarrierBinding) :
      removeFirstToken pred held = some (.ordered id lvl k b, rem) →
      IsUnlockableGuardKind k →
      TypedStmt prec ambient (.unlock pred) held rem
  | rwReadWriterPref {ambient held} (id : ObjId) (lvl : Level) :
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl →
      TypedStmt prec ambient (.rwReadWriterPref id lvl) held
        (.ordered id lvl .rwReadGuard .osBound :: held)
  | rwReadRecursive {ambient held} (id : ObjId) (lvl : Level) :
      (HoldsSameRwRead id held ∨
        AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl) →
      TypedStmt prec ambient (.rwReadRecursive id lvl) held
        (.ordered id lvl .rwReadGuard .osBound :: held)
  | rwWrite {ambient held} (id : ObjId) (lvl : Level) :
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl →
      TypedStmt prec ambient (.rwWrite id lvl) held
        (.ordered id lvl .rwWriteGuard .osBound :: held)
  | rwUpgradableRead {ambient held} (id : ObjId) (lvl : Level) :
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl →
      TypedStmt prec ambient (.rwUpgradableRead id lvl) held
        (.ordered id lvl .rwUpgradableGuard .osBound :: held)
  | rwUpgrade {ambient held rem} (pred : LinearToken Level → Bool)
      (id : ObjId) (lvl : Level) :
      removeFirstToken pred held =
        some (.ordered id lvl .rwUpgradableGuard .osBound, rem) →
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl →
      TypedStmt prec ambient (.rwUpgrade pred id lvl) held
        (.ordered id lvl .rwWriteGuard .osBound :: rem)
  | condvarWaitWhileNotNotified {ambient held rem}
      (pred : LinearToken Level → Bool)
      (id_lock : ObjId) (lvl_lock : Level)
      (id_cvar : ObjId) (lvl_cvar : Level) :
      id_lock ≠ id_cvar →
      removeFirstToken pred held =
        some (.ordered id_lock lvl_lock .mutexGuard .osBound, rem) →
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_cvar →
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_lock →
      TypedStmt prec ambient
        (.condvarWait pred id_lock lvl_lock id_cvar lvl_cvar
          (.coupledMutexPredLoop id_lock))
        held (.ordered id_lock lvl_lock .mutexGuard .osBound :: rem)
  | condvarNotify {ambient held rem} (pred : LinearToken Level → Bool)
      (id_lock id_cvar : ObjId) (lvl_cvar : Level) :
      HasHeldTokenOfKind held id_lock .mutexGuard →
      removeFirstToken pred held =
        some (.ordered id_cvar lvl_cvar .condvarSignalOb .taskMovable, rem) →
      TypedStmt prec ambient (.condvarNotify pred id_lock id_cvar lvl_cvar) held rem
  | onceCall {ambient held held'} (id_once : ObjId) (lvl_once : Level)
      (body : Stmt Level) :
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl_once →
      TypedStmt prec ((lvl_once, .osBound) :: ambient) body held held' →
      TypedStmt prec ambient (.onceCall id_once lvl_once body) held held'
  | barrierWait {ambient held rem} (pred : LinearToken Level → Bool)
      (id_bar : ObjId) (lvl_bar : Level) :
      removeFirstToken pred held =
        some (.ordered id_bar lvl_bar .barrierTicket .taskMovable, rem) →
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_bar →
      TypedStmt prec ambient (.barrierWait pred id_bar lvl_bar) held rem
  | chanCreditSend {ambient held mid rem}
      (predOb predCap : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) :
      removeFirstToken predOb held =
        some (.ordered id_ch lvl_ch .chanCreditSendOb .taskMovable, mid) →
      removeFirstToken predCap mid =
        some (.chanCapSlot id_ch, rem) →
      TypedStmt prec ambient
        (.chanCreditSend predOb predCap id_ch lvl_ch) held rem
  | chanCreditRecv {ambient held rem}
      (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) :
      removeFirstToken predOb held =
        some (.ordered id_ch lvl_ch .chanCreditRecvOb .taskMovable, rem) →
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_ch →
      TypedStmt prec ambient
        (.chanCreditRecv predOb id_ch lvl_ch) held (.chanCapSlot id_ch :: rem)
  | chanBlockingSend {ambient held rem}
      (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) :
      removeFirstToken predOb held =
        some (.ordered id_ch lvl_ch .chanBlockingSendOb .taskMovable, rem) →
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_ch →
      TypedStmt prec ambient
        (.chanBlockingSend predOb id_ch lvl_ch) held rem
  | chanBlockingRecv {ambient held rem}
      (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) :
      removeFirstToken predOb held =
        some (.ordered id_ch lvl_ch .chanBlockingRecvOb .taskMovable, rem) →
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_ch →
      TypedStmt prec ambient
        (.chanBlockingRecv predOb id_ch lvl_ch) held rem
  | chanTrySend {ambient held} (id_ch : ObjId) :
      TypedStmt prec ambient (.chanTrySend id_ch) held held
  | dropCapSlot {ambient held rem}
      (predCap : LinearToken Level → Bool) (id_ch : ObjId) :
      removeFirstToken predCap held = some (.chanCapSlot id_ch, rem) →
      TypedStmt prec ambient (.dropCapSlot predCap id_ch) held rem
  | joinWait {ambient held} (id_child : ObjId) (lvl_join : Level) :
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl_join →
      TypedStmt prec ambient (.joinWait id_child lvl_join) held held
  | rayonJoin {ambient held_f held_g held_f' held_g' f g} :
      HasNoOsBound held_f →
      HasNoOsBound held_g →
      HasNoOsBound held_f' →
      HasNoOsBound held_g' →
      HasNoOsBoundAmbient ambient →
      TypedStmt prec (tokensAmbient held_g ++ tokensAmbient held_g' ++ ambient)
        f held_f held_f' →
      TypedStmt prec (tokensAmbient held_f ++ tokensAmbient held_f' ++ ambient)
        g held_g held_g' →
      TypedStmt prec ambient (.rayonJoin held_f held_g f g)
        (held_f ++ held_g) (held_f' ++ held_g')
  | asyncMutexLockAwait {ambient held} (id : ObjId) (lvl : Level) :
      HasNoOsBound held →
      HasNoOsBoundAmbient ambient →
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl →
      TypedStmt prec ambient (.asyncMutexLockAwait id lvl) held
        (.ordered id lvl .asyncMutexGuard .taskMovable :: held)
  | asyncAwaitPoint {ambient held} (id_fut : ObjId) (lvl_fut : Level) :
      HasNoOsBound held →
      HasNoOsBoundAmbient ambient →
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl_fut →
      TypedStmt prec ambient (.asyncAwaitPoint id_fut lvl_fut) held held

def ValidThreadStmt {Level : Type} (prec : Level → Level → Prop)
    (stmt : Stmt Level) (initTokens : List (LinearToken Level)) : Prop :=
  TypedStmt prec [] stmt initTokens []

private theorem typedStmt_mutexLock_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {id : ObjId} {lvl : Level}
    {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.mutexLock id lvl) held outT) :
    AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl := by
  cases h with
  | mutexLock _ _ hb => exact hb

private theorem typedStmt_rwReadWriterPref_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {id : ObjId} {lvl : Level}
    {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.rwReadWriterPref id lvl) held outT) :
    AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl := by
  cases h with
  | rwReadWriterPref _ _ hb => exact hb

private theorem typedStmt_rwWrite_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {id : ObjId} {lvl : Level}
    {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.rwWrite id lvl) held outT) :
    AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl := by
  cases h with
  | rwWrite _ _ hb => exact hb

private theorem typedStmt_condvarWait_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {pred : LinearToken Level → Bool}
    {id_lock : ObjId} {lvl_lock : Level} {id_cvar : ObjId} {lvl_cvar : Level}
    {mode : CondvarWaitMode} {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.condvarWait pred id_lock lvl_lock id_cvar lvl_cvar mode) held outT) :
    ∃ rem,
      id_lock ≠ id_cvar ∧
      removeFirstToken pred held = some (.ordered id_lock lvl_lock .mutexGuard .osBound, rem) ∧
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_cvar := by
  cases h with
  | condvarWaitWhileNotNotified _ _ _ _ _ hne hrem hb _ =>
    exact ⟨_, hne, hrem, hb⟩

private theorem typedStmt_chanBlockingSend_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {predOb : LinearToken Level → Bool}
    {id_ch : ObjId} {lvl_ch : Level} {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.chanBlockingSend predOb id_ch lvl_ch) held outT) :
    ∃ rem,
      removeFirstToken predOb held = some (.ordered id_ch lvl_ch .chanBlockingSendOb .taskMovable, rem) ∧
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_ch := by
  cases h with
  | chanBlockingSend _ _ _ hrem hb => exact ⟨_, hrem, hb⟩

private theorem typedStmt_chanBlockingRecv_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {predOb : LinearToken Level → Bool}
    {id_ch : ObjId} {lvl_ch : Level} {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.chanBlockingRecv predOb id_ch lvl_ch) held outT) :
    ∃ rem,
      removeFirstToken predOb held = some (.ordered id_ch lvl_ch .chanBlockingRecvOb .taskMovable, rem) ∧
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_ch := by
  cases h with
  | chanBlockingRecv _ _ _ hrem hb => exact ⟨_, hrem, hb⟩

private theorem typedStmt_barrierWait_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {pred : LinearToken Level → Bool}
    {id_bar : ObjId} {lvl_bar : Level} {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.barrierWait pred id_bar lvl_bar) held outT) :
    ∃ rem,
      removeFirstToken pred held = some (.ordered id_bar lvl_bar .barrierTicket .taskMovable, rem) ∧
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_bar := by
  cases h with
  | barrierWait _ _ _ hrem hb => exact ⟨_, hrem, hb⟩

private theorem typedStmt_chanCreditRecv_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {predOb : LinearToken Level → Bool}
    {id_ch : ObjId} {lvl_ch : Level} {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.chanCreditRecv predOb id_ch lvl_ch) held outT) :
    ∃ rem,
      removeFirstToken predOb held = some (.ordered id_ch lvl_ch .chanCreditRecvOb .taskMovable, rem) ∧
      AllBelow prec (tokensLevels rem ++ ambientLevels ambient) lvl_ch := by
  cases h with
  | chanCreditRecv _ _ _ hrem hb => exact ⟨_, hrem, hb⟩

private theorem typedStmt_joinWait_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {id_child : ObjId} {lvl_join : Level}
    {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.joinWait id_child lvl_join) held outT) :
    AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl_join := by
  cases h with
  | joinWait _ _ hb => exact hb

private theorem typedStmt_asyncMutexLockAwait_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {id : ObjId} {lvl : Level}
    {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.asyncMutexLockAwait id lvl) held outT) :
    HasNoOsBound held ∧ HasNoOsBoundAmbient ambient ∧
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl := by
  cases h with
  | asyncMutexLockAwait _ _ hnoOs hnoAmb hb => exact ⟨hnoOs, hnoAmb, hb⟩

private theorem typedStmt_asyncAwaitPoint_inv {Level : Type} {prec : Level → Level → Prop}
    {ambient : List (Level × CarrierBinding)} {id_fut : ObjId} {lvl_fut : Level}
    {held outT : List (LinearToken Level)}
    (h : TypedStmt prec ambient (.asyncAwaitPoint id_fut lvl_fut) held outT) :
    HasNoOsBound held ∧ HasNoOsBoundAmbient ambient ∧
      AllBelow prec (tokensLevels held ++ ambientLevels ambient) lvl_fut := by
  cases h with
  | asyncAwaitPoint _ _ hnoOs hnoAmb hb => exact ⟨hnoOs, hnoAmb, hb⟩

/-! ### Closed Global `TokenWorld` & Non-Circular `TokenConservingWorld` Preservation -/

/-- Tightened coupled Mutex-protected predicate invariant for `Condvar::wait_while`:
whenever `notified = false`, at least one live (non-finished) unit in `units`
holds the linear `.condvarSignalOb .taskMovable` obligation for `(id_cvar, lvl_cvar)`. -/
def CondvarCoupledInv {Level : Type} (units : List (ExecUnit Level))
    (id_cvar : ObjId) (lvl_cvar : Level) (notified : Bool) : Prop :=
  notified = false →
    ∃ v : ExecUnit Level,
      v ∈ units ∧
      v.wait ≠ .finished ∧
      LinearToken.ordered id_cvar lvl_cvar .condvarSignalOb .taskMovable ∈ v.held

theorem condvarNotify_preserves_coupledInv {Level : Type}
    (units' : List (ExecUnit Level)) (id_cvar : ObjId) (lvl_cvar : Level) :
    CondvarCoupledInv units' id_cvar lvl_cvar true :=
  fun h => nomatch h

noncomputable def onceAmbient {Level : Type} :
    List (ObjId × Level) → List (Level × CarrierBinding)
  | [] => []
  | (_, lvl) :: rest => (lvl, .osBound) :: onceAmbient rest

noncomputable def onceHeldTokens {Level : Type} :
    List (ObjId × Level) → List (LinearToken Level)
  | [] => []
  | (id, lvl) :: rest => .ordered id lvl .onceInitGuard .osBound :: onceHeldTokens rest

theorem tokensLevels_onceHeldTokens {Level : Type}
    (frames : List (ObjId × Level)) :
    tokensLevels (onceHeldTokens frames) = ambientLevels (onceAmbient frames) := by
  induction frames with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk id lvl =>
      dsimp [onceHeldTokens, tokensLevels, onceAmbient, ambientLevels]
      rw [ih]

theorem onceFrames_nil_of_noOsBoundAmbient {Level : Type}
    {frames : List (ObjId × Level)} {extra : List (Level × CarrierBinding)}
    (h : HasNoOsBoundAmbient (onceAmbient frames ++ extra)) :
    frames = [] := by
  cases frames with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | mk _ _ =>
      dsimp [onceAmbient] at h
      nomatch h.1

theorem mem_onceHeldTokens_of_mem {Level : Type}
    {id : ObjId} {lvl : Level} {frames : List (ObjId × Level)}
    (h : (id, lvl) ∈ frames) :
    LinearToken.ordered id lvl .onceInitGuard .osBound ∈ onceHeldTokens frames := by
  induction frames with
  | nil => nomatch h
  | cons hd tl ih =>
    cases hd with
    | mk id' lvl' =>
      cases h with
      | head => exact List.Mem.head _
      | tail _ htl => exact List.Mem.tail _ (ih htl)

theorem countCapSlotsInList_onceHeldTokens {Level : Type} (id_ch : ObjId)
    (frames : List (ObjId × Level)) :
    countCapSlotsInList id_ch (onceHeldTokens frames) = 0 := by
  induction frames with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | mk _ _ => exact ih

structure WorldUnit (Level : Type) where
  uid : UnitId
  stmt : Stmt Level
  held : List (LinearToken Level)
  onceFrames : List (ObjId × Level)
  extraAmbient : List (Level × CarrierBinding)
  outTokens : List (LinearToken Level)
  wait : UnitWait Level

noncomputable def unitAmbient {Level : Type} (u : WorldUnit Level) :
    List (Level × CarrierBinding) :=
  onceAmbient u.onceFrames ++ u.extraAmbient

noncomputable def toExecUnit {Level : Type} (u : WorldUnit Level) :
    ExecUnit Level :=
  { uid := u.uid
    held := u.held ++ onceHeldTokens u.onceFrames
    wait := u.wait }

noncomputable def mapExecUnits {Level : Type} :
    List (WorldUnit Level) → List (ExecUnit Level)
  | [] => []
  | u :: rest => toExecUnit u :: mapExecUnits rest

theorem mem_mapExecUnits {Level : Type} {u : WorldUnit Level}
    {us : List (WorldUnit Level)} (h : u ∈ us) :
    toExecUnit u ∈ mapExecUnits us := by
  induction us with
  | nil => nomatch h
  | cons hd tl ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ htl => exact List.Mem.tail _ (ih htl)

theorem mapExecUnits_mem_inv {Level : Type} {eu : ExecUnit Level}
    {us : List (WorldUnit Level)} (h : eu ∈ mapExecUnits us) :
    ∃ u : WorldUnit Level, u ∈ us ∧ toExecUnit u = eu := by
  induction us with
  | nil => nomatch h
  | cons hd tl ih =>
    cases h with
    | head => exact ⟨hd, List.Mem.head tl, rfl⟩
    | tail _ htl =>
      cases ih htl with
      | intro u hu => exact ⟨u, List.Mem.tail hd hu.1, hu.2⟩

noncomputable def countCapSlotsWorld {Level : Type} (id_ch : ObjId) :
    List (WorldUnit Level) → Nat
  | [] => 0
  | u :: rest => countCapSlotsInList id_ch u.held + countCapSlotsWorld id_ch rest

theorem countCapSlotsWorld_append {Level : Type} (id_ch : ObjId)
    (xs ys : List (WorldUnit Level)) :
    countCapSlotsWorld id_ch (xs ++ ys) =
      countCapSlotsWorld id_ch xs + countCapSlotsWorld id_ch ys := by
  induction xs with
  | nil =>
    dsimp [countCapSlotsWorld]
    rw [Nat.zero_add]
  | cons hd tl ih =>
    dsimp [countCapSlotsWorld]
    rw [ih, Nat.add_assoc]

noncomputable def wakeUnitOn {Level : Type} (obj : ObjId)
    (u : WorldUnit Level) : WorldUnit Level :=
  match u.wait with
  | .osBlocked c o _ =>
      if Nat.beq o obj then { u with wait := .running c } else u
  | .coopBlocked o _ =>
      if Nat.beq o obj then { u with wait := .readyQueue } else u
  | _ => u

noncomputable def wakeWaitersOn {Level : Type} (obj : ObjId) :
    List (WorldUnit Level) → List (WorldUnit Level)
  | [] => []
  | u :: rest => wakeUnitOn obj u :: wakeWaitersOn obj rest

theorem wakeUnitOn_preserves_fields {Level : Type} (obj : ObjId)
    (u : WorldUnit Level) :
    (wakeUnitOn obj u).uid = u.uid ∧
    (wakeUnitOn obj u).stmt = u.stmt ∧
    (wakeUnitOn obj u).held = u.held ∧
    (wakeUnitOn obj u).onceFrames = u.onceFrames ∧
    (wakeUnitOn obj u).extraAmbient = u.extraAmbient ∧
    (wakeUnitOn obj u).outTokens = u.outTokens := by
  unfold wakeUnitOn
  cases u.wait with
  | running _ => dsimp; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | readyQueue => dsimp; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | finished => dsimp; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | osBlocked _ o _ =>
    dsimp
    cases Nat.beq o obj <;> dsimp <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | coopBlocked o _ =>
    dsimp
    cases Nat.beq o obj <;> dsimp <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wakeUnitOn_finished_iff {Level : Type} (obj : ObjId)
    (u : WorldUnit Level) :
    (wakeUnitOn obj u).wait = .finished ↔ u.wait = .finished := by
  cases u with
  | mk uid stmt held onceFrames extraAmbient outTokens wait =>
    unfold wakeUnitOn
    cases wait with
    | running _ =>
      dsimp
      constructor
      · intro x; nomatch x
      · intro x; nomatch x
    | readyQueue =>
      dsimp
      constructor
      · intro x; nomatch x
      · intro x; nomatch x
    | finished =>
      dsimp
      constructor
      · intro _; rfl
      · intro _; rfl
    | osBlocked _ o _ =>
      dsimp
      cases Nat.beq o obj with
      | true =>
        dsimp
        constructor
        · intro x; nomatch x
        · intro x; nomatch x
      | false =>
        dsimp
        constructor
        · intro x; nomatch x
        · intro x; nomatch x
    | coopBlocked o _ =>
      dsimp
      cases Nat.beq o obj with
      | true =>
        dsimp
        constructor
        · intro x; nomatch x
        · intro x; nomatch x
      | false =>
        dsimp
        constructor
        · intro x; nomatch x
        · intro x; nomatch x

theorem wakeUnitOn_stillBlocked {Level : Type} (obj : ObjId)
    (u : WorldUnit Level) {o : ObjId} {l : Level}
    (h : unitWaitLevel? (toExecUnit (wakeUnitOn obj u)) = some (o, l)) :
    o ≠ obj ∧ unitWaitLevel? (toExecUnit u) = some (o, l) := by
  cases u with
  | mk uid stmt held onceFrames extraAmbient outTokens wait =>
    unfold wakeUnitOn at h
    cases wait with
    | running _ => dsimp [toExecUnit, unitWaitLevel?] at h; nomatch h
    | readyQueue => dsimp [toExecUnit, unitWaitLevel?] at h; nomatch h
    | finished => dsimp [toExecUnit, unitWaitLevel?] at h; nomatch h
    | osBlocked c o' l' =>
      dsimp at h
      cases hb : Nat.beq o' obj with
      | true => rw [hb] at h; dsimp [toExecUnit, unitWaitLevel?] at h; nomatch h
      | false =>
        rw [hb] at h
        dsimp [toExecUnit, unitWaitLevel?] at h
        injection h with hp
        injection hp with ho hl
        subst ho; subst hl
        refine ⟨?_, rfl⟩
        intro heq; subst heq; rw [Nat.beq_refl o'] at hb; nomatch hb
    | coopBlocked o' l' =>
      dsimp at h
      cases hb : Nat.beq o' obj with
      | true => rw [hb] at h; dsimp [toExecUnit, unitWaitLevel?] at h; nomatch h
      | false =>
        rw [hb] at h
        dsimp [toExecUnit, unitWaitLevel?] at h
        injection h with hp
        injection hp with ho hl
        subst ho; subst hl
        refine ⟨?_, rfl⟩
        intro heq; subst heq; rw [Nat.beq_refl o'] at hb; nomatch hb

theorem wakeUnitOn_preserves_yield {Level : Type} (obj : ObjId)
    (u : WorldUnit Level)
    (hy : (wakeUnitOn obj u).wait = .readyQueue ∨
      ∃ o l, (wakeUnitOn obj u).wait = .coopBlocked o l) :
    u.wait = .readyQueue ∨ ∃ o l, u.wait = .coopBlocked o l := by
  cases u with
  | mk uid stmt held onceFrames extraAmbient outTokens wait =>
    unfold wakeUnitOn at hy
    cases wait with
    | running _ =>
      dsimp at hy
      cases hy with
      | inl h => nomatch h
      | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
    | finished =>
      dsimp at hy
      cases hy with
      | inl h => nomatch h
      | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
    | readyQueue => exact Or.inl rfl
    | coopBlocked o l => exact Or.inr ⟨o, l, rfl⟩
    | osBlocked c o l =>
      dsimp at hy
      cases hb : Nat.beq o obj with
      | true =>
        rw [hb] at hy; dsimp at hy
        cases hy with
        | inl h => nomatch h
        | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
      | false =>
        rw [hb] at hy; dsimp at hy
        cases hy with
        | inl h => nomatch h
        | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3

theorem mem_wakeWaitersOn {Level : Type} (obj : ObjId)
    {u : WorldUnit Level} {us : List (WorldUnit Level)} (h : u ∈ us) :
    wakeUnitOn obj u ∈ wakeWaitersOn obj us := by
  induction us with
  | nil => nomatch h
  | cons hd tl ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ htl => exact List.Mem.tail _ (ih htl)

theorem wakeWaitersOn_mem_inv {Level : Type} (obj : ObjId)
    {u' : WorldUnit Level} {us : List (WorldUnit Level)}
    (h : u' ∈ wakeWaitersOn obj us) :
    ∃ u : WorldUnit Level, u ∈ us ∧ wakeUnitOn obj u = u' := by
  induction us with
  | nil => nomatch h
  | cons hd tl ih =>
    cases h with
    | head => exact ⟨hd, List.Mem.head tl, rfl⟩
    | tail _ htl =>
      cases ih htl with
      | intro u hu => exact ⟨u, List.Mem.tail hd hu.1, hu.2⟩

theorem countCapSlotsWorld_wakeWaitersOn {Level : Type} (id_ch obj : ObjId)
    (us : List (WorldUnit Level)) :
    countCapSlotsWorld id_ch (wakeWaitersOn obj us) =
      countCapSlotsWorld id_ch us := by
  induction us with
  | nil => rfl
  | cons hd tl ih =>
    dsimp [wakeWaitersOn, countCapSlotsWorld]
    rw [(wakeUnitOn_preserves_fields obj hd).2.2.1, ih]

/-- Closed global synchronization runtime state. Every physical
contention state (`mutexHeld`, `rwHeld`, `onceIniting`, `childRunning`,
`asyncMutexHeld`, `futurePending`, `condvarNotified`, `chanBuf`/`chanCap`,
`barrierWaiting`) is tracked directly inside the world and tied by
`TokenConservingWorld` to live linear tokens — ZERO premise-baking! -/
structure SyncState (Level : Type) where
  mutexHeld : ObjId → Option (UnitId × Level)
  rwHeld : ObjId → Option (UnitId × Level)
  onceIniting : ObjId → Option (UnitId × Level)
  childRunning : ObjId → Option (UnitId × Level)
  asyncMutexHeld : ObjId → Option (UnitId × Level)
  futurePending : ObjId → Option (UnitId × Level)
  condvarNotified : ObjId → Bool
  condvarLevel : ObjId → Level
  chanBuf : ObjId → Nat
  chanCap : ObjId → Nat
  chanMode : ObjId → ChannelMode
  barrierOpen : ObjId → Bool

structure TokenWorld (Level : Type) where
  units : List (WorldUnit Level)
  sync : SyncState Level

def funUpdate {α : Type} (f : ObjId → α) (k : ObjId) (v : α) : ObjId → α :=
  fun x => if Nat.beq x k then v else f x

/-- Non-circular `TokenConservingWorld` invariant:
binds every active physical synchronization object in `world.sync` to a live
(non-finished) unit in `world.units` holding its matching linear token, enforces
`TypedStmt` on every active unit, `WellTypedWorld` on the projected `ExecUnit`s,
`CondvarCoupledInv` for all condvars, and `countCapSlotsWorld + chanBuf = chanCap`
for all `.creditManaged` channels. -/
structure TokenConservingWorld {Level : Type} (prec : Level → Level → Prop)
    (world : TokenWorld Level) : Prop where
  units_typed :
    ∀ u : WorldUnit Level, u ∈ world.units →
      (u.wait = .finished → u.held = [] ∧ u.onceFrames = []) ∧
      (u.wait ≠ .finished → TypedStmt prec (unitAmbient u) u.stmt u.held u.outTokens)
  world_wt :
    WellTypedWorld prec (mapExecUnits world.units)
  mutex_conserved :
    ∀ id holder lvl, world.sync.mutexHeld id = some (holder, lvl) →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        LinearToken.ordered id lvl .mutexGuard .osBound ∈ v.held
  rw_conserved :
    ∀ id holder lvl, world.sync.rwHeld id = some (holder, lvl) →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        ∃ k b, LinearToken.ordered id lvl k b ∈ v.held
  once_conserved :
    ∀ id holder lvl, world.sync.onceIniting id = some (holder, lvl) →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        (id, lvl) ∈ v.onceFrames
  child_conserved :
    ∀ id holder lvl, world.sync.childRunning id = some (holder, lvl) →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        LinearToken.ordered id lvl .joinExitOb .taskMovable ∈ v.held
  asyncMutex_conserved :
    ∀ id holder lvl, world.sync.asyncMutexHeld id = some (holder, lvl) →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        LinearToken.ordered id lvl .asyncMutexGuard .taskMovable ∈ v.held
  future_conserved :
    ∀ id holder lvl, world.sync.futurePending id = some (holder, lvl) →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        ∃ k b, LinearToken.ordered id lvl k b ∈ v.held
  condvar_coupled :
    ∀ id_cvar : ObjId,
      CondvarCoupledInv (mapExecUnits world.units) id_cvar
        (world.sync.condvarLevel id_cvar) (world.sync.condvarNotified id_cvar)
  creditChan_conserved :
    ∀ id_ch : ObjId,
      world.sync.chanMode id_ch = .creditManaged →
      countCapSlotsWorld id_ch world.units + world.sync.chanBuf id_ch =
        world.sync.chanCap id_ch
  chanCreditRecv_paired :
    ∀ u id_ch lvl_ch, u ∈ world.units → u.wait ≠ .finished →
      LinearToken.ordered id_ch lvl_ch .chanCreditRecvOb .taskMovable ∈ u.held →
      world.sync.chanBuf id_ch = 0 →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        LinearToken.ordered id_ch lvl_ch .chanCreditSendOb .taskMovable ∈ v.held
  chanBlockingSend_paired :
    ∀ u id_ch lvl_ch, u ∈ world.units → u.wait ≠ .finished →
      LinearToken.ordered id_ch lvl_ch .chanBlockingSendOb .taskMovable ∈ u.held →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        LinearToken.ordered id_ch lvl_ch .chanBlockingRecvOb .taskMovable ∈ v.held
  chanBlockingRecv_paired :
    ∀ u id_ch lvl_ch, u ∈ world.units → u.wait ≠ .finished →
      LinearToken.ordered id_ch lvl_ch .chanBlockingRecvOb .taskMovable ∈ u.held →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        LinearToken.ordered id_ch lvl_ch .chanBlockingSendOb .taskMovable ∈ v.held
  barrier_paired :
    ∀ u id_bar lvl_bar, u ∈ world.units → u.wait ≠ .finished →
      LinearToken.ordered id_bar lvl_bar .barrierTicket .taskMovable ∈ u.held →
      world.sync.barrierOpen id_bar = true →
      ∃ v : WorldUnit Level, v ∈ world.units ∧ v.wait ≠ .finished ∧
        v.uid ≠ u.uid ∧
        LinearToken.ordered id_bar lvl_bar .barrierTicket .taskMovable ∈ v.held

/-- Closed operational `WorldStep` transition relation:
ZERO `∃ v₀ ∈ rest, unitHoldsFor ...` and ZERO `RestFulfillersPreservedOnRelease`
baked into ANY constructor! Every blocking and non-blocking step checks ONLY
physical `sync` state and local `u.stmt` / `u.held`. -/
inductive WorldStep {Level : Type} :
    TokenWorld Level → TokenWorld Level → Prop where
  | scheduleRotate (u : WorldUnit Level) (rest : List (WorldUnit Level))
      (sync : SyncState Level) :
      WorldStep ⟨u :: rest, sync⟩ ⟨rest ++ [u], sync⟩
  | seqSkip (u : WorldUnit Level) (s₂ : Stmt Level)
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .seq .skip s₂ →
      u.wait = .running c →
      WorldStep ⟨u :: rest, sync⟩ ⟨{ u with stmt := s₂ } :: rest, sync⟩
  | unlockMutex (u : WorldUnit Level) (pred : LinearToken Level → Bool)
      (id : ObjId) (lvl : Level) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .unlock pred →
      u.wait = .running c →
      removeFirstToken pred u.held =
        some (.ordered id lvl .mutexGuard .osBound, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with stmt := .skip, held := rem } :: wakeWaitersOn id rest,
         { sync with mutexHeld := funUpdate sync.mutexHeld id none }⟩
  | unlockAsyncMutex (u : WorldUnit Level) (pred : LinearToken Level → Bool)
      (id : ObjId) (lvl : Level) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .unlock pred →
      u.wait = .running c →
      removeFirstToken pred u.held =
        some (.ordered id lvl .asyncMutexGuard .taskMovable, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with stmt := .skip, held := rem } :: wakeWaitersOn id rest,
         { sync with asyncMutexHeld := funUpdate sync.asyncMutexHeld id none }⟩
  | condvarNotify (u : WorldUnit Level) (pred : LinearToken Level → Bool)
      (id_lock id_cvar : ObjId) (lvl_cvar : Level) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .condvarNotify pred id_lock id_cvar lvl_cvar →
      u.wait = .running c →
      removeFirstToken pred u.held =
        some (.ordered id_cvar lvl_cvar .condvarSignalOb .taskMovable, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with stmt := .skip, held := rem } :: wakeWaitersOn id_cvar rest,
         { sync with condvarNotified := funUpdate sync.condvarNotified id_cvar true }⟩
  | chanCreditSend (u : WorldUnit Level)
      (predOb predCap : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) (mid rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .chanCreditSend predOb predCap id_ch lvl_ch →
      u.wait = .running c →
      removeFirstToken predOb u.held =
        some (.ordered id_ch lvl_ch .chanCreditSendOb .taskMovable, mid) →
      removeFirstToken predCap mid = some (.chanCapSlot id_ch, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with stmt := .skip, held := rem } :: wakeWaitersOn id_ch rest,
         { sync with chanBuf := funUpdate sync.chanBuf id_ch (sync.chanBuf id_ch + 1) }⟩
  | enterOnce (u : WorldUnit Level) (id_once : ObjId) (lvl_once : Level)
      (body : Stmt Level) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .onceCall id_once lvl_once body →
      u.wait = .running c →
      sync.onceIniting id_once = none →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with stmt := body, onceFrames := (id_once, lvl_once) :: u.onceFrames } :: rest,
         { sync with onceIniting := funUpdate sync.onceIniting id_once (some (u.uid, lvl_once)) }⟩
  | forkRayonJoin (u : WorldUnit Level)
      (held_f held_g held_f' held_g' : List (LinearToken Level))
      (f g : Stmt Level) (uid_g : UnitId)
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .rayonJoin held_f held_g f g →
      u.wait = .running c →
      u.held = held_f ++ held_g →
      u.outTokens = held_f' ++ held_g' →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ uid := u.uid, stmt := f, held := held_f, onceFrames := [],
           extraAmbient := tokensAmbient held_g ++ tokensAmbient held_g' ++ u.extraAmbient,
           outTokens := held_f', wait := .running c } ::
         { uid := uid_g, stmt := g, held := held_g, onceFrames := [],
           extraAmbient := tokensAmbient held_f ++ tokensAmbient held_f' ++ u.extraAmbient,
           outTokens := held_g', wait := .readyQueue } :: rest,
         sync⟩
  | blockMutexLock (u : WorldUnit Level) (id : ObjId) (lvl : Level)
      (holder : UnitId) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .mutexLock id lvl →
      u.wait = .running c →
      sync.mutexHeld id = some (holder, lvl) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with wait := .osBlocked c id lvl } :: rest, sync⟩
  | blockRwReadWriterPref (u : WorldUnit Level) (id : ObjId) (lvl : Level)
      (holder : UnitId) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .rwReadWriterPref id lvl →
      u.wait = .running c →
      sync.rwHeld id = some (holder, lvl) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with wait := .osBlocked c id lvl } :: rest, sync⟩
  | blockRwWrite (u : WorldUnit Level) (id : ObjId) (lvl : Level)
      (holder : UnitId) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .rwWrite id lvl →
      u.wait = .running c →
      sync.rwHeld id = some (holder, lvl) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with wait := .osBlocked c id lvl } :: rest, sync⟩
  | blockOnceWait (u : WorldUnit Level) (id_once : ObjId) (lvl_once : Level)
      (body : Stmt Level) (holder : UnitId) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .onceCall id_once lvl_once body →
      u.wait = .running c →
      sync.onceIniting id_once = some (holder, lvl_once) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with wait := .osBlocked c id_once lvl_once } :: rest, sync⟩
  | blockCondvarWait (u : WorldUnit Level) (pred : LinearToken Level → Bool)
      (id_lock : ObjId) (lvl_lock : Level) (id_cvar : ObjId) (lvl_cvar : Level)
      (mode : CondvarWaitMode) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .condvarWait pred id_lock lvl_lock id_cvar lvl_cvar mode →
      u.wait = .running c →
      sync.condvarLevel id_cvar = lvl_cvar →
      sync.condvarNotified id_cvar = false →
      removeFirstToken pred u.held =
        some (.ordered id_lock lvl_lock .mutexGuard .osBound, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with held := rem, wait := .osBlocked c id_cvar lvl_cvar } ::
           wakeWaitersOn id_lock rest,
         { sync with mutexHeld := funUpdate sync.mutexHeld id_lock none }⟩
  | blockChanCreditRecv (u : WorldUnit Level) (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .chanCreditRecv predOb id_ch lvl_ch →
      u.wait = .running c →
      sync.chanBuf id_ch = 0 →
      removeFirstToken predOb u.held =
        some (.ordered id_ch lvl_ch .chanCreditRecvOb .taskMovable, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with held := rem, wait := .osBlocked c id_ch lvl_ch } :: rest, sync⟩
  | blockChanBlockingSend (u : WorldUnit Level) (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .chanBlockingSend predOb id_ch lvl_ch →
      u.wait = .running c →
      removeFirstToken predOb u.held =
        some (.ordered id_ch lvl_ch .chanBlockingSendOb .taskMovable, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with held := rem, wait := .osBlocked c id_ch lvl_ch } :: rest, sync⟩
  | blockChanBlockingRecv (u : WorldUnit Level) (predOb : LinearToken Level → Bool)
      (id_ch : ObjId) (lvl_ch : Level) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .chanBlockingRecv predOb id_ch lvl_ch →
      u.wait = .running c →
      removeFirstToken predOb u.held =
        some (.ordered id_ch lvl_ch .chanBlockingRecvOb .taskMovable, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with held := rem, wait := .osBlocked c id_ch lvl_ch } :: rest, sync⟩
  | blockBarrierWait (u : WorldUnit Level) (pred : LinearToken Level → Bool)
      (id_bar : ObjId) (lvl_bar : Level) (rem : List (LinearToken Level))
      (rest : List (WorldUnit Level)) (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .barrierWait pred id_bar lvl_bar →
      u.wait = .running c →
      sync.barrierOpen id_bar = true →
      removeFirstToken pred u.held =
        some (.ordered id_bar lvl_bar .barrierTicket .taskMovable, rem) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with held := rem, wait := .osBlocked c id_bar lvl_bar } :: rest, sync⟩
  | blockJoinWait (u : WorldUnit Level) (id_child : ObjId) (lvl_join : Level)
      (holder : UnitId) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .joinWait id_child lvl_join →
      u.wait = .running c →
      sync.childRunning id_child = some (holder, lvl_join) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with wait := .osBlocked c id_child lvl_join } :: rest, sync⟩
  | blockAsyncMutexLockAwait (u : WorldUnit Level) (id : ObjId) (lvl : Level)
      (holder : UnitId) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .asyncMutexLockAwait id lvl →
      u.wait = .running c →
      sync.asyncMutexHeld id = some (holder, lvl) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with wait := .coopBlocked id lvl } :: rest, sync⟩
  | blockAsyncAwaitPoint (u : WorldUnit Level) (id_fut : ObjId) (lvl_fut : Level)
      (holder : UnitId) (rest : List (WorldUnit Level))
      (sync : SyncState Level) (c : CarrierId) :
      u.stmt = .asyncAwaitPoint id_fut lvl_fut →
      u.wait = .running c →
      sync.futurePending id_fut = some (holder, lvl_fut) →
      WorldStep ⟨u :: rest, sync⟩
        ⟨{ u with wait := .coopBlocked id_fut lvl_fut } :: rest, sync⟩

theorem allBelow_execUnit_of_ambient {Level : Type} {prec : Level → Level → Prop}
    {u : WorldUnit Level} {lvl : Level}
    (h : AllBelow prec (tokensLevels u.held ++ ambientLevels (unitAmbient u)) lvl) :
    AllBelow prec (tokensLevels (toExecUnit u).held) lvl := by
  dsimp [toExecUnit]
  rw [tokensLevels_append, tokensLevels_onceHeldTokens]
  unfold unitAmbient at h
  rw [ambientLevels_append] at h
  exact allBelow_append (allBelow_of_append_left h)
    (allBelow_of_append_left (allBelow_of_append_right h))

theorem allBelow_rem_execUnit_of_ambient {Level : Type}
    {prec : Level → Level → Prop}
    {u : WorldUnit Level} {rem : List (LinearToken Level)} {lvl : Level}
    (h : AllBelow prec (tokensLevels rem ++ ambientLevels (unitAmbient u)) lvl) :
    AllBelow prec (tokensLevels (rem ++ onceHeldTokens u.onceFrames)) lvl := by
  rw [tokensLevels_append, tokensLevels_onceHeldTokens]
  unfold unitAmbient at h
  rw [ambientLevels_append] at h
  exact allBelow_append (allBelow_of_append_left h)
    (allBelow_of_append_left (allBelow_of_append_right h))

/-- Derive a fulfiller strictly inside `rest` from ANY fulfiller in `u :: rest`
whenever `AllBelow prec (tokensLevels (toExecUnit u).held) lvl` holds (since
`StrictDAG.irrefl` forbids `u` from holding a token at its own wait level `lvl`!). -/
theorem fulfiller_in_rest_of_allBelow {Level : Type} {prec : Level → Level → Prop}
    (dag : StrictDAG Level prec)
    {u : WorldUnit Level} {rest : List (WorldUnit Level)}
    {obj : ObjId} {lvl : Level}
    (hbelow : AllBelow prec (tokensLevels (toExecUnit u).held) lvl)
    (hv : ∃ v : WorldUnit Level, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
      ∃ k b, LinearToken.ordered obj lvl k b ∈ (toExecUnit v).held) :
    ∃ v₀ : WorldUnit Level, v₀ ∈ rest ∧ v₀.wait ≠ .finished ∧
      ∃ k b, LinearToken.ordered obj lvl k b ∈ (toExecUnit v₀).held := by
  cases hv with
  | intro v hvr =>
    cases hvr.1 with
    | tail _ hvrest => exact ⟨v, hvrest, hvr.2⟩
    | head =>
      cases hvr.2.2 with
      | intro k hr1 =>
        cases hr1 with
        | intro b htok =>
          exact False.elim (dag.irrefl lvl (hbelow lvl (ordered_mem_tokensLevels htok)))

theorem retainBlock_preserves_wt {Level : Type} {prec : Level → Level → Prop}
    (dag : StrictDAG Level prec)
    {u : WorldUnit Level} {rest : List (WorldUnit Level)}
    {obj : ObjId} {lvl : Level} {w' : UnitWait Level}
    (hwt : WellTypedWorld prec (mapExecUnits (u :: rest)))
    (hw'nf : w' ≠ .finished)
    (hw'lvl : unitWaitLevel? (toExecUnit { u with wait := w' }) = some (obj, lvl))
    (hclean : (w' = .readyQueue ∨ ∃ o l, w' = .coopBlocked o l) →
      HasNoOsBound (toExecUnit u).held)
    (hbelow : AllBelow prec (tokensLevels (toExecUnit u).held) lvl)
    (hful : ∃ v : WorldUnit Level, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
      ∃ k b, LinearToken.ordered obj lvl k b ∈ (toExecUnit v).held) :
    WellTypedWorld prec (mapExecUnits ({ u with wait := w' } :: rest)) := by
  have hrestFul := fulfiller_in_rest_of_allBelow dag hbelow hful
  refine {
    finished_empty := ?_
    live_fulfiller := ?_
    strict_wait_order := ?_
    clean_yield := ?_
  }
  · intro eu heu hfin
    cases heu with
    | head => exact False.elim (hw'nf hfin)
    | tail _ hutl => exact hwt.finished_empty eu (List.Mem.tail _ hutl) hfin
  · intro eu o l heu hwu
    cases heu with
    | head =>
      rw [hw'lvl] at hwu
      injection hwu with hp
      injection hp with ho hl
      subst ho; subst hl
      cases hrestFul with
      | intro v₀ hv₀ =>
        exact ⟨toExecUnit v₀, List.Mem.tail _ (mem_mapExecUnits hv₀.1), hv₀.2⟩
    | tail _ hutl =>
      cases hwt.live_fulfiller eu o l (List.Mem.tail _ hutl) hwu with
      | intro ev hev =>
        cases hev.1 with
        | head =>
          exact ⟨toExecUnit { u with wait := w' }, List.Mem.head _, hw'nf, hev.2.2⟩
        | tail _ hvtl =>
          exact ⟨ev, List.Mem.tail _ hvtl, hev.2⟩
  · intro eu o l heu hwu
    cases heu with
    | head =>
      rw [hw'lvl] at hwu
      injection hwu with hp
      injection hp with _ hl
      subst hl
      exact hbelow
    | tail _ hutl =>
      exact hwt.strict_wait_order eu o l (List.Mem.tail _ hutl) hwu
  · intro eu heu hy
    cases heu with
    | head => exact hclean hy
    | tail _ hutl => exact hwt.clean_yield eu (List.Mem.tail _ hutl) hy

theorem releaseBlock_noWake_preserves_wt {Level : Type}
    {prec : Level → Level → Prop}
    {u : WorldUnit Level} {rem : List (LinearToken Level)}
    {rest : List (WorldUnit Level)}
    {pred : LinearToken Level → Bool}
    {obj : ObjId} {lvl : Level} {k_rm : TokenKind} {b_rm : CarrierBinding}
    {c : CarrierId}
    (hwt : WellTypedWorld prec (mapExecUnits (u :: rest)))
    (hrem : removeFirstToken pred u.held =
      some (.ordered obj lvl k_rm b_rm, rem))
    (hbelow : AllBelow prec (tokensLevels (rem ++ onceHeldTokens u.onceFrames)) lvl)
    (hrestFul : ∃ v₀ : WorldUnit Level, v₀ ∈ rest ∧ v₀.wait ≠ .finished ∧
      ∃ k b, LinearToken.ordered obj lvl k b ∈ (toExecUnit v₀).held) :
    WellTypedWorld prec
      (mapExecUnits ({ u with held := rem, wait := .osBlocked c obj lvl } :: rest)) := by
  refine {
    finished_empty := ?_
    live_fulfiller := ?_
    strict_wait_order := ?_
    clean_yield := ?_
  }
  · intro eu heu hfin
    cases heu with
    | head => nomatch hfin
    | tail _ hutl => exact hwt.finished_empty eu (List.Mem.tail _ hutl) hfin
  · intro eu o l heu hwu
    cases heu with
    | head =>
      injection hwu with hp
      injection hp with ho hl
      subst ho; subst hl
      cases hrestFul with
      | intro v₀ hv₀ =>
        exact ⟨toExecUnit v₀, List.Mem.tail _ (mem_mapExecUnits hv₀.1), hv₀.2⟩
    | tail _ hutl =>
      cases hwt.live_fulfiller eu o l (List.Mem.tail _ hutl) hwu with
      | intro ev hev =>
        cases hev.1 with
        | tail _ hvtl => exact ⟨ev, List.Mem.tail _ hvtl, hev.2⟩
        | head =>
          cases prop_em (o = obj ∧ l = lvl) with
          | inl hsame =>
            have ho := hsame.1; have hl := hsame.2
            subst ho; subst hl
            cases hrestFul with
            | intro v₀ hv₀ =>
              exact ⟨toExecUnit v₀, List.Mem.tail _ (mem_mapExecUnits hv₀.1), hv₀.2⟩
          | inr hdiff =>
            cases hev.2.2 with
            | intro k' hr1 =>
              cases hr1 with
              | intro b' htok =>
                refine ⟨toExecUnit { u with held := rem, wait := .osBlocked c obj lvl },
                  List.Mem.head _, (fun h => nomatch h), k', b', ?_⟩
                dsimp [toExecUnit] at htok
                dsimp [toExecUnit]
                cases mem_append_or htok with
                | inr honce => exact mem_append_right honce
                | inl hheld =>
                  have hneTok : LinearToken.ordered o l k' b' ≠
                      LinearToken.ordered obj lvl k_rm b_rm := by
                    intro heq
                    injection heq with ho hl _ _
                    exact hdiff ⟨ho, hl⟩
                  exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld hneTok)
  · intro eu o l heu hwu
    cases heu with
    | head =>
      injection hwu with hp
      injection hp with _ hl
      subst hl
      exact hbelow
    | tail _ hutl =>
      exact hwt.strict_wait_order eu o l (List.Mem.tail _ hutl) hwu
  · intro eu heu hy
    cases heu with
    | head =>
      cases hy with
      | inl h => nomatch h
      | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
    | tail _ hutl => exact hwt.clean_yield eu (List.Mem.tail _ hutl) hy

theorem nonBlockReleaseWake_preserves_wt {Level : Type}
    {prec : Level → Level → Prop}
    {u : WorldUnit Level} {rem : List (LinearToken Level)}
    {rest : List (WorldUnit Level)}
    {obj_wake : ObjId} {s' : Stmt Level} {c : CarrierId}
    (hwt : WellTypedWorld prec (mapExecUnits (u :: rest)))
    (hother : ∀ (o : ObjId) (l : Level) (k : TokenKind) (b : CarrierBinding),
      o ≠ obj_wake →
      LinearToken.ordered o l k b ∈ u.held →
      LinearToken.ordered o l k b ∈ rem) :
    WellTypedWorld prec
      (mapExecUnits ({ u with stmt := s', held := rem, wait := .running c } ::
        wakeWaitersOn obj_wake rest)) := by
  refine {
    finished_empty := ?_
    live_fulfiller := ?_
    strict_wait_order := ?_
    clean_yield := ?_
  }
  · intro eu heu hfin
    cases heu with
    | head => nomatch hfin
    | tail _ hutl =>
      cases mapExecUnits_mem_inv hutl with
      | intro w' hw' =>
        cases hw' with
        | intro hw'1 hw'2 =>
          cases wakeWaitersOn_mem_inv obj_wake hw'1 with
          | intro w hw =>
            subst hw'2
            rw [← hw.2] at hfin
            have hwfin : w.wait = .finished := (wakeUnitOn_finished_iff obj_wake w).1 hfin
            have hfe := hwt.finished_empty (toExecUnit w)
              (List.Mem.tail _ (mem_mapExecUnits hw.1)) hwfin
            dsimp [toExecUnit]
            rw [← hw.2, (wakeUnitOn_preserves_fields obj_wake w).2.2.1,
              (wakeUnitOn_preserves_fields obj_wake w).2.2.2.1]
            exact hfe
  · intro eu o l heu hwu
    cases heu with
    | head => nomatch hwu
    | tail _ hutl =>
      cases mapExecUnits_mem_inv hutl with
      | intro w' hw' =>
        cases hw' with
        | intro hw'1 hw'2 =>
          cases wakeWaitersOn_mem_inv obj_wake hw'1 with
          | intro w hw =>
            subst hw'2
            rw [← hw.2] at hwu
            have hsb := wakeUnitOn_stillBlocked obj_wake w hwu
            cases hwt.live_fulfiller (toExecUnit w) o l
                (List.Mem.tail _ (mem_mapExecUnits hw.1)) hsb.2 with
            | intro ev hev =>
              cases hev.1 with
              | head =>
                cases hev.2.2 with
                | intro k' hr1 =>
                  cases hr1 with
                  | intro b' htok =>
                    refine ⟨toExecUnit { u with stmt := s', held := rem, wait := .running c },
                      List.Mem.head _, (fun h => nomatch h), k', b', ?_⟩
                    dsimp [toExecUnit] at htok
                    dsimp [toExecUnit]
                    cases mem_append_or htok with
                    | inl hheld => exact mem_append_left (hother o l k' b' hsb.1 hheld)
                    | inr honce => exact mem_append_right honce
              | tail _ hvtl =>
                cases mapExecUnits_mem_inv hvtl with
                | intro v hv =>
                  rw [← hv.2] at hev
                  have hvnf : (wakeUnitOn obj_wake v).wait ≠ .finished :=
                    fun hf => hev.2.1 ((wakeUnitOn_finished_iff obj_wake v).1 hf)
                  refine ⟨toExecUnit (wakeUnitOn obj_wake v),
                    List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn obj_wake hv.1)),
                    hvnf, ?_⟩
                  dsimp [toExecUnit]
                  rw [(wakeUnitOn_preserves_fields obj_wake v).2.2.1,
                    (wakeUnitOn_preserves_fields obj_wake v).2.2.2.1]
                  exact hev.2.2
  · intro eu o l heu hwu
    cases heu with
    | head => nomatch hwu
    | tail _ hutl =>
      cases mapExecUnits_mem_inv hutl with
      | intro w' hw' =>
        cases hw' with
        | intro hw'1 hw'2 =>
          cases wakeWaitersOn_mem_inv obj_wake hw'1 with
          | intro w hw =>
            subst hw'2
            rw [← hw.2] at hwu
            have hsb := wakeUnitOn_stillBlocked obj_wake w hwu
            have hall := hwt.strict_wait_order (toExecUnit w) o l
              (List.Mem.tail _ (mem_mapExecUnits hw.1)) hsb.2
            dsimp [toExecUnit]
            rw [← hw.2, (wakeUnitOn_preserves_fields obj_wake w).2.2.1,
              (wakeUnitOn_preserves_fields obj_wake w).2.2.2.1]
            exact hall
  · intro eu heu hy
    cases heu with
    | head =>
      cases hy with
      | inl h => nomatch h
      | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
    | tail _ hutl =>
      cases mapExecUnits_mem_inv hutl with
      | intro w' hw' =>
        cases hw' with
        | intro hw'1 hw'2 =>
          cases wakeWaitersOn_mem_inv obj_wake hw'1 with
          | intro w hw =>
            subst hw'2
            rw [← hw.2] at hy
            dsimp [toExecUnit] at hy
            have hyPre := wakeUnitOn_preserves_yield obj_wake w hy
            have hcl := hwt.clean_yield (toExecUnit w)
              (List.Mem.tail _ (mem_mapExecUnits hw.1)) hyPre
            dsimp [toExecUnit]
            rw [← hw.2, (wakeUnitOn_preserves_fields obj_wake w).2.2.1,
              (wakeUnitOn_preserves_fields obj_wake w).2.2.2.1]
            exact hcl

theorem mapExecUnits_append {Level : Type} (xs ys : List (WorldUnit Level)) :
    mapExecUnits (xs ++ ys) = mapExecUnits xs ++ mapExecUnits ys := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    dsimp [mapExecUnits]
    rw [ih]

/-- Master Non-Circular Step-Preservation Theorem
(`worldStep_preserves_wellTypedWorld`):
for EVERY `WorldStep w w'` (all non-blocking steps `scheduleRotate`, `seqSkip`,
`unlockMutex`, `unlockAsyncMutex`, `condvarNotify`, `chanCreditSend`,
`enterOnce`, `forkRayonJoin`, AND all blocking steps `blockMutexLock`,
`blockRwReadWriterPref`, `blockRwWrite`, `blockOnceWait`, `blockCondvarWait`,
`blockChanCreditRecv`, `blockChanBlockingSend`, `blockChanBlockingRecv`,
`blockBarrierWait`, `blockJoinWait`, `blockAsyncMutexLockAwait`,
`blockAsyncAwaitPoint` — including steps executed INSIDE `onceCall` bodies and
`rayonJoin` branches!), `TokenConservingWorld prec w` implies:
1. `WellTypedWorld prec (mapExecUnits w'.units)` (with `live_fulfiller` DERIVED
   from `TokenConservingWorld`, zero premise-baking!),
2. `∀ S, ¬ IsClosedBlockedSet (mapExecUnits w'.units) S`,
3. `CondvarCoupledInv` preserved for all condvars, AND
4. `.creditManaged` channel slot conservation preserved for all channels! -/
theorem worldStep_preserves_wellTypedWorld {Level : Type}
    {prec : Level → Level → Prop}
    (dag : StrictDAG Level prec)
    {w w' : TokenWorld Level}
    (hcons : TokenConservingWorld prec w)
    (hstep : WorldStep w w') :
    WellTypedWorld prec (mapExecUnits w'.units) ∧
    (∀ S, ¬ IsClosedBlockedSet (mapExecUnits w'.units) S) ∧
    (∀ id_cvar, CondvarCoupledInv (mapExecUnits w'.units) id_cvar
      (w'.sync.condvarLevel id_cvar) (w'.sync.condvarNotified id_cvar)) ∧
    (∀ id_ch, w'.sync.chanMode id_ch = .creditManaged →
      countCapSlotsWorld id_ch w'.units + w'.sync.chanBuf id_ch =
        w'.sync.chanCap id_ch) := by
  have hwt := hcons.world_wt
  have hTypedOut : ∀ u : WorldUnit Level, u ∈ w.units → u.wait ≠ .finished →
      ∃ outU, TypedStmt prec (unitAmbient u) u.stmt u.held outU :=
    fun u hu hnf => ⟨u.outTokens, (hcons.units_typed u hu).2 hnf⟩
  have hRayonInv : ∀ (amb : List (Level × CarrierBinding))
      (held_f held_g held out : List (LinearToken Level)) (f g : Stmt Level),
      TypedStmt prec amb (.rayonJoin held_f held_g f g) held out →
      HasNoOsBound held_g ∧ HasNoOsBoundAmbient amb := by
    intro amb held_f held_g held out f g ht
    cases ht with
    | rayonJoin _ hnoG _ _ hnoAmb _ _ => exact ⟨hnoG, hnoAmb⟩
  have hmain : WellTypedWorld prec (mapExecUnits w'.units) ∧
      (∀ id_cvar, CondvarCoupledInv (mapExecUnits w'.units) id_cvar
        (w'.sync.condvarLevel id_cvar) (w'.sync.condvarNotified id_cvar)) ∧
      (∀ id_ch, w'.sync.chanMode id_ch = .creditManaged →
        countCapSlotsWorld id_ch w'.units + w'.sync.chanBuf id_ch =
          w'.sync.chanCap id_ch) := by
    cases hstep with
    | scheduleRotate u rest sync =>
      have hmemIff : ∀ x : ExecUnit Level,
          x ∈ mapExecUnits (rest ++ [u]) ↔ x ∈ mapExecUnits (u :: rest) := by
        intro x
        rw [mapExecUnits_append]
        refine ⟨?_, ?_⟩
        · intro hx
          cases mem_append_or hx with
          | inl hr => exact List.Mem.tail _ hr
          | inr hu =>
            cases hu with
            | head => exact List.Mem.head _
            | tail _ hn => nomatch hn
        · intro hx
          cases hx with
          | head => exact mem_append_right (List.Mem.head _)
          | tail _ hr => exact mem_append_left hr
      refine ⟨?_, ?_, ?_⟩
      · refine {
          finished_empty := fun eu heu hf => hwt.finished_empty eu ((hmemIff eu).1 heu) hf
          live_fulfiller := fun eu o l heu hwu => by
            cases hwt.live_fulfiller eu o l ((hmemIff eu).1 heu) hwu with
            | intro ev hev => exact ⟨ev, (hmemIff ev).2 hev.1, hev.2⟩
          strict_wait_order := fun eu o l heu hwu =>
            hwt.strict_wait_order eu o l ((hmemIff eu).1 heu) hwu
          clean_yield := fun eu heu hy => hwt.clean_yield eu ((hmemIff eu).1 heu) hy
        }
      · intro id_cvar hnf
        cases hcons.condvar_coupled id_cvar hnf with
        | intro v hv => exact ⟨v, (hmemIff v).2 hv.1, hv.2⟩
      · intro id_ch hmode
        dsimp
        rw [countCapSlotsWorld_append]
        have h0 := hcons.creditChan_conserved id_ch hmode
        dsimp [countCapSlotsWorld] at h0
        dsimp [countCapSlotsWorld]
        rw [Nat.add_comm (countCapSlotsWorld id_ch rest)]
        exact h0
    | seqSkip u s₂ rest sync c hstmt hwait =>
      have hsame : mapExecUnits ({ u with stmt := s₂ } :: rest) =
          mapExecUnits (u :: rest) := rfl
      refine ⟨by rw [hsame]; exact hwt,
        by intro id_cvar; rw [hsame]; exact hcons.condvar_coupled id_cvar,
        hcons.creditChan_conserved⟩
    | unlockMutex u pred id lvl rem rest sync c hstmt hwait hrem =>
      have hwt' : WellTypedWorld prec
          (mapExecUnits ({ u with stmt := .skip, held := rem } :: wakeWaitersOn id rest)) := by
        have h' := nonBlockReleaseWake_preserves_wt (u := u) (rem := rem) (rest := rest)
          (obj_wake := id) (s' := .skip) (c := c) hwt (fun o l k b hne hmem => by
            have hneTok : LinearToken.ordered o l k b ≠
                LinearToken.ordered id lvl .mutexGuard .osBound := by
              intro heq; injection heq with ho _ _ _; exact hne ho
            exact removeFirstToken_other_mem_rem hrem hmem hneTok)
        have heqW : { u with stmt := .skip, held := rem, wait := .running c } =
            { u with stmt := .skip, held := rem } := by
          cases u; dsimp at hwait; subst hwait; rfl
        rw [heqW] at h'
        exact h'
      refine ⟨hwt', ?_, ?_⟩
      · intro id_cvar hnf
        cases hcons.condvar_coupled id_cvar hnf with
        | intro v hv =>
          cases hv.1 with
          | head =>
            refine ⟨toExecUnit { u with stmt := .skip, held := rem },
              List.Mem.head _, (by dsimp [toExecUnit]; rw [hwait]; exact fun h => nomatch h), ?_⟩
            dsimp [toExecUnit] at hv
            dsimp [toExecUnit]
            cases mem_append_or hv.2.2 with
            | inr honce => exact mem_append_right honce
            | inl hheld =>
              exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                (fun heq => by injection heq with _ _ hk _; nomatch hk))
          | tail _ hvtl =>
            cases mapExecUnits_mem_inv hvtl with
            | intro vw hvw =>
              rw [← hvw.2] at hv
              refine ⟨toExecUnit (wakeUnitOn id vw),
                List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn id hvw.1)),
                fun hf => hv.2.1 ((wakeUnitOn_finished_iff id vw).1 hf), ?_⟩
              dsimp [toExecUnit]
              rw [(wakeUnitOn_preserves_fields id vw).2.2.1,
                (wakeUnitOn_preserves_fields id vw).2.2.2.1]
              exact hv.2.2
      · intro id_ch hmode
        dsimp [countCapSlotsWorld]
        rw [countCapSlotsWorld_wakeWaitersOn, ← countCapSlotsInList_removeOrdered id_ch hrem]
        exact hcons.creditChan_conserved id_ch hmode
    | unlockAsyncMutex u pred id lvl rem rest sync c hstmt hwait hrem =>
      have hwt' : WellTypedWorld prec
          (mapExecUnits ({ u with stmt := .skip, held := rem } :: wakeWaitersOn id rest)) := by
        have h' := nonBlockReleaseWake_preserves_wt (u := u) (rem := rem) (rest := rest)
          (obj_wake := id) (s' := .skip) (c := c) hwt (fun o l k b hne hmem => by
            have hneTok : LinearToken.ordered o l k b ≠
                LinearToken.ordered id lvl .asyncMutexGuard .taskMovable := by
              intro heq; injection heq with ho _ _ _; exact hne ho
            exact removeFirstToken_other_mem_rem hrem hmem hneTok)
        have heqW : { u with stmt := .skip, held := rem, wait := .running c } =
            { u with stmt := .skip, held := rem } := by
          cases u; dsimp at hwait; subst hwait; rfl
        rw [heqW] at h'
        exact h'
      refine ⟨hwt', ?_, ?_⟩
      · intro id_cvar hnf
        cases hcons.condvar_coupled id_cvar hnf with
        | intro v hv =>
          cases hv.1 with
          | head =>
            refine ⟨toExecUnit { u with stmt := .skip, held := rem },
              List.Mem.head _, (by dsimp [toExecUnit]; rw [hwait]; exact fun h => nomatch h), ?_⟩
            dsimp [toExecUnit] at hv
            dsimp [toExecUnit]
            cases mem_append_or hv.2.2 with
            | inr honce => exact mem_append_right honce
            | inl hheld =>
              exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                (fun heq => by injection heq with _ _ hk _; nomatch hk))
          | tail _ hvtl =>
            cases mapExecUnits_mem_inv hvtl with
            | intro vw hvw =>
              rw [← hvw.2] at hv
              refine ⟨toExecUnit (wakeUnitOn id vw),
                List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn id hvw.1)),
                fun hf => hv.2.1 ((wakeUnitOn_finished_iff id vw).1 hf), ?_⟩
              dsimp [toExecUnit]
              rw [(wakeUnitOn_preserves_fields id vw).2.2.1,
                (wakeUnitOn_preserves_fields id vw).2.2.2.1]
              exact hv.2.2
      · intro id_ch hmode
        dsimp [countCapSlotsWorld]
        rw [countCapSlotsWorld_wakeWaitersOn, ← countCapSlotsInList_removeOrdered id_ch hrem]
        exact hcons.creditChan_conserved id_ch hmode
    | condvarNotify u pred id_lock id_cvar lvl_cvar rem rest sync c hstmt hwait hrem =>
      have hwt' : WellTypedWorld prec
          (mapExecUnits ({ u with stmt := .skip, held := rem } :: wakeWaitersOn id_cvar rest)) := by
        have h' := nonBlockReleaseWake_preserves_wt (u := u) (rem := rem) (rest := rest)
          (obj_wake := id_cvar) (s' := .skip) (c := c) hwt (fun o l k b hne hmem => by
            have hneTok : LinearToken.ordered o l k b ≠
                LinearToken.ordered id_cvar lvl_cvar .condvarSignalOb .taskMovable := by
              intro heq; injection heq with ho _ _ _; exact hne ho
            exact removeFirstToken_other_mem_rem hrem hmem hneTok)
        have heqW : { u with stmt := .skip, held := rem, wait := .running c } =
            { u with stmt := .skip, held := rem } := by
          cases u; dsimp at hwait; subst hwait; rfl
        rw [heqW] at h'
        exact h'
      refine ⟨hwt', ?_, ?_⟩
      · intro id_c hnf
        dsimp [funUpdate] at hnf
        cases hb : Nat.beq id_c id_cvar with
        | true => rw [hb] at hnf; nomatch hnf
        | false =>
          rw [hb] at hnf; dsimp at hnf
          have hneId : id_c ≠ id_cvar := by
            intro heq; subst heq; rw [Nat.beq_refl id_c] at hb; nomatch hb
          cases hcons.condvar_coupled id_c hnf with
          | intro v hv =>
            cases hv.1 with
            | head =>
              refine ⟨toExecUnit { u with stmt := .skip, held := rem },
                List.Mem.head _, (by dsimp [toExecUnit]; rw [hwait]; exact fun h => nomatch h), ?_⟩
              dsimp [toExecUnit] at hv
              dsimp [toExecUnit]
              cases mem_append_or hv.2.2 with
              | inr honce => exact mem_append_right honce
              | inl hheld =>
                exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                  (fun heq => by injection heq with ho _ _ _; exact hneId ho))
            | tail _ hvtl =>
              cases mapExecUnits_mem_inv hvtl with
              | intro vw hvw =>
                rw [← hvw.2] at hv
                refine ⟨toExecUnit (wakeUnitOn id_cvar vw),
                  List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn id_cvar hvw.1)),
                  fun hf => hv.2.1 ((wakeUnitOn_finished_iff id_cvar vw).1 hf), ?_⟩
                dsimp [toExecUnit]
                rw [(wakeUnitOn_preserves_fields id_cvar vw).2.2.1,
                  (wakeUnitOn_preserves_fields id_cvar vw).2.2.2.1]
                exact hv.2.2
      · intro id_ch hmode
        dsimp [countCapSlotsWorld]
        rw [countCapSlotsWorld_wakeWaitersOn, ← countCapSlotsInList_removeOrdered id_ch hrem]
        exact hcons.creditChan_conserved id_ch hmode
    | chanCreditSend u predOb predCap id_ch lvl_ch mid rem rest sync c hstmt hwait hob hcap =>
      have hwt' : WellTypedWorld prec
          (mapExecUnits ({ u with stmt := .skip, held := rem } :: wakeWaitersOn id_ch rest)) := by
        have h' := nonBlockReleaseWake_preserves_wt (u := u) (rem := rem) (rest := rest)
          (obj_wake := id_ch) (s' := .skip) (c := c) hwt (fun o l k b hne hmem => by
            have hmid : LinearToken.ordered o l k b ∈ mid :=
              removeFirstToken_other_mem_rem hob hmem
                (fun heq => by injection heq with ho _ _ _; exact hne ho)
            exact removeFirstToken_other_mem_rem hcap hmid (fun heq => nomatch heq))
        have heqW : { u with stmt := .skip, held := rem, wait := .running c } =
            { u with stmt := .skip, held := rem } := by
          cases u; dsimp at hwait; subst hwait; rfl
        rw [heqW] at h'
        exact h'
      refine ⟨hwt', ?_, ?_⟩
      · intro id_c hnf
        cases hcons.condvar_coupled id_c hnf with
        | intro v hv =>
          cases hv.1 with
          | head =>
            refine ⟨toExecUnit { u with stmt := .skip, held := rem },
              List.Mem.head _, (by dsimp [toExecUnit]; rw [hwait]; exact fun h => nomatch h), ?_⟩
            dsimp [toExecUnit] at hv
            dsimp [toExecUnit]
            cases mem_append_or hv.2.2 with
            | inr honce => exact mem_append_right honce
            | inl hheld =>
              have hmid := removeFirstToken_other_mem_rem hob hheld
                (fun heq => by injection heq with _ _ hk _; nomatch hk)
              exact mem_append_left (removeFirstToken_other_mem_rem hcap hmid
                (fun heq => nomatch heq))
          | tail _ hvtl =>
            cases mapExecUnits_mem_inv hvtl with
            | intro vw hvw =>
              rw [← hvw.2] at hv
              refine ⟨toExecUnit (wakeUnitOn id_ch vw),
                List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn id_ch hvw.1)),
                fun hf => hv.2.1 ((wakeUnitOn_finished_iff id_ch vw).1 hf), ?_⟩
              dsimp [toExecUnit]
              rw [(wakeUnitOn_preserves_fields id_ch vw).2.2.1,
                (wakeUnitOn_preserves_fields id_ch vw).2.2.2.1]
              exact hv.2.2
      · intro id_q hmode
        have hprev := hcons.creditChan_conserved id_q hmode
        dsimp [countCapSlotsWorld] at hprev
        dsimp [countCapSlotsWorld, funUpdate]
        rw [countCapSlotsWorld_wakeWaitersOn]
        have h1 := countCapSlotsInList_removeOrdered id_q hob
        have h2 := countCapSlotsInList_removeCapSlot id_q hcap
        rw [h1, h2] at hprev
        cases hb : Nat.beq id_q id_ch with
        | true =>
          have heq : id_q = id_ch := Nat.eq_of_beq_eq_true hb
          subst heq
          rw [Nat.beq_refl id_q] at hprev
          dsimp at hprev
          dsimp
          rw [Nat.add_assoc 1 (countCapSlotsInList id_q rem) (countCapSlotsWorld id_q rest),
            Nat.add_comm 1 (countCapSlotsInList id_q rem + countCapSlotsWorld id_q rest),
            Nat.add_assoc _ 1 (sync.chanBuf id_q),
            Nat.add_comm 1 (sync.chanBuf id_q)] at hprev
          exact hprev
        | false =>
          have hbf : Nat.beq id_ch id_q = false := by
            cases h2b : Nat.beq id_ch id_q with
            | false => rfl
            | true =>
              have heq := Nat.eq_of_beq_eq_true h2b
              subst heq; rw [Nat.beq_refl id_ch] at hb; nomatch hb
          rw [hbf] at hprev
          dsimp at hprev
          rw [Nat.zero_add] at hprev
          exact hprev
    | enterOnce u id_once lvl_once body rest sync c hstmt hwait _ =>
      let u' : WorldUnit Level :=
        { u with stmt := body, onceFrames := (id_once, lvl_once) :: u.onceFrames }
      have hwt' : WellTypedWorld prec (mapExecUnits (u' :: rest)) := by
        refine {
          finished_empty := ?_
          live_fulfiller := ?_
          strict_wait_order := ?_
          clean_yield := ?_
        }
        · intro eu heu hfin
          cases heu with
          | head => dsimp [toExecUnit, u'] at hfin; rw [hwait] at hfin; nomatch hfin
          | tail _ hutl => exact hwt.finished_empty eu (List.Mem.tail _ hutl) hfin
        · intro eu o l heu hwu
          cases heu with
          | head => dsimp [toExecUnit, unitWaitLevel?, u'] at hwu; rw [hwait] at hwu; nomatch hwu
          | tail _ hutl =>
            cases hwt.live_fulfiller eu o l (List.Mem.tail _ hutl) hwu with
            | intro ev hev =>
              cases hev.1 with
              | tail _ hvtl => exact ⟨ev, List.Mem.tail _ hvtl, hev.2⟩
              | head =>
                cases hev.2.2 with
                | intro k hr1 =>
                  cases hr1 with
                  | intro b htok =>
                    refine ⟨toExecUnit u', List.Mem.head _,
                      (by dsimp [toExecUnit, u']; rw [hwait]; exact fun h => nomatch h),
                      k, b, ?_⟩
                    dsimp [toExecUnit] at htok
                    dsimp [toExecUnit, u', onceHeldTokens]
                    cases mem_append_or htok with
                    | inl hh => exact mem_append_left hh
                    | inr ho => exact mem_append_right (List.Mem.tail _ ho)
        · intro eu o l heu hwu
          cases heu with
          | head => dsimp [toExecUnit, unitWaitLevel?, u'] at hwu; rw [hwait] at hwu; nomatch hwu
          | tail _ hutl => exact hwt.strict_wait_order eu o l (List.Mem.tail _ hutl) hwu
        · intro eu heu hy
          cases heu with
          | head =>
            dsimp [toExecUnit, u'] at hy
            rw [hwait] at hy
            cases hy with
            | inl h => nomatch h
            | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
          | tail _ hutl => exact hwt.clean_yield eu (List.Mem.tail _ hutl) hy
      refine ⟨hwt', ?_, hcons.creditChan_conserved⟩
      intro id_c hnf
      cases hcons.condvar_coupled id_c hnf with
      | intro v hv =>
        cases hv.1 with
        | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
        | head =>
          refine ⟨toExecUnit u', List.Mem.head _,
            (by dsimp [toExecUnit, u']; rw [hwait]; exact fun h => nomatch h), ?_⟩
          dsimp [toExecUnit] at hv
          dsimp [toExecUnit, u', onceHeldTokens]
          cases mem_append_or hv.2.2 with
          | inl hh => exact mem_append_left hh
          | inr ho => exact mem_append_right (List.Mem.tail _ ho)
    | forkRayonJoin u held_f held_g held_f' held_g' f g uid_g rest sync c hstmt hwait hheld hout =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; exact fun h => nomatch h)
      rw [hstmt] at htypedU
      cases hRayonInv _ _ _ _ _ _ _ htypedU with
      | intro hnoG hnoAmb =>
        have hframesNil : u.onceFrames = [] := onceFrames_nil_of_noOsBoundAmbient hnoAmb
        let uF : WorldUnit Level :=
          { uid := u.uid, stmt := f, held := held_f, onceFrames := [],
            extraAmbient := tokensAmbient held_g ++ tokensAmbient held_g' ++ u.extraAmbient,
            outTokens := held_f', wait := .running c }
        let uG : WorldUnit Level :=
          { uid := uid_g, stmt := g, held := held_g, onceFrames := [],
            extraAmbient := tokensAmbient held_f ++ tokensAmbient held_f' ++ u.extraAmbient,
            outTokens := held_g', wait := .readyQueue }
        have hwt' : WellTypedWorld prec (mapExecUnits (uF :: uG :: rest)) := by
          refine {
            finished_empty := ?_
            live_fulfiller := ?_
            strict_wait_order := ?_
            clean_yield := ?_
          }
          · intro eu heu hfin
            cases heu with
            | head => nomatch hfin
            | tail _ h2 =>
              cases h2 with
              | head => nomatch hfin
              | tail _ hutl => exact hwt.finished_empty eu (List.Mem.tail _ hutl) hfin
          · intro eu o l heu hwu
            cases heu with
            | head => nomatch hwu
            | tail _ h2 =>
              cases h2 with
              | head => nomatch hwu
              | tail _ hutl =>
                cases hwt.live_fulfiller eu o l (List.Mem.tail _ hutl) hwu with
                | intro ev hev =>
                  cases hev.1 with
                  | tail _ hvtl =>
                    exact ⟨ev, List.Mem.tail _ (List.Mem.tail _ hvtl), hev.2⟩
                  | head =>
                    cases hev.2.2 with
                    | intro k hr1 =>
                      cases hr1 with
                      | intro b htok =>
                        dsimp [toExecUnit] at htok
                        rw [hheld, hframesNil] at htok
                        dsimp [onceHeldTokens] at htok
                        rw [List.append_nil] at htok
                        cases mem_append_or htok with
                        | inl hf =>
                          refine ⟨toExecUnit uF, List.Mem.head _,
                            (fun h => nomatch h), k, b, ?_⟩
                          dsimp [toExecUnit, uF, onceHeldTokens]
                          rw [List.append_nil]; exact hf
                        | inr hg =>
                          refine ⟨toExecUnit uG, List.Mem.tail _ (List.Mem.head _),
                            (fun h => nomatch h), k, b, ?_⟩
                          dsimp [toExecUnit, uG, onceHeldTokens]
                          rw [List.append_nil]; exact hg
          · intro eu o l heu hwu
            cases heu with
            | head => nomatch hwu
            | tail _ h2 =>
              cases h2 with
              | head => nomatch hwu
              | tail _ hutl => exact hwt.strict_wait_order eu o l (List.Mem.tail _ hutl) hwu
          · intro eu heu hy
            cases heu with
            | head =>
              cases hy with
              | inl h => nomatch h
              | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
            | tail _ h2 =>
              cases h2 with
              | head =>
                dsimp [toExecUnit, uG, onceHeldTokens]
                rw [List.append_nil]
                exact hnoG
              | tail _ hutl => exact hwt.clean_yield eu (List.Mem.tail _ hutl) hy
        refine ⟨hwt', ?_, ?_⟩
        · intro id_c hnf
          cases hcons.condvar_coupled id_c hnf with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvtl => exact ⟨v, List.Mem.tail _ (List.Mem.tail _ hvtl), hv.2⟩
            | head =>
              dsimp [toExecUnit] at hv
              rw [hheld, hframesNil] at hv
              dsimp [onceHeldTokens] at hv
              rw [List.append_nil] at hv
              cases mem_append_or hv.2.2 with
              | inl hf =>
                refine ⟨toExecUnit uF, List.Mem.head _, (fun h => nomatch h), ?_⟩
                dsimp [toExecUnit, uF, onceHeldTokens]; rw [List.append_nil]; exact hf
              | inr hg =>
                refine ⟨toExecUnit uG, List.Mem.tail _ (List.Mem.head _),
                  (fun h => nomatch h), ?_⟩
                dsimp [toExecUnit, uG, onceHeldTokens]; rw [List.append_nil]; exact hg
        · intro id_ch hmode
          have hprev := hcons.creditChan_conserved id_ch hmode
          dsimp [countCapSlotsWorld] at hprev
          rw [hheld, countCapSlotsInList_append] at hprev
          dsimp [countCapSlotsWorld]
          rw [← Nat.add_assoc]
          exact hprev
    | blockMutexLock u id lvl holder rest sync c hstmt hwait hm =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      have hbelow := typedStmt_mutexLock_inv htypedU
      have hful : ∃ v, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
          ∃ k b, LinearToken.ordered id lvl k b ∈ (toExecUnit v).held := by
        cases hcons.mutex_conserved id holder lvl hm with
        | intro v hv =>
          exact ⟨v, hv.1, hv.2.1, .mutexGuard, .osBound, mem_append_left hv.2.2⟩
      refine ⟨retainBlock_preserves_wt dag hwt (by intro h; nomatch h) rfl
        (fun hy => by cases hy with | inl h => nomatch h | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3)
        (allBelow_execUnit_of_ambient hbelow) hful,
        ?_, hcons.creditChan_conserved⟩
      intro id_c hnf
      cases hcons.condvar_coupled id_c hnf with
      | intro v hv =>
        cases hv.1 with
        | head => exact ⟨toExecUnit { u with wait := .osBlocked c id lvl }, List.Mem.head _, (by intro h; nomatch h), hv.2.2⟩
        | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
    | blockRwReadWriterPref u id lvl holder rest sync c hstmt hwait hrw =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      have hbelow := typedStmt_rwReadWriterPref_inv htypedU
      have hful : ∃ v, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
          ∃ k b, LinearToken.ordered id lvl k b ∈ (toExecUnit v).held := by
        cases hcons.rw_conserved id holder lvl hrw with
        | intro v hv =>
          cases hv.2.2 with | intro k hr1 => cases hr1 with | intro b htok =>
            exact ⟨v, hv.1, hv.2.1, k, b, mem_append_left htok⟩
      refine ⟨retainBlock_preserves_wt dag hwt (by intro h; nomatch h) rfl
        (fun hy => by cases hy with | inl h => nomatch h | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3)
        (allBelow_execUnit_of_ambient hbelow) hful,
        ?_, hcons.creditChan_conserved⟩
      intro id_c hnf
      cases hcons.condvar_coupled id_c hnf with
      | intro v hv =>
        cases hv.1 with
        | head => exact ⟨toExecUnit { u with wait := .osBlocked c id lvl }, List.Mem.head _, (by intro h; nomatch h), hv.2.2⟩
        | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
    | blockRwWrite u id lvl holder rest sync c hstmt hwait hrw =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      have hbelow := typedStmt_rwWrite_inv htypedU
      have hful : ∃ v, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
          ∃ k b, LinearToken.ordered id lvl k b ∈ (toExecUnit v).held := by
        cases hcons.rw_conserved id holder lvl hrw with
        | intro v hv =>
          cases hv.2.2 with | intro k hr1 => cases hr1 with | intro b htok =>
            exact ⟨v, hv.1, hv.2.1, k, b, mem_append_left htok⟩
      refine ⟨retainBlock_preserves_wt dag hwt (by intro h; nomatch h) rfl
        (fun hy => by cases hy with | inl h => nomatch h | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3)
        (allBelow_execUnit_of_ambient hbelow) hful,
        ?_, hcons.creditChan_conserved⟩
      intro id_c hnf
      cases hcons.condvar_coupled id_c hnf with
      | intro v hv =>
        cases hv.1 with
        | head => exact ⟨toExecUnit { u with wait := .osBlocked c id lvl }, List.Mem.head _, (by intro h; nomatch h), hv.2.2⟩
        | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
    | blockOnceWait u id_once lvl_once body holder rest sync c hstmt hwait honce =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      cases htypedU with
      | onceCall _ _ _ hbelow _ =>
        have hful : ∃ v, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
            ∃ k b, LinearToken.ordered id_once lvl_once k b ∈ (toExecUnit v).held := by
          cases hcons.once_conserved id_once holder lvl_once honce with
          | intro v hv =>
            exact ⟨v, hv.1, hv.2.1, .onceInitGuard, .osBound,
              mem_append_right (mem_onceHeldTokens_of_mem hv.2.2)⟩
        refine ⟨retainBlock_preserves_wt dag hwt (by intro h; nomatch h) rfl
          (fun hy => by cases hy with | inl h => nomatch h | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3)
          (allBelow_execUnit_of_ambient hbelow) hful,
          ?_, hcons.creditChan_conserved⟩
        intro id_c hnf
        cases hcons.condvar_coupled id_c hnf with
        | intro v hv =>
          cases hv.1 with
          | head => exact ⟨toExecUnit { u with wait := .osBlocked c id_once lvl_once }, List.Mem.head _, (by intro h; nomatch h), hv.2.2⟩
          | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
    | blockCondvarWait u pred id_lock lvl_lock id_cvar lvl_cvar mode rem rest sync c hstmt hwait hclvl hcnf hrem =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      cases typedStmt_condvarWait_inv htypedU with
      | intro remT hinv =>
        have hremT := hinv.2.1
        have hbelowCvar := hinv.2.2
        rw [hrem] at hremT
        injection hremT with hp
        injection hp with _ hremEq
        subst hremEq
        have hbelowExec := allBelow_rem_execUnit_of_ambient hbelowCvar
        have hcoupled := hcons.condvar_coupled id_cvar
        rw [hclvl] at hcoupled
        have hfulRest : ∃ v₀ : WorldUnit Level, v₀ ∈ rest ∧ v₀.wait ≠ .finished ∧
            LinearToken.ordered id_cvar lvl_cvar .condvarSignalOb .taskMovable ∈ (toExecUnit v₀).held := by
          cases hcoupled hcnf with
          | intro ev hev =>
            cases hev.1 with
            | tail _ hvtl =>
              cases mapExecUnits_mem_inv hvtl with
              | intro v₀ hv₀ =>
                rw [← hv₀.2] at hev
                exact ⟨v₀, hv₀.1, hev.2.1, hev.2.2⟩
            | head =>
              dsimp [toExecUnit] at hev
              have hinRem : LinearToken.ordered id_cvar lvl_cvar .condvarSignalOb .taskMovable ∈
                  rem ++ onceHeldTokens u.onceFrames := by
                cases mem_append_or hev.2.2 with
                | inr honce => exact mem_append_right honce
                | inl hheld =>
                  exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                    (fun heq => by injection heq with _ _ hk _; nomatch hk))
              exact False.elim (dag.irrefl lvl_cvar
                (hbelowExec lvl_cvar (ordered_mem_tokensLevels hinRem)))
        have hwt' : WellTypedWorld prec
            (mapExecUnits ({ u with held := rem, wait := .osBlocked c id_cvar lvl_cvar } ::
              wakeWaitersOn id_lock rest)) := by
          refine {
            finished_empty := ?_
            live_fulfiller := ?_
            strict_wait_order := ?_
            clean_yield := ?_
          }
          · intro eu heu hfin
            cases heu with
            | head => nomatch hfin
            | tail _ hutl =>
              cases mapExecUnits_mem_inv hutl with
              | intro w' hw' =>
                cases hw' with
                | intro hw'1 hw'2 =>
                  cases wakeWaitersOn_mem_inv id_lock hw'1 with
                  | intro w hw =>
                    subst hw'2
                    rw [← hw.2] at hfin
                    have hwfin := (wakeUnitOn_finished_iff id_lock w).1 hfin
                    have hfe := hwt.finished_empty (toExecUnit w)
                      (List.Mem.tail _ (mem_mapExecUnits hw.1)) hwfin
                    dsimp [toExecUnit]
                    rw [← hw.2, (wakeUnitOn_preserves_fields id_lock w).2.2.1,
                      (wakeUnitOn_preserves_fields id_lock w).2.2.2.1]
                    exact hfe
          · intro eu o l heu hwu
            cases heu with
            | head =>
              injection hwu with hp2
              injection hp2 with ho hl
              subst ho; subst hl
              cases hfulRest with
              | intro v₀ hv₀ =>
                refine ⟨toExecUnit (wakeUnitOn id_lock v₀),
                  List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn id_lock hv₀.1)),
                  fun hf => hv₀.2.1 ((wakeUnitOn_finished_iff id_lock v₀).1 hf),
                  .condvarSignalOb, .taskMovable, ?_⟩
                dsimp [toExecUnit]
                rw [(wakeUnitOn_preserves_fields id_lock v₀).2.2.1,
                  (wakeUnitOn_preserves_fields id_lock v₀).2.2.2.1]
                exact hv₀.2.2
            | tail _ hutl =>
              cases mapExecUnits_mem_inv hutl with
              | intro w' hw' =>
                cases hw' with
                | intro hw'1 hw'2 =>
                  cases wakeWaitersOn_mem_inv id_lock hw'1 with
                  | intro w hw =>
                    subst hw'2
                    rw [← hw.2] at hwu
                    have hsb := wakeUnitOn_stillBlocked id_lock w hwu
                    cases hwt.live_fulfiller (toExecUnit w) o l
                        (List.Mem.tail _ (mem_mapExecUnits hw.1)) hsb.2 with
                    | intro ev hev =>
                      cases hev.1 with
                      | head =>
                        cases hev.2.2 with
                        | intro k' hr1 =>
                          cases hr1 with
                          | intro b' htok =>
                            refine ⟨toExecUnit { u with held := rem, wait := .osBlocked c id_cvar lvl_cvar },
                              List.Mem.head _, (by intro h; nomatch h), k', b', ?_⟩
                            dsimp [toExecUnit] at htok
                            dsimp [toExecUnit]
                            cases mem_append_or htok with
                            | inr honce => exact mem_append_right honce
                            | inl hheld =>
                              exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                                (fun heq => by injection heq with ho _ _ _; exact hsb.1 ho))
                      | tail _ hvtl =>
                        cases mapExecUnits_mem_inv hvtl with
                        | intro v hv =>
                          rw [← hv.2] at hev
                          refine ⟨toExecUnit (wakeUnitOn id_lock v),
                            List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn id_lock hv.1)),
                            fun hf => hev.2.1 ((wakeUnitOn_finished_iff id_lock v).1 hf), ?_⟩
                          dsimp [toExecUnit]
                          rw [(wakeUnitOn_preserves_fields id_lock v).2.2.1,
                            (wakeUnitOn_preserves_fields id_lock v).2.2.2.1]
                          exact hev.2.2
          · intro eu o l heu hwu
            cases heu with
            | head =>
              injection hwu with hp2
              injection hp2 with _ hl
              subst hl
              exact hbelowExec
            | tail _ hutl =>
              cases mapExecUnits_mem_inv hutl with
              | intro w' hw' =>
                cases hw' with
                | intro hw'1 hw'2 =>
                  cases wakeWaitersOn_mem_inv id_lock hw'1 with
                  | intro w hw =>
                    subst hw'2
                    rw [← hw.2] at hwu
                    have hsb := wakeUnitOn_stillBlocked id_lock w hwu
                    have hall := hwt.strict_wait_order (toExecUnit w) o l
                      (List.Mem.tail _ (mem_mapExecUnits hw.1)) hsb.2
                    dsimp [toExecUnit]
                    rw [← hw.2, (wakeUnitOn_preserves_fields id_lock w).2.2.1,
                      (wakeUnitOn_preserves_fields id_lock w).2.2.2.1]
                    exact hall
          · intro eu heu hy
            cases heu with
            | head =>
              cases hy with
              | inl h => nomatch h
              | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3
            | tail _ hutl =>
              cases mapExecUnits_mem_inv hutl with
              | intro w' hw' =>
                cases hw' with
                | intro hw'1 hw'2 =>
                  cases wakeWaitersOn_mem_inv id_lock hw'1 with
                  | intro w hw =>
                    subst hw'2
                    rw [← hw.2] at hy
                    dsimp [toExecUnit] at hy
                    have hyPre := wakeUnitOn_preserves_yield id_lock w hy
                    have hcl := hwt.clean_yield (toExecUnit w)
                      (List.Mem.tail _ (mem_mapExecUnits hw.1)) hyPre
                    dsimp [toExecUnit]
                    rw [← hw.2, (wakeUnitOn_preserves_fields id_lock w).2.2.1,
                      (wakeUnitOn_preserves_fields id_lock w).2.2.2.1]
                    exact hcl
        refine ⟨hwt', ?_, ?_⟩
        · intro id_c hnf2
          cases hcons.condvar_coupled id_c hnf2 with
          | intro v hv =>
            cases hv.1 with
            | head =>
              refine ⟨toExecUnit { u with held := rem, wait := .osBlocked c id_cvar lvl_cvar },
                List.Mem.head _, (by intro h; nomatch h), ?_⟩
              dsimp [toExecUnit] at hv
              dsimp [toExecUnit]
              cases mem_append_or hv.2.2 with
              | inr honce => exact mem_append_right honce
              | inl hheld =>
                exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                  (fun heq => by injection heq with _ _ hk _; nomatch hk))
            | tail _ hvtl =>
              cases mapExecUnits_mem_inv hvtl with
              | intro vw hvw =>
                rw [← hvw.2] at hv
                refine ⟨toExecUnit (wakeUnitOn id_lock vw),
                  List.Mem.tail _ (mem_mapExecUnits (mem_wakeWaitersOn id_lock hvw.1)),
                  fun hf => hv.2.1 ((wakeUnitOn_finished_iff id_lock vw).1 hf), ?_⟩
                dsimp [toExecUnit]
                rw [(wakeUnitOn_preserves_fields id_lock vw).2.2.1,
                  (wakeUnitOn_preserves_fields id_lock vw).2.2.2.1]
                exact hv.2.2
        · intro id_ch hmode
          dsimp [countCapSlotsWorld]
          rw [countCapSlotsWorld_wakeWaitersOn, ← countCapSlotsInList_removeOrdered id_ch hrem]
          exact hcons.creditChan_conserved id_ch hmode
    | blockChanCreditRecv u predOb id_ch lvl_ch rem rest sync c hstmt hwait hbuf0 hrem =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      cases typedStmt_chanCreditRecv_inv htypedU with
      | intro remT hinv =>
        have hremT := hinv.1
        have hbelow := hinv.2
        rw [hrem] at hremT
        injection hremT with hp; injection hp with _ hremEq; subst hremEq
        have hbelowExec := allBelow_rem_execUnit_of_ambient hbelow
        have hfulRest : ∃ v₀ : WorldUnit Level, v₀ ∈ rest ∧ v₀.wait ≠ .finished ∧
            ∃ k b, LinearToken.ordered id_ch lvl_ch k b ∈ (toExecUnit v₀).held := by
          cases hcons.chanCreditRecv_paired u id_ch lvl_ch (List.Mem.head rest)
              (by rw [hwait]; intro h; nomatch h)
              (removeFirstToken_sub hrem).1 hbuf0 with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvrest => exact ⟨v, hvrest, hv.2.1, .chanCreditSendOb, .taskMovable, mem_append_left hv.2.2⟩
            | head =>
              have hinRem := removeFirstToken_other_mem_rem hrem hv.2.2
                (fun heq => by injection heq with _ _ hk _; nomatch hk)
              exact False.elim (dag.irrefl lvl_ch
                (hbelowExec lvl_ch (ordered_mem_tokensLevels (mem_append_left hinRem))))
        refine ⟨releaseBlock_noWake_preserves_wt hwt hrem hbelowExec hfulRest, ?_, ?_⟩
        · intro id_c hnf
          cases hcons.condvar_coupled id_c hnf with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
            | head =>
              refine ⟨toExecUnit { u with held := rem, wait := .osBlocked c id_ch lvl_ch },
                List.Mem.head _, (by intro h; nomatch h), ?_⟩
              dsimp [toExecUnit] at hv; dsimp [toExecUnit]
              cases mem_append_or hv.2.2 with
              | inr honce => exact mem_append_right honce
              | inl hheld =>
                exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                  (fun heq => by injection heq with _ _ hk _; nomatch hk))
        · intro id_q hmode
          dsimp [countCapSlotsWorld]
          rw [← countCapSlotsInList_removeOrdered id_q hrem]
          exact hcons.creditChan_conserved id_q hmode
    | blockChanBlockingSend u predOb id_ch lvl_ch rem rest sync c hstmt hwait hrem =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      cases typedStmt_chanBlockingSend_inv htypedU with
      | intro remT hinv =>
        have hremT := hinv.1; have hbelow := hinv.2
        rw [hrem] at hremT
        injection hremT with hp; injection hp with _ hremEq; subst hremEq
        have hbelowExec := allBelow_rem_execUnit_of_ambient hbelow
        have hfulRest : ∃ v₀ : WorldUnit Level, v₀ ∈ rest ∧ v₀.wait ≠ .finished ∧
            ∃ k b, LinearToken.ordered id_ch lvl_ch k b ∈ (toExecUnit v₀).held := by
          cases hcons.chanBlockingSend_paired u id_ch lvl_ch (List.Mem.head rest)
              (by rw [hwait]; intro h; nomatch h)
              (removeFirstToken_sub hrem).1 with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvrest => exact ⟨v, hvrest, hv.2.1, .chanBlockingRecvOb, .taskMovable, mem_append_left hv.2.2⟩
            | head =>
              have hinRem := removeFirstToken_other_mem_rem hrem hv.2.2
                (fun heq => by injection heq with _ _ hk _; nomatch hk)
              exact False.elim (dag.irrefl lvl_ch
                (hbelowExec lvl_ch (ordered_mem_tokensLevels (mem_append_left hinRem))))
        refine ⟨releaseBlock_noWake_preserves_wt hwt hrem hbelowExec hfulRest, ?_, ?_⟩
        · intro id_c hnf
          cases hcons.condvar_coupled id_c hnf with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
            | head =>
              refine ⟨toExecUnit { u with held := rem, wait := .osBlocked c id_ch lvl_ch },
                List.Mem.head _, (by intro h; nomatch h), ?_⟩
              dsimp [toExecUnit] at hv; dsimp [toExecUnit]
              cases mem_append_or hv.2.2 with
              | inr honce => exact mem_append_right honce
              | inl hheld =>
                exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                  (fun heq => by injection heq with _ _ hk _; nomatch hk))
        · intro id_q hmode
          dsimp [countCapSlotsWorld]
          rw [← countCapSlotsInList_removeOrdered id_q hrem]
          exact hcons.creditChan_conserved id_q hmode
    | blockChanBlockingRecv u predOb id_ch lvl_ch rem rest sync c hstmt hwait hrem =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      cases typedStmt_chanBlockingRecv_inv htypedU with
      | intro remT hinv =>
        have hremT := hinv.1; have hbelow := hinv.2
        rw [hrem] at hremT
        injection hremT with hp; injection hp with _ hremEq; subst hremEq
        have hbelowExec := allBelow_rem_execUnit_of_ambient hbelow
        have hfulRest : ∃ v₀ : WorldUnit Level, v₀ ∈ rest ∧ v₀.wait ≠ .finished ∧
            ∃ k b, LinearToken.ordered id_ch lvl_ch k b ∈ (toExecUnit v₀).held := by
          cases hcons.chanBlockingRecv_paired u id_ch lvl_ch (List.Mem.head rest)
              (by rw [hwait]; intro h; nomatch h)
              (removeFirstToken_sub hrem).1 with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvrest => exact ⟨v, hvrest, hv.2.1, .chanBlockingSendOb, .taskMovable, mem_append_left hv.2.2⟩
            | head =>
              have hinRem := removeFirstToken_other_mem_rem hrem hv.2.2
                (fun heq => by injection heq with _ _ hk _; nomatch hk)
              exact False.elim (dag.irrefl lvl_ch
                (hbelowExec lvl_ch (ordered_mem_tokensLevels (mem_append_left hinRem))))
        refine ⟨releaseBlock_noWake_preserves_wt hwt hrem hbelowExec hfulRest, ?_, ?_⟩
        · intro id_c hnf
          cases hcons.condvar_coupled id_c hnf with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
            | head =>
              refine ⟨toExecUnit { u with held := rem, wait := .osBlocked c id_ch lvl_ch },
                List.Mem.head _, (by intro h; nomatch h), ?_⟩
              dsimp [toExecUnit] at hv; dsimp [toExecUnit]
              cases mem_append_or hv.2.2 with
              | inr honce => exact mem_append_right honce
              | inl hheld =>
                exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                  (fun heq => by injection heq with _ _ hk _; nomatch hk))
        · intro id_q hmode
          dsimp [countCapSlotsWorld]
          rw [← countCapSlotsInList_removeOrdered id_q hrem]
          exact hcons.creditChan_conserved id_q hmode
    | blockBarrierWait u pred id_bar lvl_bar rem rest sync c hstmt hwait hopen hrem =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      cases typedStmt_barrierWait_inv htypedU with
      | intro remT hinv =>
        have hremT := hinv.1; have hbelow := hinv.2
        rw [hrem] at hremT
        injection hremT with hp; injection hp with _ hremEq; subst hremEq
        have hbelowExec := allBelow_rem_execUnit_of_ambient hbelow
        have hfulRest : ∃ v₀ : WorldUnit Level, v₀ ∈ rest ∧ v₀.wait ≠ .finished ∧
            ∃ k b, LinearToken.ordered id_bar lvl_bar k b ∈ (toExecUnit v₀).held := by
          cases hcons.barrier_paired u id_bar lvl_bar (List.Mem.head rest)
              (by rw [hwait]; intro h; nomatch h)
              (removeFirstToken_sub hrem).1 hopen with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvrest => exact ⟨v, hvrest, hv.2.1, .barrierTicket, .taskMovable, mem_append_left hv.2.2.2⟩
            | head => exact False.elim (hv.2.2.1 rfl)
        refine ⟨releaseBlock_noWake_preserves_wt hwt hrem hbelowExec hfulRest, ?_, ?_⟩
        · intro id_c hnf
          cases hcons.condvar_coupled id_c hnf with
          | intro v hv =>
            cases hv.1 with
            | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
            | head =>
              refine ⟨toExecUnit { u with held := rem, wait := .osBlocked c id_bar lvl_bar },
                List.Mem.head _, (by intro h; nomatch h), ?_⟩
              dsimp [toExecUnit] at hv; dsimp [toExecUnit]
              cases mem_append_or hv.2.2 with
              | inr honce => exact mem_append_right honce
              | inl hheld =>
                exact mem_append_left (removeFirstToken_other_mem_rem hrem hheld
                  (fun heq => by injection heq with _ _ hk _; nomatch hk))
        · intro id_q hmode
          dsimp [countCapSlotsWorld]
          rw [← countCapSlotsInList_removeOrdered id_q hrem]
          exact hcons.creditChan_conserved id_q hmode
    | blockJoinWait u id_child lvl_join holder rest sync c hstmt hwait hch =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      have hbelow := typedStmt_joinWait_inv htypedU
      have hful : ∃ v, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
          ∃ k b, LinearToken.ordered id_child lvl_join k b ∈ (toExecUnit v).held := by
        cases hcons.child_conserved id_child holder lvl_join hch with
        | intro v hv =>
          exact ⟨v, hv.1, hv.2.1, .joinExitOb, .taskMovable, mem_append_left hv.2.2⟩
      refine ⟨retainBlock_preserves_wt dag hwt (by intro h; nomatch h) rfl
        (fun hy => by cases hy with | inl h => nomatch h | inr h => cases h with | intro _ h2 => cases h2 with | intro _ h3 => nomatch h3)
        (allBelow_execUnit_of_ambient hbelow) hful,
        ?_, hcons.creditChan_conserved⟩
      intro id_c hnf
      cases hcons.condvar_coupled id_c hnf with
      | intro v hv =>
        cases hv.1 with
        | head => exact ⟨toExecUnit { u with wait := .osBlocked c id_child lvl_join }, List.Mem.head _, (by intro h; nomatch h), hv.2.2⟩
        | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
    | blockAsyncMutexLockAwait u id lvl holder rest sync c hstmt hwait ham =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      have hinv := typedStmt_asyncMutexLockAwait_inv htypedU
      have hnoOs := hinv.1; have hnoAmb := hinv.2.1; have hbelow := hinv.2.2
      have hframesNil : u.onceFrames = [] := onceFrames_nil_of_noOsBoundAmbient hnoAmb
      have hnoExec : HasNoOsBound (toExecUnit u).held := by
        dsimp [toExecUnit]; rw [hframesNil]; dsimp [onceHeldTokens]; rw [List.append_nil]; exact hnoOs
      have hful : ∃ v, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
          ∃ k b, LinearToken.ordered id lvl k b ∈ (toExecUnit v).held := by
        cases hcons.asyncMutex_conserved id holder lvl ham with
        | intro v hv =>
          exact ⟨v, hv.1, hv.2.1, .asyncMutexGuard, .taskMovable, mem_append_left hv.2.2⟩
      refine ⟨retainBlock_preserves_wt dag hwt (by intro h; nomatch h) rfl
        (fun _ => hnoExec)
        (allBelow_execUnit_of_ambient hbelow) hful,
        ?_, hcons.creditChan_conserved⟩
      intro id_c hnf
      cases hcons.condvar_coupled id_c hnf with
      | intro v hv =>
        cases hv.1 with
        | head => exact ⟨toExecUnit { u with wait := .coopBlocked id lvl }, List.Mem.head _, (by intro h; nomatch h), hv.2.2⟩
        | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
    | blockAsyncAwaitPoint u id_fut lvl_fut holder rest sync c hstmt hwait hfut =>
      have htypedU := (hcons.units_typed u (List.Mem.head rest)).2 (by rw [hwait]; intro h; nomatch h)
      rw [hstmt] at htypedU
      have hinv := typedStmt_asyncAwaitPoint_inv htypedU
      have hnoOs := hinv.1; have hnoAmb := hinv.2.1; have hbelow := hinv.2.2
      have hframesNil : u.onceFrames = [] := onceFrames_nil_of_noOsBoundAmbient hnoAmb
      have hnoExec : HasNoOsBound (toExecUnit u).held := by
        dsimp [toExecUnit]; rw [hframesNil]; dsimp [onceHeldTokens]; rw [List.append_nil]; exact hnoOs
      have hful : ∃ v, v ∈ u :: rest ∧ v.wait ≠ .finished ∧
          ∃ k b, LinearToken.ordered id_fut lvl_fut k b ∈ (toExecUnit v).held := by
        cases hcons.future_conserved id_fut holder lvl_fut hfut with
        | intro v hv =>
          cases hv.2.2 with | intro k hr1 => cases hr1 with | intro b htok =>
            exact ⟨v, hv.1, hv.2.1, k, b, mem_append_left htok⟩
      refine ⟨retainBlock_preserves_wt dag hwt (by intro h; nomatch h) rfl
        (fun _ => hnoExec)
        (allBelow_execUnit_of_ambient hbelow) hful,
        ?_, hcons.creditChan_conserved⟩
      intro id_c hnf
      cases hcons.condvar_coupled id_c hnf with
      | intro v hv =>
        cases hv.1 with
        | head => exact ⟨toExecUnit { u with wait := .coopBlocked id_fut lvl_fut }, List.Mem.head _, (by intro h; nomatch h), hv.2.2⟩
        | tail _ hvtl => exact ⟨v, List.Mem.tail _ hvtl, hv.2⟩
  exact ⟨hmain.1, wellTypedWorld_no_closedBlockedSet dag hmain.1, hmain.2.1, hmain.2.2⟩

/-! ### Level Instances & All 8 Deadlock Topologies -/

structure LexLevel where
  tier : Nat
  addr : Nat

def lexPrec (a b : LexLevel) : Prop :=
  a.tier < b.tier ∨ (a.tier = b.tier ∧ a.addr < b.addr)

theorem lexPrec_strictDAG : StrictDAG LexLevel lexPrec := by
  refine ⟨?_, ?_⟩
  · intro l hl
    cases hl with
    | inl hlt => exact Nat.lt_irrefl l.tier hlt
    | inr heq => exact Nat.lt_irrefl l.addr heq.2
  · intro a b c hab hbc
    unfold lexPrec at hab hbc
    unfold lexPrec
    cases hab with
    | inl ht1 =>
      cases hbc with
      | inl ht2 => exact Or.inl (Nat.lt_trans ht1 ht2)
      | inr heq2 => rw [← heq2.1]; exact Or.inl ht1
    | inr heq1 =>
      cases hbc with
      | inl ht2 => rw [heq1.1]; exact Or.inl ht2
      | inr heq2 =>
        exact Or.inr ⟨Eq.trans heq1.1 heq2.1, Nat.lt_trans heq1.2 heq2.2⟩

abbrev natPrec (a b : Nat) : Prop := a < b

theorem natPrec_strictDAG : StrictDAG Nat natPrec :=
  ⟨Nat.lt_irrefl, fun h1 h2 => Nat.lt_trans h1 h2⟩

def truePred {Level : Type} (_ : LinearToken Level) : Bool := true

def objEqPred {Level : Type} (target : ObjId) : LinearToken Level → Bool
  | .ordered obj _ _ _ => Nat.beq obj target
  | .chanCapSlot id_ch => Nat.beq id_ch target

def capSlotPred {Level : Type} (target : ObjId) : LinearToken Level → Bool
  | .chanCapSlot id_ch => Nat.beq id_ch target
  | .ordered _ _ _ _ => false

-- Topology 1a: Two-lock DAG statement + guard-leak witness
def dagTwoLockStmt : Stmt Nat :=
  .seq (.mutexLock 0 0)
    (.seq (.mutexLock 2 2)
      (.seq (.unlock truePred) (.unlock truePred)))

theorem topology1a_dag_positive : ValidThreadStmt natPrec dagTwoLockStmt [] := by
  have s1 : TypedStmt natPrec [] (.mutexLock 0 0) []
      [.ordered 0 0 .mutexGuard .osBound] :=
    .mutexLock 0 0 (fun _ h => nomatch h)
  have s2 : TypedStmt natPrec [] (.mutexLock 2 2)
      [.ordered 0 0 .mutexGuard .osBound]
      [.ordered 2 2 .mutexGuard .osBound, .ordered 0 0 .mutexGuard .osBound] := by
    refine .mutexLock 2 2 ?_
    intro l hl
    cases hl with
    | head => decide
    | tail _ h => nomatch h
  have s3 : TypedStmt natPrec [] (.unlock truePred)
      [.ordered 2 2 .mutexGuard .osBound, .ordered 0 0 .mutexGuard .osBound]
      [.ordered 0 0 .mutexGuard .osBound] :=
    .unlockToken truePred 2 2 .mutexGuard .osBound rfl (Or.inl rfl)
  have s4 : TypedStmt natPrec [] (.unlock truePred)
      [.ordered 0 0 .mutexGuard .osBound] [] :=
    .unlockToken truePred 0 0 .mutexGuard .osBound rfl (Or.inl rfl)
  exact .seq s1 (.seq s2 (.seq s3 s4))

theorem topology1a_forget_deadlock_witness :
    let leakedWorld : List (ExecUnit Nat) := [
      { uid := 0, held := [.ordered 0 0 .mutexGuard .osBound], wait := .finished },
      { uid := 1, held := [], wait := .osBlocked 1 0 0 }
    ]
    ¬ WellTypedWorld natPrec leakedWorld ∧
    (∀ u : ExecUnit Nat, u ∈ leakedWorld → u.wait ≠ .finished → unitIsBlocked u) ∧
    (∀ v : ExecUnit Nat, v ∈ leakedWorld → ¬ unitHoldsFor v 0 0) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro hwt
    have hemp := hwt.finished_empty _ (List.Mem.head _) rfl
    nomatch hemp
  · intro u hu hnf
    cases hu with
    | head => exact False.elim (hnf rfl)
    | tail _ hu2 =>
      cases hu2 with
      | head => exact ⟨0, 0, rfl⟩
      | tail _ hnil => nomatch hnil
  · intro v hv hholds
    cases hv with
    | head => exact hholds.1 rfl
    | tail _ hv2 =>
      cases hv2 with
      | head =>
        cases hholds.2 with
        | intro _ hr => cases hr with | intro _ ht => nomatch ht
      | tail _ hnil => nomatch hnil

-- Topology 1b: Runtime address-sorted multi-shard lock
theorem topology1b_addr_sorted_lock_positive (t a b : Nat) (hne : a ≠ b) :
    (a < b →
      TypedStmt lexPrec []
        (.seq (.mutexLock a ⟨t, a⟩) (.mutexLock b ⟨t, b⟩))
        []
        [.ordered b ⟨t, b⟩ .mutexGuard .osBound,
         .ordered a ⟨t, a⟩ .mutexGuard .osBound]) ∧
    (¬ (a < b) →
      TypedStmt lexPrec []
        (.seq (.mutexLock b ⟨t, b⟩) (.mutexLock a ⟨t, a⟩))
        []
        [.ordered a ⟨t, a⟩ .mutexGuard .osBound,
         .ordered b ⟨t, b⟩ .mutexGuard .osBound]) := by
  refine ⟨?_, ?_⟩
  · intro hab
    have op1 : TypedStmt lexPrec [] (.mutexLock a (LexLevel.mk t a)) []
        [.ordered a (LexLevel.mk t a) .mutexGuard .osBound] :=
      .mutexLock a (LexLevel.mk t a) (fun _ h => nomatch h)
    have op2 : TypedStmt lexPrec [] (.mutexLock b (LexLevel.mk t b))
        [.ordered a (LexLevel.mk t a) .mutexGuard .osBound]
        [.ordered b (LexLevel.mk t b) .mutexGuard .osBound,
         .ordered a (LexLevel.mk t a) .mutexGuard .osBound] := by
      refine .mutexLock b (LexLevel.mk t b) ?_
      intro l hl
      cases hl with
      | head => exact Or.inr ⟨rfl, hab⟩
      | tail _ h => nomatch h
    exact .seq op1 op2
  · intro hnab
    have hba : b < a := by
      cases Nat.lt_or_ge a b with
      | inl hlt => exact False.elim (hnab hlt)
      | inr hge =>
        cases Nat.lt_or_eq_of_le hge with
        | inl hlt => exact hlt
        | inr heq => exact False.elim (hne (Eq.symm heq))
    have op1 : TypedStmt lexPrec [] (.mutexLock b (LexLevel.mk t b)) []
        [.ordered b (LexLevel.mk t b) .mutexGuard .osBound] :=
      .mutexLock b (LexLevel.mk t b) (fun _ h => nomatch h)
    have op2 : TypedStmt lexPrec [] (.mutexLock a (LexLevel.mk t a))
        [.ordered b (LexLevel.mk t b) .mutexGuard .osBound]
        [.ordered a (LexLevel.mk t a) .mutexGuard .osBound,
         .ordered b (LexLevel.mk t b) .mutexGuard .osBound] := by
      refine .mutexLock a (LexLevel.mk t a) ?_
      intro l hl
      cases hl with
      | head => exact Or.inr ⟨rfl, hba⟩
      | tail _ h => nomatch h
    exact .seq op1 op2

theorem topology1b_same_addr_rejected (t a : Nat) :
    ∀ out, ¬ TypedStmt lexPrec [] (.mutexLock a ⟨t, a⟩)
      [.ordered a ⟨t, a⟩ .mutexGuard .osBound] out := by
  intro out ht
  cases ht with
  | mutexLock _ _ hall =>
    exact lexPrec_strictDAG.irrefl ⟨t, a⟩ (hall _ (List.Mem.head []))

-- Topology 2: Writer-preferring `RwLock` vs `read_recursive` vs `upgrade`
theorem topology2_rwlock_writerPref_rejects_recursive_read (id lvl : Nat) :
    ∀ out, ¬ TypedStmt natPrec [] (.rwReadWriterPref id lvl)
      [.ordered id lvl .rwReadGuard .osBound] out := by
  intro out ht
  cases ht with
  | rwReadWriterPref _ _ hall =>
    exact Nat.lt_irrefl lvl (hall _ (List.Mem.head []))

theorem topology2_rwlock_readRecursive_admits_even_with_higher_lock :
    TypedStmt natPrec []
      (.seq (.rwReadWriterPref 0 10)
        (.seq (.mutexLock 1 20) (.rwReadRecursive 0 10)))
      []
      [.ordered 0 10 .rwReadGuard .osBound,
       .ordered 1 20 .mutexGuard .osBound,
       .ordered 0 10 .rwReadGuard .osBound] := by
  have s1 : TypedStmt natPrec [] (.rwReadWriterPref 0 10) []
      [.ordered 0 10 .rwReadGuard .osBound] :=
    .rwReadWriterPref 0 10 (fun _ h => nomatch h)
  have s2 : TypedStmt natPrec [] (.mutexLock 1 20)
      [.ordered 0 10 .rwReadGuard .osBound]
      [.ordered 1 20 .mutexGuard .osBound, .ordered 0 10 .rwReadGuard .osBound] := by
    refine .mutexLock 1 20 ?_
    intro l hl
    cases hl with
    | head => decide
    | tail _ h => nomatch h
  have s3 : TypedStmt natPrec [] (.rwReadRecursive 0 10)
      [.ordered 1 20 .mutexGuard .osBound, .ordered 0 10 .rwReadGuard .osBound]
      [.ordered 0 10 .rwReadGuard .osBound,
       .ordered 1 20 .mutexGuard .osBound,
       .ordered 0 10 .rwReadGuard .osBound] :=
    .rwReadRecursive 0 10 (Or.inl (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))
  exact .seq s1 (.seq s2 s3)

theorem topology2_rwlock_upgradable_clean_upgrade_positive :
    TypedStmt natPrec []
      (.seq (.rwUpgradableRead 0 10) (.rwUpgrade truePred 0 10))
      [] [.ordered 0 10 .rwWriteGuard .osBound] :=
  .seq (.rwUpgradableRead 0 10 (fun _ h => nomatch h))
       (.rwUpgrade truePred 0 10 rfl (fun _ h => nomatch h))

theorem topology2_rwlock_upgrade_while_holding_higher_lock_rejected :
    let heldAfterHigh : List (LinearToken Nat) :=
      [.ordered 1 20 .mutexGuard .osBound,
       .ordered 0 10 .rwUpgradableGuard .osBound]
    ∀ out, ¬ TypedStmt natPrec [] (.rwUpgrade (objEqPred 0) 0 10) heldAfterHigh out := by
  intro heldAfterHigh out ht
  cases ht with
  | rwUpgrade _ _ _ hrem hall =>
    dsimp [heldAfterHigh, removeFirstToken, objEqPred] at hrem
    injection hrem with hpair
    injection hpair with _ hremEq
    subst hremEq
    have hlt : 20 < 10 := hall 20 (List.Mem.head [])
    nomatch hlt

-- Topology 3: Lock-guarded `Condvar` (`condvarNotify` requires holding `Mutex(id_lock)`!)
def condvarWaiterLoopStmt : Stmt Nat :=
  .seq (.mutexLock 2 10)
    (.seq (.condvarWait truePred 2 10 99 5 (.coupledMutexPredLoop 2))
      (.unlock truePred))

def condvarNotifierStmt : Stmt Nat :=
  .seq (.mutexLock 2 10)
    (.seq (.condvarNotify (objEqPred 99) 2 99 5)
      (.unlock truePred))

theorem topology3_condvar_standard_idiom_positive :
    ValidThreadStmt natPrec condvarWaiterLoopStmt [] ∧
    ValidThreadStmt natPrec condvarNotifierStmt
      [.ordered 99 5 .condvarSignalOb .taskMovable] := by
  refine ⟨?_, ?_⟩
  · have w1 : TypedStmt natPrec [] (.mutexLock 2 10) []
        [.ordered 2 10 .mutexGuard .osBound] :=
      .mutexLock 2 10 (fun _ h => nomatch h)
    have w2 : TypedStmt natPrec []
        (.condvarWait truePred 2 10 99 5 (.coupledMutexPredLoop 2))
        [.ordered 2 10 .mutexGuard .osBound]
        [.ordered 2 10 .mutexGuard .osBound] :=
      .condvarWaitWhileNotNotified truePred 2 10 99 5 (by decide) rfl
        (fun _ h => nomatch h) (fun _ h => nomatch h)
    have w3 : TypedStmt natPrec [] (.unlock truePred)
        [.ordered 2 10 .mutexGuard .osBound] [] :=
      .unlockToken truePred 2 10 .mutexGuard .osBound rfl (Or.inl rfl)
    exact .seq w1 (.seq w2 w3)
  · have n1 : TypedStmt natPrec [] (.mutexLock 2 10)
        [.ordered 99 5 .condvarSignalOb .taskMovable]
        [.ordered 2 10 .mutexGuard .osBound,
         .ordered 99 5 .condvarSignalOb .taskMovable] := by
      refine .mutexLock 2 10 ?_
      intro l hl
      cases hl with
      | head => decide
      | tail _ h => nomatch h
    have n2 : TypedStmt natPrec [] (.condvarNotify (objEqPred 99) 2 99 5)
        [.ordered 2 10 .mutexGuard .osBound,
         .ordered 99 5 .condvarSignalOb .taskMovable]
        [.ordered 2 10 .mutexGuard .osBound] :=
      .condvarNotify (objEqPred 99) 2 99 5 (Or.inl ⟨rfl, rfl⟩) rfl
    have n3 : TypedStmt natPrec [] (.unlock truePred)
        [.ordered 2 10 .mutexGuard .osBound] [] :=
      .unlockToken truePred 2 10 .mutexGuard .osBound rfl (Or.inl rfl)
    exact .seq n1 (.seq n2 n3)

/-- lock-guarded `condvarNotify` rejection: calling `condvarNotify`
without holding the coupled `Mutex(2)` is rejected! -/
theorem topology3_unheld_lock_condvar_notify_rejected :
    ∀ out, ¬ TypedStmt natPrec []
      (.condvarNotify (objEqPred 99) 2 99 5)
      [.ordered 99 5 .condvarSignalOb .taskMovable] out := by
  intro out ht
  cases ht with
  | condvarNotify _ _ _ _ hlock _ =>
    cases hlock with
    | inl h1 => nomatch h1.2
    | inr h2 => exact False.elim h2

theorem topology3_unguarded_condvar_lost_wakeup_rejected :
    (∀ amb pred idL lvlL idC lvlC held out,
      ¬ TypedStmt natPrec amb
          (.condvarWait pred idL lvlL idC lvlC .unguardedUnconditional)
          held out) ∧
    (let worldAfterNotifierDone : List (ExecUnit Nat) := [
       { uid := 0, held := [.ordered 2 10 .mutexGuard .osBound], wait := .running 0 },
       { uid := 1, held := [], wait := .finished }
     ]
     let lostWakeupWorld : List (ExecUnit Nat) := [
       { uid := 0, held := [], wait := .osBlocked 0 99 5 },
       { uid := 1, held := [], wait := .finished }
     ]
     WellTypedWorld natPrec worldAfterNotifierDone ∧
     CondvarCoupledInv worldAfterNotifierDone 99 5 true ∧
     ¬ WellTypedWorld natPrec lostWakeupWorld) := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ ht
    nomatch ht
  · dsimp
    refine ⟨?_, condvarNotify_preserves_coupledInv _ 99 5, ?_⟩
    · refine {
        finished_empty := ?_
        live_fulfiller := ?_
        strict_wait_order := ?_
        clean_yield := ?_
      }
      · intro u hu hfin
        cases hu with
        | head => nomatch hfin
        | tail _ hu2 =>
          cases hu2 with
          | head => rfl
          | tail _ hnil => nomatch hnil
      · intro u _ _ hu hwu
        cases hu with
        | head => nomatch hwu
        | tail _ hu2 =>
          cases hu2 with
          | head => nomatch hwu
          | tail _ hnil => nomatch hnil
      · intro u _ _ hu hwu
        cases hu with
        | head => nomatch hwu
        | tail _ hu2 =>
          cases hu2 with
          | head => nomatch hwu
          | tail _ hnil => nomatch hnil
      · intro u hu hy
        cases hu with
        | head =>
          cases hy with
          | inl hrq => nomatch hrq
          | inr hcb => cases hcb with | intro _ h2 => cases h2 with | intro _ h => nomatch h
        | tail _ hu2 =>
          cases hu2 with
          | head =>
            cases hy with
            | inl hrq => nomatch hrq
            | inr hcb => cases hcb with | intro _ h2 => cases h2 with | intro _ h => nomatch h
          | tail _ hnil => nomatch hnil
    · intro hwt
      cases hwt.live_fulfiller _ 99 5 (List.Mem.head _) rfl with
      | intro v hv =>
        cases hv.1 with
        | head =>
          cases hv.2.2 with | intro _ h2 => cases h2 with | intro _ ht => nomatch ht
        | tail _ hv2 =>
          cases hv2 with
          | head => exact hv.2.1 rfl
          | tail _ hnil => nomatch hnil

theorem topology3_condvar_outer_lock_deadlock_impossible {Level : Type}
    {prec : Level → Level → Prop} (dag : StrictDAG Level prec)
    (lvl_L1 lvl_cvar : Level) :
    ¬ (AllBelow prec (tokensLevels [.ordered 1 lvl_L1 .mutexGuard .osBound]) lvl_cvar ∧
       AllBelow prec (tokensLevels [.ordered 99 lvl_cvar .condvarSignalOb .taskMovable]) lvl_L1) := by
  intro hboth
  exact strictDAG_asymm dag
    (hboth.1 lvl_L1 (List.Mem.head []))
    (hboth.2 lvl_cvar (List.Mem.head []))

-- Topology 4: `Once` / `OnceLock`
def onceNestedStmt : Stmt Nat :=
  .onceCall 1 10 (.onceCall 2 20 (.seq (.mutexLock 3 30) (.unlock truePred)))

theorem topology4_once_hierarchical_positive :
    ValidThreadStmt natPrec onceNestedStmt [] := by
  have mLock : TypedStmt natPrec [(20, .osBound), (10, .osBound)]
      (.mutexLock 3 30) [] [.ordered 3 30 .mutexGuard .osBound] := by
    refine .mutexLock 3 30 ?_
    intro l hl
    cases hl with
    | head => decide
    | tail _ hl2 =>
      cases hl2 with
      | head => decide
      | tail _ hnil => nomatch hnil
  have mUnlock : TypedStmt natPrec [(20, .osBound), (10, .osBound)]
      (.unlock truePred) [.ordered 3 30 .mutexGuard .osBound] [] :=
    .unlockToken truePred 3 30 .mutexGuard .osBound rfl (Or.inl rfl)
  have innerOnce : TypedStmt natPrec [(10, .osBound)]
      (.onceCall 2 20 (.seq (.mutexLock 3 30) (.unlock truePred))) [] [] := by
    refine .onceCall 2 20 _ ?_ (.seq mLock mUnlock)
    intro l hl
    cases hl with
    | head => decide
    | tail _ hnil => nomatch hnil
  exact .onceCall 1 10 _ (fun _ h => nomatch h) innerOnce

theorem topology4_once_reentrant_rejected (id lvl : Nat) (body : Stmt Nat) :
    ∀ out, ¬ TypedStmt natPrec [] (.onceCall id lvl (.onceCall id lvl body)) [] out := by
  intro out ht
  cases ht with
  | onceCall _ _ _ _ hinner =>
    cases hinner with
    | onceCall _ _ _ hall _ =>
      exact Nat.lt_irrefl lvl (hall lvl (List.Mem.head []))

/-- carrier-tagged `ambient` rejection: `.await` (and `rayon::join`)
inside `Once::call_once` is REJECTED because `onceCall` pushes
`(lvl_once, .osBound)` into `ambient`, falsifying `HasNoOsBoundAmbient`! -/
theorem topology4_once_containing_await_rejected :
    ¬ ∃ h', TypedStmt natPrec [] (.onceCall 1 10 (.asyncAwaitPoint 88 20)) [] h' := by
  intro hex
  cases hex with
  | intro h' ht =>
    cases ht with
    | onceCall _ _ _ _ hbody =>
      cases hbody with
      | asyncAwaitPoint _ _ _ hnoAmb _ =>
        nomatch hnoAmb.1

theorem topology4_once_containing_rayon_rejected :
    ¬ ∃ h', TypedStmt natPrec [] (.onceCall 1 10 (.rayonJoin [] [] .skip .skip)) [] h' := by
  intro hex
  cases hex with
  | intro h' ht =>
    cases ht with
    | onceCall _ _ _ _ hbody =>
      cases hbody with
      | rayonJoin _ _ _ _ hnoAmb _ _ =>
        nomatch hnoAmb.1

-- Topology 5a: `Barrier::wait` party tickets
theorem topology5a_barrier_party_positive :
    ValidThreadStmt natPrec (.barrierWait truePred 50 15)
      [.ordered 50 15 .barrierTicket .taskMovable] :=
  .barrierWait truePred 50 15 rfl (fun _ h => nomatch h)

theorem topology5a_barrier_double_ticket_same_thread_rejected :
    let twoTickets : List (LinearToken Nat) :=
      [.ordered 50 15 .barrierTicket .taskMovable,
       .ordered 50 15 .barrierTicket .taskMovable]
    ∀ out, ¬ TypedStmt natPrec [] (.barrierWait truePred 50 15) twoTickets out := by
  intro twoTickets out ht
  cases ht with
  | barrierWait _ _ _ hrem hall =>
    dsimp [twoTickets, removeFirstToken, truePred] at hrem
    injection hrem with hpair
    injection hpair with _ hremEq
    subst hremEq
    exact Nat.lt_irrefl 15 (hall 15 (List.Mem.head []))

-- Topology 5b` Slot Conservation):
def creditSendUnderHigherLockStmt : Stmt Nat :=
  .seq (.mutexLock 1 20)
    (.seq (.chanCreditSend (objEqPred 60) (capSlotPred 60) 60 10)
      (.unlock truePred))

def pairedCreditRecvReplenishStmt : Stmt Nat :=
  .seq (.mutexLock 1 20)
    (.seq (.unlock truePred)
      (.seq (.chanCreditRecv truePred 60 10)
        (.dropCapSlot (capSlotPred 60) 60)))

theorem topology5_bounded_chan_credit_send_under_higher_lock_positive :
    ValidThreadStmt natPrec creditSendUnderHigherLockStmt
      [.ordered 60 10 .chanCreditSendOb .taskMovable, .chanCapSlot 60] ∧
    ValidThreadStmt natPrec pairedCreditRecvReplenishStmt
      [.ordered 60 10 .chanCreditRecvOb .taskMovable] := by
  refine ⟨?_, ?_⟩
  · have s1 : TypedStmt natPrec [] (.mutexLock 1 20)
        [.ordered 60 10 .chanCreditSendOb .taskMovable, .chanCapSlot 60]
        [.ordered 1 20 .mutexGuard .osBound,
         .ordered 60 10 .chanCreditSendOb .taskMovable,
         .chanCapSlot 60] := by
      refine .mutexLock 1 20 ?_
      intro l hl
      cases hl with
      | head => decide
      | tail _ hnil => nomatch hnil
    have s2 : TypedStmt natPrec []
        (.chanCreditSend (objEqPred 60) (capSlotPred 60) 60 10)
        [.ordered 1 20 .mutexGuard .osBound,
         .ordered 60 10 .chanCreditSendOb .taskMovable,
         .chanCapSlot 60]
        [.ordered 1 20 .mutexGuard .osBound] :=
      .chanCreditSend (objEqPred 60) (capSlotPred 60) 60 10 rfl rfl
    have s3 : TypedStmt natPrec [] (.unlock truePred)
        [.ordered 1 20 .mutexGuard .osBound] [] :=
      .unlockToken truePred 1 20 .mutexGuard .osBound rfl (Or.inl rfl)
    exact .seq s1 (.seq s2 s3)
  · have r1 : TypedStmt natPrec [] (.mutexLock 1 20)
        [.ordered 60 10 .chanCreditRecvOb .taskMovable]
        [.ordered 1 20 .mutexGuard .osBound,
         .ordered 60 10 .chanCreditRecvOb .taskMovable] := by
      refine .mutexLock 1 20 ?_
      intro l hl
      cases hl with
      | head => decide
      | tail _ hnil => nomatch hnil
    have r2 : TypedStmt natPrec [] (.unlock truePred)
        [.ordered 1 20 .mutexGuard .osBound,
         .ordered 60 10 .chanCreditRecvOb .taskMovable]
        [.ordered 60 10 .chanCreditRecvOb .taskMovable] :=
      .unlockToken truePred 1 20 .mutexGuard .osBound rfl (Or.inl rfl)
    have r3 : TypedStmt natPrec [] (.chanCreditRecv truePred 60 10)
        [.ordered 60 10 .chanCreditRecvOb .taskMovable]
        [.chanCapSlot 60] :=
      .chanCreditRecv truePred 60 10 rfl (fun _ h => nomatch h)
    have r4 : TypedStmt natPrec [] (.dropCapSlot (capSlotPred 60) 60)
        [.chanCapSlot 60] [] :=
      .dropCapSlot (capSlotPred 60) 60 rfl
    exact .seq r1 (.seq r2 (.seq r3 r4))

/-- mode-disjoint channel protection
(`topology5_mixed_mode_send_cannot_steal_credit_slot`):
1. An uncredited `chanBlockingSend` CANNOT consume a `.creditManaged` channel's
   `.chanCreditSendOb` token (even with empty held locks where `AllBelow` would
   trivially hold!), preventing slot theft from `.chanCapSlot` holders!
2. A `.levelOrdered` channel's `.chanBlockingRecvOb` token CANNOT invoke
   `chanCreditRecv` to forge a `.chanCapSlot`! -/
theorem topology5_mixed_mode_send_cannot_steal_credit_slot :
    (∀ predOb out,
      ¬ TypedStmt natPrec []
          (.chanBlockingSend predOb 60 10)
          [.ordered 60 10 .chanCreditSendOb .taskMovable] out) ∧
    (∀ predOb out,
      ¬ TypedStmt natPrec []
          (.chanCreditRecv predOb 60 10)
          [.ordered 60 10 .chanBlockingRecvOb .taskMovable] out) := by
  refine ⟨?_, ?_⟩
  · intro predOb out ht
    cases ht with
    | chanBlockingSend _ _ _ hrem _ =>
      have hin := (removeFirstToken_sub hrem).1
      cases hin with
      | tail _ hnil => nomatch hnil
  · intro predOb out ht
    cases ht with
    | chanCreditRecv _ _ _ hrem _ =>
      have hin := (removeFirstToken_sub hrem).1
      cases hin with
      | tail _ hnil => nomatch hnil

theorem topology5_bounded_chan_overflow_while_holding_higher_lock_rejected :
    let t2HeldNoSlot : List (LinearToken Nat) :=
      [.ordered 1 20 .mutexGuard .osBound,
       .ordered 60 10 .chanCreditSendOb .taskMovable]
    let t2HeldBlocking : List (LinearToken Nat) :=
      [.ordered 1 20 .mutexGuard .osBound,
       .ordered 60 10 .chanBlockingSendOb .taskMovable]
    (∀ predOb predCap out,
      ¬ TypedStmt natPrec []
          (.chanCreditSend predOb predCap 60 10) t2HeldNoSlot out) ∧
    (∀ predOb out,
      ¬ TypedStmt natPrec []
          (.chanBlockingSend predOb 60 10) t2HeldNoSlot out) ∧
    (∀ out,
      ¬ TypedStmt natPrec []
          (.chanBlockingSend (objEqPred 60) 60 10) t2HeldBlocking out) := by
  intro t2HeldNoSlot t2HeldBlocking
  refine ⟨?_, ?_, ?_⟩
  · intro predOb predCap out ht
    cases ht with
    | @chanCreditSend _ _ mid rem _ _ _ _ hob hcap =>
      have hsub1 := removeFirstToken_sub hob
      have hsub2 := removeFirstToken_sub hcap
      have hin : LinearToken.chanCapSlot 60 ∈ t2HeldNoSlot :=
        hsub1.2 _ hsub2.1
      dsimp [t2HeldNoSlot] at hin
      cases hin with
      | tail _ hin2 =>
        cases hin2 with
        | tail _ hnil => nomatch hnil
  · intro predOb out ht
    cases ht with
    | chanBlockingSend _ _ _ hrem _ =>
      have hin := (removeFirstToken_sub hrem).1
      dsimp [t2HeldNoSlot] at hin
      cases hin with
      | tail _ hin2 =>
        cases hin2 with
        | tail _ hnil => nomatch hnil
  · intro out ht
    cases ht with
    | chanBlockingSend _ _ _ hrem hall =>
      dsimp [t2HeldBlocking, removeFirstToken, objEqPred] at hrem
      injection hrem with hpair
      injection hpair with _ hremEq
      subst hremEq
      have hlt : 20 < 10 := hall 20 (List.Mem.head [])
      nomatch hlt

theorem topology5b_join_holding_lock_needed_by_child_impossible {Level : Type}
    {prec : Level → Level → Prop} (dag : StrictDAG Level prec)
    (lvl_child lvl_lock : Level) :
    ¬ (AllBelow prec (tokensLevels [.ordered 70 lvl_child .joinExitOb .taskMovable]) lvl_lock ∧
       AllBelow prec (tokensLevels [.ordered 1 lvl_lock .mutexGuard .osBound]) lvl_child) := by
  intro hboth
  exact strictDAG_asymm dag
    (hboth.1 lvl_child (List.Mem.head []))
    (hboth.2 lvl_lock (List.Mem.head []))

-- Topology 6
def rayonPureNestedStmt : Stmt Nat :=
  .rayonJoin [] []
    (.seq (.asyncMutexLockAwait 1 5) (.unlock truePred))
    (.seq (.asyncMutexLockAwait 2 5) (.unlock truePred))

theorem topology6_rayon_pure_nested_positive :
    ValidThreadStmt natPrec rayonPureNestedStmt [] := by
  have fStmt : TypedStmt natPrec []
      (.seq (.asyncMutexLockAwait 1 5) (.unlock truePred)) [] [] :=
    .seq (.asyncMutexLockAwait 1 5 True.intro True.intro (fun _ h => nomatch h))
         (.unlockToken truePred 1 5 .asyncMutexGuard .taskMovable rfl
           (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have gStmt : TypedStmt natPrec []
      (.seq (.asyncMutexLockAwait 2 5) (.unlock truePred)) [] [] :=
    .seq (.asyncMutexLockAwait 2 5 True.intro True.intro (fun _ h => nomatch h))
         (.unlockToken truePred 2 5 .asyncMutexGuard .taskMovable rfl
           (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  exact .rayonJoin (held_f := []) (held_g := []) (held_f' := []) (held_g' := [])
    True.intro True.intro True.intro True.intro True.intro fStmt gStmt

/-- Asymmetric returned-guard Rayon deadlock rejection
(`topology6_rayon_asymmetric_returned_guard_deadlock_rejected`):
rejects BOTH the `.asyncMutexLockAwait` (`.taskMovable`) version AND the
`.mutexLock` (`.osBound`) version of `badRayonStmt`, where `f` locks+unlocks
`1@20` and `g` locks `1@20` and returns the guard! Because `f` is checked under
`tokensAmbient held_g ++ tokensAmbient held_g' ++ ambient`, `f` sees `20` from
`held_g'` and fails `20 < 20`! -/
def badRayonReturnedAsyncGuardStmt : Stmt Nat :=
  .rayonJoin [] []
    (.seq (.asyncMutexLockAwait 1 20) (.unlock truePred))
    (.asyncMutexLockAwait 1 20)

def badRayonReturnedOsGuardStmt : Stmt Nat :=
  .rayonJoin [] []
    (.seq (.mutexLock 1 20) (.unlock truePred))
    (.mutexLock 1 20)

theorem topology6_rayon_asymmetric_returned_guard_deadlock_rejected :
    (∀ out, ¬ TypedStmt natPrec [] badRayonReturnedAsyncGuardStmt [] out) ∧
    (∀ out, ¬ TypedStmt natPrec [] badRayonReturnedOsGuardStmt [] out) := by
  refine ⟨?_, ?_⟩
  · intro out ht
    cases ht with
    | rayonJoin _ _ _ _ _ hf hg =>
      cases hg with
      | asyncMutexLockAwait _ _ _ _ _ =>
        cases hf with
        | seq hf1 _ =>
          cases hf1 with
          | asyncMutexLockAwait _ _ _ _ hall =>
            exact Nat.lt_irrefl 20 (hall 20 (List.Mem.head []))
  · intro out ht
    cases ht with
    | rayonJoin _ _ _ hnoG' _ _ hg =>
      cases hg with
      | mutexLock _ _ _ =>
        nomatch hnoG'.1

theorem topology6_rayon_spoof_unlock_rejected :
    let gGuard : LinearToken Nat := .ordered 10 5 .asyncMutexGuard .taskMovable
    ∀ predF predG out,
      ¬ TypedStmt natPrec []
          (.rayonJoin [] [gGuard] (.unlock predF) (.unlock predG))
          [gGuard] out := by
  intro gGuard predF predG out ht
  cases ht with
  | rayonJoin _ _ _ _ _ hf _ =>
    cases hf with
    | unlockToken _ _ _ _ _ hrem _ =>
      nomatch hrem

theorem topology6_rayon_os_recv_waiting_on_sibling_send_rejected :
    let fOb : LinearToken Nat := .ordered 60 10 .chanBlockingRecvOb .taskMovable
    let gOb : LinearToken Nat := .ordered 60 10 .chanBlockingSendOb .taskMovable
    ∀ gBody out,
      ¬ TypedStmt natPrec []
          (.rayonJoin [fOb] [gOb] (.chanBlockingRecv truePred 60 10) gBody)
          [fOb, gOb] out := by
  intro fOb gOb gBody out ht
  cases ht with
  | rayonJoin _ _ _ _ _ hf _ =>
    cases hf with
    | chanBlockingRecv _ _ _ hrem hall =>
      dsimp [fOb, removeFirstToken, truePred] at hrem
      injection hrem with hpair
      injection hpair with _ hremEq
      subst hremEq
      exact Nat.lt_irrefl 10 (hall 10 (List.Mem.head _))

theorem topology6_rayon_holding_os_mutex_rejected :
    ¬ HasNoOsBound [.ordered 1 5 .mutexGuard .osBound] ∧
    (∀ out, ¬ TypedStmt natPrec []
      (.rayonJoin [.ordered 1 5 .mutexGuard .osBound] [] .skip .skip)
      [.ordered 1 5 .mutexGuard .osBound] out) := by
  refine ⟨(fun h => nomatch h.1), ?_⟩
  intro out ht
  cases ht with
  | rayonJoin hnoF _ _ _ _ _ _ => nomatch hnoF.1

-- Topology 7: Async `tokio::sync::Mutex` across `.await` vs sync `Mutex` across `.await`
def asyncScopedSyncStmt : Stmt Nat :=
  .seq (.asyncMutexLockAwait 1 5)
    (.seq (.mutexLock 2 20)
      (.seq (.unlock truePred)
        (.seq (.asyncAwaitPoint 88 10)
          (.unlock truePred))))

theorem topology7_async_mutex_across_await_and_scoped_sync_mutex_positive :
    ValidThreadStmt natPrec asyncScopedSyncStmt [] := by
  have s1 : TypedStmt natPrec [] (.asyncMutexLockAwait 1 5) []
      [.ordered 1 5 .asyncMutexGuard .taskMovable] :=
    .asyncMutexLockAwait 1 5 True.intro True.intro (fun _ h => nomatch h)
  have s2 : TypedStmt natPrec [] (.mutexLock 2 20)
      [.ordered 1 5 .asyncMutexGuard .taskMovable]
      [.ordered 2 20 .mutexGuard .osBound,
       .ordered 1 5 .asyncMutexGuard .taskMovable] := by
    refine .mutexLock 2 20 ?_
    intro l hl
    cases hl with
    | head => decide
    | tail _ h => nomatch h
  have s3 : TypedStmt natPrec [] (.unlock truePred)
      [.ordered 2 20 .mutexGuard .osBound,
       .ordered 1 5 .asyncMutexGuard .taskMovable]
      [.ordered 1 5 .asyncMutexGuard .taskMovable] :=
    .unlockToken truePred 2 20 .mutexGuard .osBound rfl (Or.inl rfl)
  have s4 : TypedStmt natPrec [] (.asyncAwaitPoint 88 10)
      [.ordered 1 5 .asyncMutexGuard .taskMovable]
      [.ordered 1 5 .asyncMutexGuard .taskMovable] := by
    refine .asyncAwaitPoint 88 10 ⟨rfl, True.intro⟩ True.intro ?_
    intro l hl
    cases hl with
    | head => decide
    | tail _ h => nomatch h
  have s5 : TypedStmt natPrec [] (.unlock truePred)
      [.ordered 1 5 .asyncMutexGuard .taskMovable] [] :=
    .unlockToken truePred 1 5 .asyncMutexGuard .taskMovable rfl
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  exact .seq s1 (.seq s2 (.seq s3 (.seq s4 s5)))

theorem topology7_sync_mutex_across_await_single_worker_deadlock :
    let badAsyncWorld : List (ExecUnit Nat) := [
      { uid := 0
        held := [.ordered 0 0 .mutexGuard .osBound]
        wait := .coopBlocked 99 10 },
      { uid := 1
        held := [.ordered 99 10 .condvarSignalOb .taskMovable]
        wait := .osBlocked 0 0 0 }
    ]
    (∀ out, ¬ TypedStmt natPrec [] (.asyncAwaitPoint 99 10)
      [.ordered 0 0 .mutexGuard .osBound] out) ∧
    ¬ WellTypedWorld natPrec badAsyncWorld := by
  refine ⟨?_, ?_⟩
  · intro out ht
    cases ht with
    | asyncAwaitPoint _ _ hnoOs _ _ => nomatch hnoOs.1
  · intro hwt
    have hclean := hwt.clean_yield _ (List.Mem.head _) (Or.inr ⟨99, 10, rfl⟩)
    nomatch hclean.1

end Anneal.DeadlockLogic
