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
import Trusted.Concurrency

namespace Anneal.ConcurrencySeparation

open Trusted.Concurrency

noncomputable def chooseBoolCS (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : Bool :=
  (Classical.choice h).1

theorem chooseBoolCS_spec (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : P (chooseBoolCS P h) :=
  (Classical.choice h).2

theorem chooseBoolCS_congr {P Q : Bool → Prop} (hPQ : P = Q)
    (hP : Nonempty (Subtype P))
    (hQ : Nonempty (Subtype Q)) :
    chooseBoolCS P hP = chooseBoolCS Q hQ := by
  subst hPQ
  rfl

theorem cs_em (p : Prop) : p ∨ ¬ p := by
  let U (x : Bool) : Prop := x = true ∨ p
  let V (x : Bool) : Prop := x = false ∨ p
  have exU : Nonempty (Subtype U) := ⟨⟨true, Or.inl rfl⟩⟩
  have exV : Nonempty (Subtype V) := ⟨⟨false, Or.inl rfl⟩⟩
  have hu : U (chooseBoolCS U exU) := chooseBoolCS_spec U exU
  have hv : V (chooseBoolCS V exV) := chooseBoolCS_spec V exV
  cases Decidable.em (chooseBoolCS U exU = chooseBoolCS V exV) with
  | inr hne =>
    refine Or.inr ?_
    intro hp
    have hUV : U = V := by
      funext x
      exact propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    exact hne (chooseBoolCS_congr hUV exU exV)
  | inl heq =>
    cases hu with
    | inr hp => exact Or.inl hp
    | inl hut =>
      cases hv with
      | inr hp => exact Or.inl hp
      | inl hvf =>
        rw [hut, hvf] at heq
        nomatch heq

theorem eventuallyAlways_implies_infinitelyOften {P : Nat → Prop}
    (h : EventuallyAlways P) : InfinitelyOften P := by
  cases h with
  | intro N₀ hN₀ =>
    intro N
    refine ⟨N + N₀, ?_, ?_⟩
    · exact Nat.le_add_right N N₀
    · exact hN₀ (N + N₀) (Nat.le_add_left N₀ N)

theorem strongFair_implies_weakFair {L : Type} {run : Run L}
    (hsf : StrongFair run) : WeakFair run := by
  intro t hea
  exact hsf t (eventuallyAlways_implies_infinitelyOften hea)

theorem actionStrongFair_implies_actionWeakFair {L : Type}
    {en : Config L → ThreadId → Prop}
    {act : Config L → Config L → ThreadId → Prop}
    {run : Run L}
    (hsf : ActionStrongFair en act run) : ActionWeakFair en act run := by
  intro t hea
  exact hsf t (eventuallyAlways_implies_infinitelyOften hea)

theorem unconditional_implies_weakFairTerminates {L : Type} {sys : ConcSystem L}
    (h : UnconditionalTerminates sys) : WeakFairTerminates sys := by
  intro run hv _
  exact h run hv

theorem weakFair_implies_strongFairTerminates {L : Type} {sys : ConcSystem L}
    (h : WeakFairTerminates sys) : StrongFairTerminates sys := by
  intro run hv hsf
  exact h run hv (strongFair_implies_weakFair hsf)

theorem listGet_unique {α : Type} {xs : List α} {i : Nat} {a b : α}
    (ha : listGet? xs i = some a) (hb : listGet? xs i = some b) : a = b := by
  rw [ha] at hb
  injection hb

theorem listSet_same {α : Type} {es : List α} {i : Nat} {e v : α}
    (hget : listGet? es i = some e) : listGet? (listSet es i v) i = some v := by
  induction es generalizing i with
  | nil => nomatch hget
  | cons hd tl ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih hget

theorem listSet_other {α : Type} {es : List α} {i j : Nat} {v : α}
    (hne : i ≠ j) : listGet? (listSet es i v) j = listGet? es j := by
  induction es generalizing i j with
  | nil => rfl
  | cons hd tl ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ k => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' => exact ih (fun h => hne (congrArg Nat.succ h))

theorem blocked_not_enabled {L : Type} {cfg : Config L} {t : ThreadId}
    (hb : IsBlocked cfg t) (he : IsEnabled cfg t) : False := by
  cases hb with
  | intro eb hrest =>
    cases hrest with
    | intro r hbr =>
      cases he with
      | intro ee heer =>
        have heq : eb = ee := listGet_unique hbr.1 heer.1
        subst heq
        have hst : eb.status = .enabled := heer.2
        rw [hbr.2] at hst
        nomatch hst

theorem active_not_term_not_enabled_is_blocked {L : Type} {cfg : Config L}
    {t : ThreadId}
    (hact : ThreadActive cfg t)
    (hnt : ¬ IsTerminated cfg t)
    (hne : ¬ IsEnabled cfg t) : IsBlocked cfg t := by
  cases hact with
  | intro e hget =>
    cases hst : e.status with
    | enabled => exact False.elim (hne ⟨e, hget, hst⟩)
    | terminated => exact False.elim (hnt ⟨e, hget, hst⟩)
    | blocked r => exact ⟨e, r, hget, hst⟩

theorem inWaitEpisode_not_exited {L : Type} {cfg : Config L} {t : ThreadId}
    (hw : InWaitEpisode cfg t) (hex : ExitedWaitEpisode cfg t) : False := by
  cases hw with
  | intro e1 he1 =>
    cases hex with
    | intro e2 he2 =>
      have heq := listGet_unique he1.1 he2.1
      subst heq
      cases he2.2 with
      | inl hf =>
        have ht := he1.2.1
        rw [hf] at ht
        nomatch ht
      | inr ht => exact he1.2.2 ht

theorem no_step_from_all_disabled_noSpurious {L : Type} {sys : ConcSystem L}
    (hno : NoSpuriousWakes sys)
    {c₀ cfg' : Config L}
    (hdis : ∀ t : ThreadId, ¬ IsEnabled c₀ t)
    (hr : Reaches sys c₀ cfg') : cfg' = c₀ := by
  induction hr with
  | refl => rfl
  | @tail c₂ c₃ tid _ hstep ih =>
    subst ih
    cases hstep with
    | inl hp => exact False.elim (hdis tid (sys.progStepRequiresEnabled tid c₂ c₃ hp))
    | inr hw => exact False.elim (hno tid c₂ c₃ hw)

theorem noSpuriousWakes_implies_spuriousWakeNonRescuing {L : Type}
    {sys : ConcSystem L} (hno : NoSpuriousWakes sys) :
    SpuriousWakeNonRescuing sys := by
  refine ⟨IsGlobalDeadlock, fun _ _ hg => hg, ?_⟩
  intro t c₁ c₂ hg hstep
  cases hstep with
  | inl hp =>
    exact False.elim (hg.2.1 t (sys.progStepRequiresEnabled t c₁ c₂ hp))
  | inr hw =>
    exact False.elim (hno t c₁ c₂ hw)

theorem closedBlockedTrap_implies_deadlockedSubsystem {L : Type}
    {sys : ConcSystem L} {cfg : Config L} {S : ThreadId → Prop}
    (htrap : ClosedBlockedTrap sys cfg S) :
    IsDeadlockedSubsystem sys cfg S := by
  refine ⟨htrap.1, ?_⟩
  intro cfg' hr
  induction hr with
  | refl => exact htrap.2.1
  | @tail c₂ c₃ tid hr₁₂ hstep ih =>
    exact htrap.2.2 c₂ c₃ tid hr₁₂ ih hstep

theorem subsystemDeadlockFree_implies_globalDeadlockFree {L : Type}
    {sys : ConcSystem L}
    (hno : NoSpuriousWakes sys)
    (hsdf : SubsystemDeadlockFree sys) : GlobalDeadlockFree sys := by
  intro cfg hreach hgdl
  cases hgdl.1 with
  | intro t₀ ht₀ =>
    have hb₀ : IsBlocked cfg t₀ :=
      active_not_term_not_enabled_is_blocked ht₀.1 ht₀.2 (hgdl.2.1 t₀)
    have hsub : IsDeadlockedSubsystem sys cfg (fun t => t = t₀) := by
      refine ⟨⟨t₀, rfl⟩, ?_⟩
      intro cfg' hr t ht
      subst ht
      have heq : cfg' = cfg :=
        no_step_from_all_disabled_noSpurious hno hgdl.2.1 hr
      subst heq
      exact hb₀
    exact hsdf cfg hreach (fun t => t = t₀) hsub

/-- Master Implication (works directly for systems WITH
`OsSpuriousFutexWake`!): whenever `sys` satisfies `SpuriousWakeNonRescuing`
(automatic for deterministic `NoSpuriousWakes` systems AND proved below for all
`WellFormedFutexProg` systems under `mkSpuriousProgSystem`),
`SubsystemDeadlockFreeWaitEpisode sys` implies `GlobalDeadlockFree sys`. -/
theorem subsystemDeadlockFreeWaitEpisode_implies_globalDeadlockFree
    {L : Type} {sys : ConcSystem L}
    (hnonres : SpuriousWakeNonRescuing sys)
    (hsdf : SubsystemDeadlockFreeWaitEpisode sys) : GlobalDeadlockFree sys := by
  intro cfg hreach hgdl
  cases hnonres with
  | intro Trap hTrap =>
    cases hgdl.1 with
    | intro t₀ ht₀ =>
      have hw₀ : InWaitEpisode cfg t₀ := by
        cases hgdl.2.2 t₀ ht₀.1 with
        | inl hw => exact hw
        | inr ht => exact False.elim (ht₀.2 ht)
      have hsub : IsDeadlockedSubsystemWaitEpisode sys cfg (fun t => t = t₀) := by
        refine ⟨⟨t₀, rfl⟩, ?_, ?_⟩
        · intro t ht; subst ht; exact hw₀
        · intro cfg' hr t ht
          subst ht
          have hboth : Trap cfg' ∧ InWaitEpisode cfg' t := by
            induction hr with
            | refl => exact ⟨hTrap.1 cfg hreach hgdl, hw₀⟩
            | @tail c₂ c₃ tid _ hstep ih =>
              have hnext := hTrap.2 tid c₂ c₃ ih.1 hstep
              exact ⟨hnext.1, hnext.2 t ih.2⟩
          intro hex
          exact inWaitEpisode_not_exited hboth.2 hex
      exact hsdf cfg hreach (fun t => t = t₀) hsub

structure FinitePrefix (sys : ConcSystem L) (target : Config L) where
  len : Nat
  states : Nat → Config L
  steps : Nat → ThreadId
  start_eq : states 0 = sys.init
  end_eq : states len = target
  valid_step : ∀ i : Nat, i < len → sys.stepBy (steps i) (states i) (states (i + 1))

theorem buildPrefix {L : Type} {sys : ConcSystem L} {cfg : Config L}
    (hr : Reachable sys cfg) : ∃ _ : FinitePrefix sys cfg, True := by
  change Reaches sys sys.init cfg at hr
  induction hr with
  | refl =>
    exact ⟨{
      len := 0
      states := fun _ => sys.init
      steps := fun _ => 0
      start_eq := rfl
      end_eq := rfl
      valid_step := fun _ hi => nomatch hi
    }, True.intro⟩
  | @tail c₂ c₃ tid _ hstep ih =>
    cases ih with
    | intro p _ =>
      refine ⟨{
        len := p.len + 1
        states := fun i => if i ≤ p.len then p.states i else c₃
        steps := fun i => if i < p.len then p.steps i else tid
        start_eq := by simp [Nat.zero_le, p.start_eq]
        end_eq := by
          have hnot : ¬ (p.len + 1 ≤ p.len) := Nat.not_succ_le_self p.len
          simp [hnot]
        valid_step := by
          intro i hi
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
          | inl hlt =>
            have hle1 : i ≤ p.len := Nat.le_of_lt hlt
            have hle2 : i + 1 ≤ p.len := hlt
            simp [hlt, hle1, hle2]
            exact p.valid_step i hlt
          | inr heq =>
            subst heq
            have hle : p.len ≤ p.len := Nat.le_refl p.len
            have hlt_irrefl : ¬ (p.len < p.len) := Nat.lt_irrefl p.len
            have hnle : ¬ (p.len + 1 ≤ p.len) := Nat.not_succ_le_self p.len
            simp [hle, hlt_irrefl, hnle, p.end_eq]
            exact hstep
      }, True.intro⟩

theorem strongFairTerminates_implies_globalDeadlockFree {L : Type}
    {sys : ConcSystem L}
    (hsft : StrongFairTerminates sys) : GlobalDeadlockFree sys := by
  intro cfg hreach hgdl
  cases buildPrefix hreach with
  | intro p _ =>
    let run : Run L := {
      trace := fun n => if n ≤ p.len then p.states n else cfg
      stepAt := fun n => if n < p.len then some (p.steps n) else none
    }
    have hnoProg : ∀ t c', ¬ sys.progStepBy t cfg c' :=
      fun t c' hp => hgdl.2.1 t (sys.progStepRequiresEnabled t cfg c' hp)
    have hv : ValidRun sys run := by
      refine ⟨by simp [run, Nat.zero_le, p.start_eq], ?_⟩
      intro n
      cases Decidable.em (n < p.len) with
      | inl hlt =>
        have hle1 : n ≤ p.len := Nat.le_of_lt hlt
        have hle2 : n + 1 ≤ p.len := hlt
        simp [run, hlt, hle1, hle2]
        exact p.valid_step n hlt
      | inr hnlt =>
        simp [run, hnlt]
        cases Decidable.em (n ≤ p.len) with
        | inl hle =>
          have heq : n = p.len := Nat.le_antisymm hle (Nat.ge_of_not_lt hnlt)
          subst heq
          have hnle : ¬ (p.len + 1 ≤ p.len) := Nat.not_succ_le_self p.len
          simp [Nat.le_refl, hnle, p.end_eq]
          exact ⟨hgdl.2.1, hnoProg⟩
        | inr hnle =>
          have hnle2 : ¬ (n + 1 ≤ p.len) := fun h => hnle (Nat.le_of_succ_le h)
          simp [hnle, hnle2]
          exact ⟨hgdl.2.1, hnoProg⟩
    have hsf : StrongFair run := by
      intro t hio
      cases hio (p.len + 1) with
      | intro n hn =>
        have hnle : ¬ (n ≤ p.len) :=
          fun h => Nat.not_succ_le_self p.len (Nat.le_trans hn.1 h)
        have hen : IsEnabled cfg t := by
          have hraw := hn.2
          simp [run, hnle] at hraw
          exact hraw
        exact False.elim (hgdl.2.1 t hen)
    have hterm : RunTerminates run := hsft run hv hsf
    cases hterm with
    | intro n hall =>
      dsimp at hall
      cases Decidable.em (n < p.len) with
      | inl hlt =>
        have hstep := p.valid_step n hlt
        have hnt :=
          stepRequiresNotTerminated sys
            (p.steps n) (p.states n) (p.states (n + 1)) hstep
        have hle : n ≤ p.len := Nat.le_of_lt hlt
        have hall' : AllTerminated (p.states n) := by
          simp [run, hle] at hall
          exact hall
        cases hnt.1 with
        | intro e he =>
          exact hnt.2 ⟨e, he, hall' (p.steps n) e he⟩
      | inr hnlt =>
        have hcfg : run.trace n = cfg := by
          cases Decidable.em (n ≤ p.len) with
          | inl hle =>
            have heq : n = p.len := Nat.le_antisymm hle (Nat.ge_of_not_lt hnlt)
            subst heq
            simp [run, Nat.le_refl, p.end_eq]
          | inr hnle =>
            simp [run, hnle]
        rw [hcfg] at hall
        cases hgdl.1 with
        | intro t₀ ht₀ =>
          cases ht₀.1 with
          | intro e₀ he₀ =>
            exact ht₀.2 ⟨e₀, he₀, hall t₀ e₀ he₀⟩

theorem mkProgSystem_noSpuriousWakes (prog : ConcProg) :
    NoSpuriousWakes (mkProgSystem prog) :=
  fun _ _ _ h => h

/-! ### Instruction Reduction Helpers (`rfl`, avoiding lazy `Trusted.*.eq_1`) -/

theorem eval_casLoop (t : ThreadId) (st : RegState) (iw : Bool)
    (addr exp des npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.casLoop addr exp des npc) c =
      if Nat.beq (c.mem addr) exp then
        { c with
          threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr des }
      else c := rfl

theorem eval_store (t : ThreadId) (st : RegState) (iw : Bool)
    (addr val npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.store addr val npc) c =
      { c with
        threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩
        mem := memWrite c.mem addr val } := rfl

theorem eval_storeRegSucc (t : ThreadId) (st : RegState) (iw : Bool)
    (addr npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.storeRegSucc addr npc) c =
      { c with
        threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩
        mem := memWrite c.mem addr (st.reg + 1) } := rfl

theorem eval_fetchAdd (t : ThreadId) (st : RegState) (iw : Bool)
    (addr npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.fetchAdd addr npc) c =
      { c with
        threads := listSet c.threads t ⟨⟨npc, c.mem addr⟩, .enabled, false⟩
        mem := memWrite c.mem addr (c.mem addr + 1) } := rfl

theorem eval_awaitRegEq (t : ThreadId) (st : RegState) (iw : Bool)
    (addr npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.awaitRegEq addr npc) c =
      if Nat.beq (c.mem addr) st.reg then
        { c with threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩ }
      else c := rfl

theorem eval_futexLock (t : ThreadId) (st : RegState) (iw : Bool)
    (addr npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.futexLock addr npc) c =
      if Nat.beq (c.mem addr) 0 then
        { c with
          threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr 1 }
      else
        { c with
          threads := listSet c.threads t
            ⟨st, .blocked (.futex addr (c.mem addr)), true⟩ } := rfl

theorem eval_futexWaitEnter (t : ThreadId) (st : RegState) (iw : Bool)
    (addr checkPc acqPc : Nat) (c : Config RegState) :
    evalInstr t st iw (.futexWaitEnter addr checkPc acqPc) c =
      if iw then
        { c with
          threads := listSet c.threads t ⟨⟨checkPc, st.reg + 1⟩, .enabled, true⟩ }
      else if Nat.beq (c.mem addr) 0 then
        { c with
          threads := listSet c.threads t ⟨⟨acqPc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr 1 }
      else
        { c with
          threads := listSet c.threads t
            ⟨st, .blocked (.futex addr (c.mem addr)), true⟩ } := rfl

theorem eval_futexRetryAcquire (t : ThreadId) (st : RegState) (iw : Bool)
    (addr waitPc acqPc : Nat) (c : Config RegState) :
    evalInstr t st iw (.futexRetryAcquire addr waitPc acqPc) c =
      if Nat.beq (c.mem addr) 0 then
        { c with
          threads := listSet c.threads t ⟨⟨acqPc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr 1 }
      else
        { c with
          threads := listSet c.threads t
            ⟨⟨waitPc, st.reg⟩, .blocked (.futex addr (c.mem addr)), true⟩ } := rfl

theorem eval_futexUnlock (t : ThreadId) (st : RegState) (iw : Bool)
    (addr npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.futexUnlock addr npc) c =
      let woken := wakeFutexAll addr c.threads
      { c with
        threads := listSet woken t ⟨⟨npc, st.reg⟩, .enabled, false⟩
        mem := memWrite c.mem addr 0 } := rfl

theorem eval_parkWait (t : ThreadId) (st : RegState) (iw : Bool)
    (npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.parkWait npc) c =
      if c.parkToken t then
        { c with
          threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩
          parkToken := fun u => if Nat.beq u t then false else c.parkToken u }
      else
        { c with threads := listSet c.threads t ⟨st, .blocked .park, true⟩ } := rfl

theorem eval_unparkThread (t : ThreadId) (st : RegState) (iw : Bool)
    (target npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.unparkThread target npc) c =
      let woken := wakeParked target c.threads
      { c with
        threads := listSet woken t ⟨⟨npc, st.reg⟩, .enabled, false⟩
        parkToken := fun u => if Nat.beq u target then true else c.parkToken u } := rfl

theorem eval_joinThread (t : ThreadId) (st : RegState) (iw : Bool)
    (target npc : Nat) (c : Config RegState) :
    evalInstr t st iw (.joinThread target npc) c =
      match listGet? c.threads target with
      | some te =>
          match te.status with
          | .terminated =>
              { c with threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩ }
          | _ =>
              { c with threads := listSet c.threads t ⟨st, .blocked (.join target), true⟩ }
      | none =>
          { c with threads := listSet c.threads t ⟨⟨npc, st.reg⟩, .enabled, false⟩ } := rfl

theorem eval_spinSelf (t : ThreadId) (st : RegState) (iw : Bool) (c : Config RegState) :
    evalInstr t st iw .spinSelf c = c := rfl

theorem eval_halt (t : ThreadId) (st : RegState) (iw : Bool) (c : Config RegState) :
    evalInstr t st iw .halt c =
      { c with threads := wakeJoiners t (listSet c.threads t ⟨st, .terminated, false⟩) } := rfl

theorem memWrite_eq (m : Addr → Val) (a v x : Nat) :
    memWrite m a v x = (if Nat.beq x a then v else m x) := rfl

theorem memWrite_same (m : Addr → Val) (a v : Nat) :
    memWrite m a v a = v := by
  rw [memWrite_eq, Nat.beq_refl a]
  rfl

theorem memWrite_diff (m : Addr → Val) {a b : Nat} (v : Nat)
    (hb : Nat.beq b a = false) :
    memWrite m a v b = m b := by
  rw [memWrite_eq, hb]
  rfl

theorem listGet_zero {α : Type} (x : α) (xs : List α) :
    listGet? (x :: xs) 0 = some x := rfl

theorem listGet_succ {α : Type} (x : α) (xs : List α) (k : Nat) :
    listGet? (x :: xs) (k + 1) = listGet? xs k := rfl

theorem wakeFutexAll_cons (addr : Addr) (hd : ThreadEntry RegState)
    (tl : List (ThreadEntry RegState)) :
    wakeFutexAll addr (hd :: tl) =
      (match hd.status with
       | .blocked (.futex a _) =>
           if Nat.beq a addr then { hd with status := .enabled } else hd
       | _ => hd) :: wakeFutexAll addr tl := rfl

theorem wakeJoiners_cons (doneTid : ThreadId) (hd : ThreadEntry RegState)
    (tl : List (ThreadEntry RegState)) :
    wakeJoiners doneTid (hd :: tl) =
      (match hd.status with
       | .blocked (.join target) =>
           if Nat.beq target doneTid then { hd with status := .enabled } else hd
       | _ => hd) :: wakeJoiners doneTid tl := rfl

theorem wakeParked_eq (target : ThreadId)
    (entries : List (ThreadEntry RegState)) :
    wakeParked target entries =
      match listGet? entries target with
      | some e =>
          match e.status with
          | .blocked .park => listSet entries target { e with status := .enabled }
          | _ => entries
      | none => entries := rfl

theorem wakeFutexAll_get_blocked {addr : Addr}
    {es : List (ThreadEntry RegState)} {i : Nat} {e : ThreadEntry RegState}
    {r : WaitReason}
    (hget : listGet? (wakeFutexAll addr es) i = some e)
    (hblk : e.status = .blocked r) :
    listGet? es i = some e ∧ ∀ exp, r ≠ .futex addr exp := by
  induction es generalizing i with
  | nil => nomatch hget
  | cons hd tl ih =>
    rw [wakeFutexAll_cons] at hget
    cases i with
    | zero =>
      rw [listGet_zero] at hget
      injection hget with heq
      cases hst : hd.status with
      | enabled =>
        rw [hst] at heq; dsimp at heq; subst heq; rw [hst] at hblk; nomatch hblk
      | terminated =>
        rw [hst] at heq; dsimp at heq; subst heq; rw [hst] at hblk; nomatch hblk
      | blocked r₀ =>
        rw [hst] at heq
        cases r₀ with
        | park =>
          dsimp at heq; subst heq
          refine ⟨rfl, fun _ h => ?_⟩
          rw [hst] at hblk; injection hblk with hr; rw [← hr] at h; nomatch h
        | join target =>
          dsimp at heq; subst heq
          refine ⟨rfl, fun _ h => ?_⟩
          rw [hst] at hblk; injection hblk with hr; rw [← hr] at h; nomatch h
        | futex a exp₀ =>
          dsimp at heq
          cases hbeq : Nat.beq a addr with
          | true =>
            rw [hbeq] at heq; dsimp at heq; subst heq; nomatch hblk
          | false =>
            rw [hbeq] at heq; dsimp at heq; subst heq
            refine ⟨rfl, fun exp h => ?_⟩
            rw [hst] at hblk; injection hblk with hr; rw [← hr] at h
            injection h with ha _
            subst ha
            rw [Nat.beq_refl a] at hbeq
            nomatch hbeq
    | succ k =>
      rw [listGet_succ] at hget
      exact ih hget

theorem wakeJoiners_get_blocked {doneTid : ThreadId}
    {es : List (ThreadEntry RegState)} {i : Nat} {e : ThreadEntry RegState}
    {r : WaitReason}
    (hget : listGet? (wakeJoiners doneTid es) i = some e)
    (hblk : e.status = .blocked r) :
    listGet? es i = some e := by
  induction es generalizing i with
  | nil => nomatch hget
  | cons hd tl ih =>
    rw [wakeJoiners_cons] at hget
    cases i with
    | zero =>
      rw [listGet_zero] at hget
      injection hget with heq
      cases hst : hd.status with
      | enabled =>
        rw [hst] at heq; dsimp at heq; subst heq; rw [hst] at hblk; nomatch hblk
      | terminated =>
        rw [hst] at heq; dsimp at heq; subst heq; rw [hst] at hblk; nomatch hblk
      | blocked r₀ =>
        rw [hst] at heq
        cases r₀ with
        | park => dsimp at heq; subst heq; rfl
        | futex a exp₀ => dsimp at heq; subst heq; rfl
        | join target =>
          dsimp at heq
          cases hbeq : Nat.beq target doneTid with
          | true => rw [hbeq] at heq; dsimp at heq; subst heq; nomatch hblk
          | false => rw [hbeq] at heq; dsimp at heq; subst heq; rfl
    | succ k =>
      rw [listGet_succ] at hget
      exact ih hget

theorem enabled_pair {c : Config RegState} {s0 s1 : RegState} {w0 w1 : Bool}
    (hth : c.threads = [⟨s0, .enabled, w0⟩, ⟨s1, .enabled, w1⟩]) :
    IsEnabled c 0 ∧ IsEnabled c 1 := by
  refine ⟨⟨⟨s0, .enabled, w0⟩, ?_, rfl⟩, ⟨⟨s1, .enabled, w1⟩, ?_, rfl⟩⟩
  · rw [hth]; rfl
  · rw [hth]; rfl

/-! ### Spin-Only Programs Never Enter `inWaitEpisode` (`SubsystemDeadlockFreeWaitEpisode`) -/

def IsSpinOnlyInstr : ConcInstr → Prop
  | .casLoop _ _ _ _ => True
  | .store _ _ _ => True
  | .storeRegSucc _ _ => True
  | .fetchAdd _ _ => True
  | .awaitRegEq _ _ => True
  | .spinSelf => True
  | .halt => True
  | .futexLock _ _ => False
  | .futexWaitEnter _ _ _ => False
  | .futexRetryAcquire _ _ _ => False
  | .futexUnlock _ _ => False
  | .parkWait _ => False
  | .unparkThread _ _ => False
  | .joinThread _ _ => False

def IsSpinOnlyProg (prog : ConcProg) : Prop :=
  ∀ (t : ThreadId) (body : Nat → ConcInstr),
    listGet? prog t = some body → ∀ pc : Nat, IsSpinOnlyInstr (body pc)

def NoWaitOrBlockedEntries (entries : List (ThreadEntry RegState)) : Prop :=
  @List.rec (ThreadEntry RegState) (fun _ => Prop)
    True
    (fun e _ ih =>
      e.inWaitEpisode = false ∧ (∀ r : WaitReason, e.status ≠ .blocked r) ∧ ih)
    entries

theorem noWaitOrBlocked_initProgThreads (prog : ConcProg) :
    NoWaitOrBlockedEntries (initProgThreads prog) := by
  induction prog with
  | nil => exact True.intro
  | cons _ rest ih =>
    refine ⟨rfl, ?_, ih⟩
    intro r hr
    nomatch hr

theorem noWaitOrBlocked_listSet {es : List (ThreadEntry RegState)}
    (h : NoWaitOrBlockedEntries es) (t : Nat) (e' : ThreadEntry RegState)
    (hw' : e'.inWaitEpisode = false)
    (hb' : ∀ r : WaitReason, e'.status ≠ .blocked r) :
    NoWaitOrBlockedEntries (listSet es t e') := by
  induction es generalizing t with
  | nil => exact True.intro
  | cons e rest ih =>
    cases t with
    | zero => exact ⟨hw', hb', h.2.2⟩
    | succ k => exact ⟨h.1, h.2.1, ih h.2.2 k⟩

theorem noWaitOrBlocked_wakeJoiners {es : List (ThreadEntry RegState)}
    (h : NoWaitOrBlockedEntries es) (doneTid : ThreadId) :
    NoWaitOrBlockedEntries (wakeJoiners doneTid es) := by
  induction es with
  | nil => exact True.intro
  | cons e rest ih =>
    rw [wakeJoiners_cons]
    refine ⟨?_, ?_, ih h.2.2⟩
    · cases hst : e.status with
      | enabled => exact h.1
      | terminated => exact h.1
      | blocked r₀ => exact False.elim (h.2.1 r₀ hst)
    · intro r
      cases hst : e.status with
      | enabled => rw [hst]; exact fun h => nomatch h
      | terminated => rw [hst]; exact fun h => nomatch h
      | blocked r₀ => exact False.elim (h.2.1 r₀ hst)

theorem noWaitOrBlocked_entries_get {es : List (ThreadEntry RegState)}
    (h : NoWaitOrBlockedEntries es) {t : Nat} {e : ThreadEntry RegState}
    (hget : listGet? es t = some e) :
    e.inWaitEpisode = false ∧ ∀ r : WaitReason, e.status ≠ .blocked r := by
  induction es generalizing t with
  | nil => nomatch hget
  | cons hd tl ih =>
    cases t with
    | zero =>
      injection hget with heq
      subst heq
      exact ⟨h.1, h.2.1⟩
    | succ k =>
      exact ih h.2.2 hget

theorem not_blocked_enabled : ∀ r : WaitReason, ThreadStatus.enabled ≠ .blocked r :=
  fun _ h => nomatch h

theorem not_blocked_terminated : ∀ r : WaitReason, ThreadStatus.terminated ≠ .blocked r :=
  fun _ h => nomatch h

theorem spinOnly_evalInstr_noWaitOrBlocked {t : ThreadId} {st : RegState}
    {iw : Bool} {instr : ConcInstr} {c : Config RegState}
    (hinstr : IsSpinOnlyInstr instr) (ih : NoWaitOrBlockedEntries c.threads) :
    NoWaitOrBlockedEntries (evalInstr t st iw instr c).threads := by
  cases instr with
  | casLoop addr exp des npc =>
    rw [eval_casLoop]
    cases hb : Nat.beq (c.mem addr) exp with
    | false => dsimp; exact ih
    | true => dsimp; exact noWaitOrBlocked_listSet ih t _ rfl not_blocked_enabled
  | store _ _ _ =>
    exact noWaitOrBlocked_listSet ih t _ rfl not_blocked_enabled
  | storeRegSucc _ _ =>
    exact noWaitOrBlocked_listSet ih t _ rfl not_blocked_enabled
  | fetchAdd _ _ =>
    exact noWaitOrBlocked_listSet ih t _ rfl not_blocked_enabled
  | awaitRegEq addr _ =>
    rw [eval_awaitRegEq]
    cases hb : Nat.beq (c.mem addr) st.reg with
    | false => dsimp; exact ih
    | true => dsimp; exact noWaitOrBlocked_listSet ih t _ rfl not_blocked_enabled
  | futexLock _ _ => exact False.elim hinstr
  | futexWaitEnter _ _ _ => exact False.elim hinstr
  | futexRetryAcquire _ _ _ => exact False.elim hinstr
  | futexUnlock _ _ => exact False.elim hinstr
  | parkWait _ => exact False.elim hinstr
  | unparkThread _ _ => exact False.elim hinstr
  | joinThread _ _ => exact False.elim hinstr
  | spinSelf => exact ih
  | halt =>
    exact noWaitOrBlocked_wakeJoiners
      (noWaitOrBlocked_listSet ih t _ rfl not_blocked_terminated) t

theorem spinOnlyProg_preserves_noWaitOrBlocked_det {prog : ConcProg}
    (hspin : IsSpinOnlyProg prog) {cfg : Config RegState}
    (hr : Reachable (mkProgSystem prog) cfg) :
    NoWaitOrBlockedEntries cfg.threads := by
  change Reaches (mkProgSystem prog) (mkProgSystem prog).init cfg at hr
  induction hr with
  | refl => exact noWaitOrBlocked_initProgThreads prog
  | @tail c₂ c₃ tid _ hstep ih =>
    cases hstep with
    | inl hp =>
      cases hp with
      | intro e hrest =>
        cases hrest with
        | intro body hb =>
          rw [hb.2.2.2]
          exact spinOnly_evalInstr_noWaitOrBlocked
            (hspin tid body hb.2.2.1 e.localState.pc) ih
    | inr hw => exact False.elim hw

theorem spinOnlyProg_preserves_noWaitOrBlocked_spurious {prog : ConcProg}
    (hspin : IsSpinOnlyProg prog) {cfg : Config RegState}
    (hr : Reachable (mkSpuriousProgSystem prog) cfg) :
    NoWaitOrBlockedEntries cfg.threads := by
  change Reaches (mkSpuriousProgSystem prog) (mkSpuriousProgSystem prog).init cfg at hr
  induction hr with
  | refl => exact noWaitOrBlocked_initProgThreads prog
  | @tail c₂ c₃ tid _ hstep ih =>
    cases hstep with
    | inl hp =>
      cases hp with
      | intro e hrest =>
        cases hrest with
        | intro body hb =>
          rw [hb.2.2.2]
          exact spinOnly_evalInstr_noWaitOrBlocked
            (hspin tid body hb.2.2.1 e.localState.pc) ih
    | inr hw =>
      cases hw with
      | intro st h1 =>
        cases h1 with
        | intro addr h2 =>
          cases h2 with
          | intro exp hwk =>
            have hnb := (noWaitOrBlocked_entries_get ih hwk.1).2 (.futex addr exp)
            exact False.elim (hnb rfl)

/-- Spin-only programs never enter `inWaitEpisode`, hence satisfy
`SubsystemDeadlockFreeWaitEpisode` under BOTH `mkProgSystem` and
`mkSpuriousProgSystem`. -/
theorem spinOnly_subsystemDeadlockFreeWaitEpisode {prog : ConcProg}
    (hspin : IsSpinOnlyProg prog) :
    SubsystemDeadlockFreeWaitEpisode (mkProgSystem prog) ∧
    SubsystemDeadlockFreeWaitEpisode (mkSpuriousProgSystem prog) := by
  refine ⟨?_, ?_⟩
  · intro cfg hr S hsub
    cases hsub.1 with
    | intro t₀ ht₀ =>
      cases hsub.2.1 t₀ ht₀ with
      | intro e he =>
        have hnw := (noWaitOrBlocked_entries_get
          (spinOnlyProg_preserves_noWaitOrBlocked_det hspin hr) he.1).1
        rw [he.2.1] at hnw
        nomatch hnw
  · intro cfg hr S hsub
    cases hsub.1 with
    | intro t₀ ht₀ =>
      cases hsub.2.1 t₀ ht₀ with
      | intro e he =>
        have hnw := (noWaitOrBlocked_entries_get
          (spinOnlyProg_preserves_noWaitOrBlocked_spurious hspin hr) he.1).1
        rw [he.2.1] at hnw
        nomatch hnw

theorem spinOnly_spurious_nonRescuing {prog : ConcProg}
    (hspin : IsSpinOnlyProg prog) :
    SpuriousWakeNonRescuing (mkSpuriousProgSystem prog) := by
  refine ⟨fun c => NoWaitOrBlockedEntries c.threads ∧ IsGlobalDeadlock c, ?_, ?_⟩
  · intro cfg hr hg
    exact ⟨spinOnlyProg_preserves_noWaitOrBlocked_spurious hspin hr, hg⟩
  · intro t c₁ c₂ htrap hstep
    cases hstep with
    | inl hp =>
      exact False.elim (htrap.2.2.1 t (progStepRequiresEnabled prog t c₁ c₂ hp))
    | inr hw =>
      cases hw with
      | intro st h1 =>
        cases h1 with
        | intro addr h2 =>
          cases h2 with
          | intro exp hwk =>
            have hnb := (noWaitOrBlocked_entries_get htrap.1 hwk.1).2 (.futex addr exp)
            exact False.elim (hnb rfl)

theorem spinOnlyProg_globalDeadlockFree {prog : ConcProg}
    (hspin : IsSpinOnlyProg prog) :
    GlobalDeadlockFree (mkProgSystem prog) :=
  subsystemDeadlockFreeWaitEpisode_implies_globalDeadlockFree
    (noSpuriousWakes_implies_spuriousWakeNonRescuing (mkProgSystem_noSpuriousWakes prog))
    (spinOnly_subsystemDeadlockFreeWaitEpisode hspin).1

/-! ### General `WellFormedFutexProg` Non-Rescuing Theorem for `mkSpuriousProgSystem` -/

def IsWellFormedFutexInstr (body : Nat → ConcInstr) (pc : Nat) : Prop :=
  match body pc with
  | .futexLock _ _ => True
  | .futexWaitEnter addr checkPc acqPc =>
      body checkPc = .futexRetryAcquire addr pc acqPc
  | .futexRetryAcquire addr waitPc acqPc =>
      body waitPc = .futexWaitEnter addr pc acqPc
  | .futexUnlock _ _ => True
  | .spinSelf => True
  | .halt => True
  | _ => False

def WellFormedFutexProg (prog : ConcProg) : Prop :=
  ∀ (t : ThreadId) (body : Nat → ConcInstr),
    listGet? prog t = some body → ∀ pc : Nat, IsWellFormedFutexInstr body pc

def BlockedFutexContended (prog : ConcProg) (c : Config RegState) : Prop :=
  ∀ (t : ThreadId) (e : ThreadEntry RegState) (r : WaitReason),
    listGet? c.threads t = some e →
    e.status = .blocked r →
    ∃ (addr : Addr) (exp : Val) (body : Nat → ConcInstr),
      r = .futex addr exp ∧
      c.mem addr ≠ 0 ∧
      listGet? prog t = some body ∧
      ((∃ npc, body e.localState.pc = .futexLock addr npc) ∨
       (∃ checkPc acqPc, body e.localState.pc = .futexWaitEnter addr checkPc acqPc))

theorem memWrite_nonzero_preserves_nonzero (m : Addr → Val) (a addr : Addr)
    (h : m addr ≠ 0) : memWrite m a 1 addr ≠ 0 := by
  rw [memWrite_eq]
  cases Nat.beq addr a with
  | true => dsimp; exact fun h0 => nomatch h0
  | false => exact h

theorem nat_beq_zero_false_implies_ne_zero {x : Nat} (h : Nat.beq x 0 = false) :
    x ≠ 0 := by
  intro hx
  subst hx
  nomatch h

theorem wellFormedFutex_preserves_blockedContended {prog : ConcProg}
    (hwf : WellFormedFutexProg prog) {cfg : Config RegState}
    (hr : Reachable (mkSpuriousProgSystem prog) cfg) :
    BlockedFutexContended prog cfg := by
  change Reaches (mkSpuriousProgSystem prog) (mkSpuriousProgSystem prog).init cfg at hr
  induction hr with
  | refl =>
    intro t e r hget hblk
    have hnb := (noWaitOrBlocked_entries_get
      (noWaitOrBlocked_initProgThreads prog) hget).2 r
    exact False.elim (hnb hblk)
  | @tail c₂ c₃ tid _ hstep ih =>
    cases hstep with
    | inr hw =>
      cases hw with
      | intro st h1 =>
        cases h1 with
        | intro addr h2 =>
          cases h2 with
          | intro exp hwk =>
            rw [hwk.2]
            intro t e r hget hblk
            cases Decidable.em (tid = t) with
            | inl heq =>
              subst heq
              have hsame := listSet_same (v := ⟨st, .enabled, true⟩) hwk.1
              dsimp at hget
              have hee := listGet_unique hget hsame
              subst hee
              nomatch hblk
            | inr hne =>
              dsimp at hget
              rw [listSet_other hne] at hget
              exact ih t e r hget hblk
    | inl hp =>
      cases hp with
      | intro e0 hrest =>
        cases hrest with
        | intro body0 hb =>
          have hget0 := hb.1
          have hprog0 := hb.2.2.1
          have hc3 := hb.2.2.2
          subst hc3
          have hwf0 := hwf tid body0 hprog0 e0.localState.pc
          unfold IsWellFormedFutexInstr at hwf0
          cases hinstr : body0 e0.localState.pc with
          | casLoop _ _ _ _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | store _ _ _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | storeRegSucc _ _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | fetchAdd _ _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | awaitRegEq _ _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | parkWait _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | unparkThread _ _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | joinThread _ _ => rw [hinstr] at hwf0; exact False.elim hwf0
          | spinSelf =>
            rw [eval_spinSelf]
            exact ih
          | halt =>
            rw [eval_halt]
            intro t e r hget hblk
            dsimp at hget
            have hpre := wakeJoiners_get_blocked hget hblk
            cases Decidable.em (tid = t) with
            | inl heq =>
              subst heq
              have hsame := listSet_same (v := ⟨e0.localState, .terminated, false⟩) hget0
              have hee := listGet_unique hpre hsame
              subst hee; nomatch hblk
            | inr hne =>
              rw [listSet_other hne] at hpre
              exact ih t e r hpre hblk
          | futexLock a npc =>
            rw [eval_futexLock]
            cases hbeq : Nat.beq (c₂.mem a) 0 with
            | true =>
              dsimp
              intro t e r hget hblk
              cases Decidable.em (tid = t) with
              | inl heq =>
                subst heq
                have hsame := listSet_same (v := ⟨⟨npc, e0.localState.reg⟩, .enabled, false⟩) hget0
                have hee := listGet_unique hget hsame
                subst hee; nomatch hblk
              | inr hne =>
                rw [listSet_other hne] at hget
                cases ih t e r hget hblk with
                | intro addr hr1 =>
                  cases hr1 with
                  | intro exp hr2 =>
                    cases hr2 with
                    | intro bd hbd =>
                      exact ⟨addr, exp, bd, hbd.1,
                        memWrite_nonzero_preserves_nonzero c₂.mem a addr hbd.2.1,
                        hbd.2.2⟩
            | false =>
              dsimp
              intro t e r hget hblk
              cases Decidable.em (tid = t) with
              | inl heq =>
                subst heq
                have hsame := listSet_same
                  (v := ⟨e0.localState, .blocked (.futex a (c₂.mem a)), true⟩) hget0
                have hee := listGet_unique hget hsame
                subst hee
                injection hblk with hrEq
                exact ⟨a, c₂.mem a, body0, Eq.symm hrEq,
                  nat_beq_zero_false_implies_ne_zero hbeq,
                  hprog0, Or.inl ⟨npc, hinstr⟩⟩
              | inr hne =>
                rw [listSet_other hne] at hget
                exact ih t e r hget hblk
          | futexWaitEnter a checkPc acqPc =>
            rw [eval_futexWaitEnter]
            cases e0.inWaitEpisode with
            | true =>
              dsimp
              intro t e r hget hblk
              cases Decidable.em (tid = t) with
              | inl heq =>
                subst heq
                have hsame := listSet_same
                  (v := ⟨⟨checkPc, e0.localState.reg + 1⟩, .enabled, true⟩) hget0
                have hee := listGet_unique hget hsame
                subst hee; nomatch hblk
              | inr hne =>
                rw [listSet_other hne] at hget
                exact ih t e r hget hblk
            | false =>
              dsimp
              cases hbeq : Nat.beq (c₂.mem a) 0 with
              | true =>
                dsimp
                intro t e r hget hblk
                cases Decidable.em (tid = t) with
                | inl heq =>
                  subst heq
                  have hsame := listSet_same
                    (v := ⟨⟨acqPc, e0.localState.reg⟩, .enabled, false⟩) hget0
                  have hee := listGet_unique hget hsame
                  subst hee; nomatch hblk
                | inr hne =>
                  rw [listSet_other hne] at hget
                  cases ih t e r hget hblk with
                  | intro addr hr1 =>
                    cases hr1 with
                    | intro exp hr2 =>
                      cases hr2 with
                      | intro bd hbd =>
                        exact ⟨addr, exp, bd, hbd.1,
                          memWrite_nonzero_preserves_nonzero c₂.mem a addr hbd.2.1,
                          hbd.2.2⟩
              | false =>
                dsimp
                intro t e r hget hblk
                cases Decidable.em (tid = t) with
                | inl heq =>
                  subst heq
                  have hsame := listSet_same
                    (v := ⟨e0.localState, .blocked (.futex a (c₂.mem a)), true⟩) hget0
                  have hee := listGet_unique hget hsame
                  subst hee
                  injection hblk with hrEq
                  exact ⟨a, c₂.mem a, body0, Eq.symm hrEq,
                    nat_beq_zero_false_implies_ne_zero hbeq,
                    hprog0, Or.inr ⟨checkPc, acqPc, hinstr⟩⟩
                | inr hne =>
                  rw [listSet_other hne] at hget
                  exact ih t e r hget hblk
          | futexRetryAcquire a waitPc acqPc =>
            rw [hinstr] at hwf0
            dsimp at hwf0
            rw [eval_futexRetryAcquire]
            cases hbeq : Nat.beq (c₂.mem a) 0 with
            | true =>
              dsimp
              intro t e r hget hblk
              cases Decidable.em (tid = t) with
              | inl heq =>
                subst heq
                have hsame := listSet_same
                  (v := ⟨⟨acqPc, e0.localState.reg⟩, .enabled, false⟩) hget0
                have hee := listGet_unique hget hsame
                subst hee; nomatch hblk
              | inr hne =>
                rw [listSet_other hne] at hget
                cases ih t e r hget hblk with
                | intro addr hr1 =>
                  cases hr1 with
                  | intro exp hr2 =>
                    cases hr2 with
                    | intro bd hbd =>
                      exact ⟨addr, exp, bd, hbd.1,
                        memWrite_nonzero_preserves_nonzero c₂.mem a addr hbd.2.1,
                        hbd.2.2⟩
            | false =>
              dsimp
              intro t e r hget hblk
              cases Decidable.em (tid = t) with
              | inl heq =>
                subst heq
                have hsame := listSet_same
                  (v := ⟨⟨waitPc, e0.localState.reg⟩, .blocked (.futex a (c₂.mem a)), true⟩) hget0
                have hee := listGet_unique hget hsame
                subst hee
                injection hblk with hrEq
                exact ⟨a, c₂.mem a, body0, Eq.symm hrEq,
                  nat_beq_zero_false_implies_ne_zero hbeq,
                  hprog0, Or.inr ⟨e0.localState.pc, acqPc, hwf0⟩⟩
              | inr hne =>
                rw [listSet_other hne] at hget
                exact ih t e r hget hblk
          | futexUnlock a npc =>
            rw [eval_futexUnlock]
            intro t e r hget hblk
            dsimp at hget
            cases Decidable.em (tid = t) with
            | inl heq =>
              subst heq
              have hwakeGet : ∃ ew, listGet? (wakeFutexAll a c₂.threads) tid = some ew := by
                have hlen : ∀ (es : List (ThreadEntry RegState)) (k : Nat) (ex : ThreadEntry RegState),
                    listGet? es k = some ex → ∃ ew, listGet? (wakeFutexAll a es) k = some ew := by
                  intro es
                  induction es with
                  | nil => intro _ _ h; nomatch h
                  | cons hd tl ihtl =>
                    intro k ex hk
                    rw [wakeFutexAll_cons]
                    cases k with
                    | zero => exact ⟨_, listGet_zero _ _⟩
                    | succ k' => exact ihtl k' ex hk
                exact hlen c₂.threads tid e0 hget0
              cases hwakeGet with
              | intro ew hew =>
                have hsame := listSet_same (v := ⟨⟨npc, e0.localState.reg⟩, .enabled, false⟩) hew
                have hee := listGet_unique hget hsame
                subst hee; nomatch hblk
            | inr hne =>
              rw [listSet_other hne] at hget
              have hpre := wakeFutexAll_get_blocked hget hblk
              cases ih t e r hpre.1 hblk with
              | intro addr hr1 =>
                cases hr1 with
                | intro exp hr2 =>
                  cases hr2 with
                  | intro bd hbd =>
                    have hneAddr : addr ≠ a := fun ha =>
                      hpre.2 exp (by rw [hbd.1, ha])
                    have hbeqFalse : Nat.beq addr a = false := by
                      cases hb : Nat.beq addr a with
                      | false => rfl
                      | true => exact False.elim (hneAddr (Nat.eq_of_beq_eq_true hb))
                    exact ⟨addr, exp, bd, hbd.1,
                      by dsimp; rw [memWrite_diff c₂.mem 0 hbeqFalse]; exact hbd.2.1,
                      hbd.2.2⟩

def ContendedFutexTrap (prog : ConcProg) (c : Config RegState) : Prop :=
  ∀ (t : ThreadId) (e : ThreadEntry RegState),
    listGet? c.threads t = some e →
    e.status = .terminated ∨
    (e.inWaitEpisode = true ∧
     e.status ≠ .terminated ∧
     ∃ body : Nat → ConcInstr,
       listGet? prog t = some body ∧
       ((∃ addr npc, body e.localState.pc = .futexLock addr npc ∧ c.mem addr ≠ 0) ∨
        (∃ addr checkPc acqPc,
          body e.localState.pc = .futexWaitEnter addr checkPc acqPc ∧ c.mem addr ≠ 0) ∨
        (∃ addr waitPc acqPc,
          body e.localState.pc = .futexRetryAcquire addr waitPc acqPc ∧ c.mem addr ≠ 0)))

theorem nat_beq_zero_of_ne_zero {x : Nat} (h : x ≠ 0) : Nat.beq x 0 = false := by
  cases x with
  | zero => exact False.elim (h rfl)
  | succ _ => rfl

/-- General non-circular spurious-wakeup closure theorem: EVERY
`WellFormedFutexProg` satisfies `SpuriousWakeNonRescuing` under
`mkSpuriousProgSystem`, WITHOUT assuming whether the program is deadlock-free
or deadlocks! -/
theorem wellFormedFutexProg_spuriousWakeNonRescuing {prog : ConcProg}
    (hwf : WellFormedFutexProg prog) :
    SpuriousWakeNonRescuing (mkSpuriousProgSystem prog) := by
  refine ⟨ContendedFutexTrap prog, ?_, ?_⟩
  · intro cfg hr hgdl t e hget
    cases hst : e.status with
    | terminated => exact Or.inl rfl
    | enabled => exact False.elim (hgdl.2.1 t ⟨e, hget, hst⟩)
    | blocked r =>
      have hnt : ¬ IsTerminated cfg t := by
        intro ht
        cases ht with
        | intro e' he' =>
          have hee := listGet_unique hget he'.1
          subst hee; rw [hst] at he'; nomatch he'.2
      have hwait : InWaitEpisode cfg t := by
        cases hgdl.2.2 t ⟨e, hget⟩ with
        | inl hw => exact hw
        | inr ht => exact False.elim (hnt ht)
      cases hwait with
      | intro e' he' =>
        have hee := listGet_unique hget he'.1
        subst hee
        cases wellFormedFutex_preserves_blockedContended hwf hr t e r hget hst with
        | intro addr hr1 =>
          cases hr1 with
          | intro exp hr2 =>
            cases hr2 with
            | intro body hbd =>
              refine Or.inr ⟨he'.2.1, (by intro h; nomatch h), body, hbd.2.2.1, ?_⟩
              cases hbd.2.2.2 with
              | inl hfl =>
                cases hfl with | intro npc hn => exact Or.inl ⟨addr, npc, hn, hbd.2.1⟩
              | inr hfw =>
                cases hfw with
                | intro cp hr3 =>
                  cases hr3 with
                  | intro ap ha => exact Or.inr (Or.inl ⟨addr, cp, ap, ha, hbd.2.1⟩)
  · intro tid c₁ c₂ htrap hstep
    cases hstep with
    | inr hw =>
      cases hw with
      | intro st h1 =>
        cases h1 with
        | intro addr h2 =>
          cases h2 with
          | intro exp hwk =>
            rw [hwk.2]
            refine ⟨?_, ?_⟩
            · intro t e hget
              dsimp at hget
              cases Decidable.em (tid = t) with
              | inl heq =>
                subst heq
                have hsame := listSet_same (v := ⟨st, .enabled, true⟩) hwk.1
                have hee := listGet_unique hget hsame
                subst hee
                cases htrap tid ⟨st, .blocked (.futex addr exp), true⟩ hwk.1 with
                | inl hterm => nomatch hterm
                | inr hok =>
                  refine Or.inr ⟨rfl, (by dsimp; intro h; nomatch h), ?_⟩
                  dsimp
                  exact hok.2.2
              | inr hne =>
                rw [listSet_other hne] at hget
                exact htrap t e hget
            · intro u hu
              cases hu with
              | intro eu heu =>
                cases Decidable.em (tid = u) with
                | inl heq =>
                  subst heq
                  exact ⟨⟨st, .enabled, true⟩,
                    by dsimp; exact listSet_same hwk.1, rfl, fun h => nomatch h⟩
                | inr hne =>
                  exact ⟨eu, by dsimp; rw [listSet_other hne]; exact heu.1, heu.2⟩
    | inl hp =>
      cases hp with
      | intro e0 hrest =>
        cases hrest with
        | intro body0 hb =>
          have hget0 := hb.1
          have hen0 := hb.2.1
          have hprog0 := hb.2.2.1
          have hc2 := hb.2.2.2
          subst hc2
          cases htrap tid e0 hget0 with
          | inl hterm => rw [hen0] at hterm; nomatch hterm
          | inr hok0 =>
            have hiw0 := hok0.1
            cases hok0.2.2 with
            | intro body1 hbd1 =>
              have hsameBody := listGet_unique hprog0 hbd1.1
              subst hsameBody
              cases hbd1.2 with
              | inl hfl =>
                cases hfl with
                | intro addr hr1 =>
                  cases hr1 with
                  | intro npc hflEq =>
                    rw [hflEq.1, eval_futexLock, nat_beq_zero_of_ne_zero hflEq.2]
                    dsimp
                    refine ⟨?_, ?_⟩
                    · intro t e hget
                      cases Decidable.em (tid = t) with
                      | inl heq =>
                        subst heq
                        have hsame := listSet_same
                          (v := ⟨e0.localState, .blocked (.futex addr (c₁.mem addr)), true⟩) hget0
                        have hee := listGet_unique hget hsame
                        subst hee
                        refine Or.inr ⟨rfl, (by dsimp; intro h; nomatch h), ?_⟩
                        dsimp
                        exact ⟨body0, hprog0, Or.inl ⟨addr, npc, hflEq⟩⟩
                      | inr hne =>
                        rw [listSet_other hne] at hget
                        exact htrap t e hget
                    · intro u hu
                      cases hu with
                      | intro eu heu =>
                        cases Decidable.em (tid = u) with
                        | inl heq =>
                          subst heq
                          exact ⟨⟨e0.localState, .blocked (.futex addr (c₁.mem addr)), true⟩,
                            listSet_same hget0, rfl, fun h => nomatch h⟩
                        | inr hne =>
                          exact ⟨eu, by rw [listSet_other hne]; exact heu.1, heu.2⟩
              | inr hrestCases =>
                cases hrestCases with
                | inl hfw =>
                  cases hfw with
                  | intro addr hr1 =>
                    cases hr1 with
                    | intro checkPc hr2 =>
                      cases hr2 with
                      | intro acqPc hfwEq =>
                        have hwfPair := hwf tid body0 hprog0 e0.localState.pc
                        unfold IsWellFormedFutexInstr at hwfPair
                        rw [hfwEq.1] at hwfPair
                        dsimp at hwfPair
                        rw [hfwEq.1, eval_futexWaitEnter, hiw0]
                        dsimp
                        refine ⟨?_, ?_⟩
                        · intro t e hget
                          cases Decidable.em (tid = t) with
                          | inl heq =>
                            subst heq
                            have hsame := listSet_same
                              (v := ⟨⟨checkPc, e0.localState.reg + 1⟩, .enabled, true⟩) hget0
                            have hee := listGet_unique hget hsame
                            subst hee
                            refine Or.inr ⟨rfl, (by dsimp; intro h; nomatch h), ?_⟩
                            dsimp
                            exact ⟨body0, hprog0,
                              Or.inr (Or.inr ⟨addr, e0.localState.pc, acqPc, hwfPair, hfwEq.2⟩)⟩
                          | inr hne =>
                            rw [listSet_other hne] at hget
                            exact htrap t e hget
                        · intro u hu
                          cases hu with
                          | intro eu heu =>
                            cases Decidable.em (tid = u) with
                            | inl heq =>
                              subst heq
                              exact ⟨⟨⟨checkPc, e0.localState.reg + 1⟩, .enabled, true⟩,
                                listSet_same hget0, rfl, fun h => nomatch h⟩
                            | inr hne =>
                              exact ⟨eu, by rw [listSet_other hne]; exact heu.1, heu.2⟩
                | inr hfr =>
                  cases hfr with
                  | intro addr hr1 =>
                    cases hr1 with
                    | intro waitPc hr2 =>
                      cases hr2 with
                      | intro acqPc hfrEq =>
                        have hwfPair := hwf tid body0 hprog0 e0.localState.pc
                        unfold IsWellFormedFutexInstr at hwfPair
                        rw [hfrEq.1] at hwfPair
                        dsimp at hwfPair
                        rw [hfrEq.1, eval_futexRetryAcquire, nat_beq_zero_of_ne_zero hfrEq.2]
                        dsimp
                        refine ⟨?_, ?_⟩
                        · intro t e hget
                          cases Decidable.em (tid = t) with
                          | inl heq =>
                            subst heq
                            have hsame := listSet_same
                              (v := ⟨⟨waitPc, e0.localState.reg⟩, .blocked (.futex addr (c₁.mem addr)), true⟩) hget0
                            have hee := listGet_unique hget hsame
                            subst hee
                            refine Or.inr ⟨rfl, (by dsimp; intro h; nomatch h), ?_⟩
                            dsimp
                            exact ⟨body0, hprog0,
                              Or.inr (Or.inl ⟨addr, e0.localState.pc, acqPc, hwfPair, hfrEq.2⟩)⟩
                          | inr hne =>
                            rw [listSet_other hne] at hget
                            exact htrap t e hget
                        · intro u hu
                          cases hu with
                          | intro eu heu =>
                            cases Decidable.em (tid = u) with
                            | inl heq =>
                              subst heq
                              exact ⟨⟨⟨waitPc, e0.localState.reg⟩, .blocked (.futex addr (c₁.mem addr)), true⟩,
                                listSet_same hget0, rfl, fun h => nomatch h⟩
                            | inr hne =>
                              exact ⟨eu, by rw [listSet_other hne]; exact heu.1, heu.2⟩

/-! ### SpinLock & Contended Fairness Separation -/

def spinOnceBody : Nat → ConcInstr
  | 0 => .casLoop 0 0 1 1
  | 1 => .store 0 0 2
  | _ => .halt

def SpinOnceProg : ConcProg := [spinOnceBody, spinOnceBody]
noncomputable def SpinOnceSys : ConcSystem RegState := mkProgSystem SpinOnceProg
noncomputable def SpinOnceSpuriousSys : ConcSystem RegState := mkSpuriousProgSystem SpinOnceProg

theorem spinOnce_isSpinOnly : IsSpinOnlyProg SpinOnceProg := by
  intro t body hget pc
  cases t with
  | zero =>
    injection hget with hb; subst hb
    cases pc with | zero => exact True.intro | succ k => cases k <;> exact True.intro
  | succ t1 =>
    cases t1 with
    | zero =>
      injection hget with hb; subst hb
      cases pc with | zero => exact True.intro | succ k => cases k <;> exact True.intro
    | succ _ => nomatch hget

theorem spinOnce_subsystemDeadlockFreeWaitEpisode :
    SubsystemDeadlockFreeWaitEpisode SpinOnceSys ∧
    SubsystemDeadlockFreeWaitEpisode SpinOnceSpuriousSys :=
  spinOnly_subsystemDeadlockFreeWaitEpisode spinOnce_isSpinOnly

theorem spinOnce_globalDeadlockFree : GlobalDeadlockFree SpinOnceSys :=
  spinOnlyProg_globalDeadlockFree spinOnce_isSpinOnly

/-- Direct non-vacuous instantiation of
`subsystemDeadlockFreeWaitEpisode_implies_globalDeadlockFree` on a
`mkSpuriousProgSystem` (`SpinOnceSpuriousSys`) WITH `OsSpuriousFutexWake`. -/
theorem spinOnce_spurious_globalDeadlockFree :
    GlobalDeadlockFree SpinOnceSpuriousSys :=
  subsystemDeadlockFreeWaitEpisode_implies_globalDeadlockFree
    (spinOnly_spurious_nonRescuing spinOnce_isSpinOnly)
    spinOnce_subsystemDeadlockFreeWaitEpisode.2

def spinOnceLockedCfg : Config RegState :=
  { threads := [⟨⟨1, 0⟩, .enabled, false⟩, ⟨⟨0, 0⟩, .enabled, false⟩]
    mem := memWrite (fun _ => 0) 0 1
    parkToken := fun _ => false }

noncomputable def unfairSpinRun : Run RegState :=
  { trace := fun n => match n with | 0 => SpinOnceSys.init | _ + 1 => spinOnceLockedCfg
    stepAt := fun n => match n with | 0 => some 0 | _ + 1 => some 1 }

theorem spinOnce_not_unconditionalTerminates :
    ¬ UnconditionalTerminates SpinOnceSys := by
  intro hterm
  have hv : ValidRun SpinOnceSys unfairSpinRun := by
    refine ⟨rfl, ?_⟩
    intro n
    cases n with
    | zero => exact Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, spinOnceBody, rfl, rfl, rfl, rfl⟩
    | succ _ => exact Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, spinOnceBody, rfl, rfl, rfl, rfl⟩
  cases hterm unfairSpinRun hv with
  | intro n hall =>
    dsimp at hall
    cases n with
    | zero => nomatch (hall 0 ⟨⟨0, 0⟩, .enabled, false⟩ rfl)
    | succ _ => nomatch (hall 0 ⟨⟨1, 0⟩, .enabled, false⟩ rfl)

def spinReacquirerBody : Nat → ConcInstr
  | 0 => .casLoop 0 0 1 1
  | _ => .store 0 0 0

def SpinContendedProg : ConcProg := [spinOnceBody, spinReacquirerBody]
noncomputable def SpinContendedSys : ConcSystem RegState := mkProgSystem SpinContendedProg

theorem spinContended_isSpinOnly : IsSpinOnlyProg SpinContendedProg := by
  intro t body hget pc
  cases t with
  | zero =>
    injection hget with hb; subst hb
    cases pc with | zero => exact True.intro | succ k => cases k <;> exact True.intro
  | succ t1 =>
    cases t1 with
    | zero =>
      injection hget with hb; subst hb; cases pc <;> exact True.intro
    | succ _ => nomatch hget

theorem spinContended_globalDeadlockFree : GlobalDeadlockFree SpinContendedSys :=
  spinOnlyProg_globalDeadlockFree spinContended_isSpinOnly

def contendedHeldByT1 : Config RegState :=
  { threads := [⟨⟨0, 0⟩, .enabled, false⟩, ⟨⟨1, 0⟩, .enabled, false⟩]
    mem := memWrite (fun _ => 0) 0 1
    parkToken := fun _ => false }

theorem memWrite_zero_cancel :
    memWrite (memWrite (fun _ => 0) 0 1) 0 0 = (fun _ => 0) := by
  funext x
  rw [memWrite_eq, memWrite_eq]
  cases Nat.beq x 0 <;> rfl

inductive Phase3 where
  | p0 | p1 | p2

def phase3Next : Phase3 → Phase3
  | .p0 => .p1
  | .p1 => .p2
  | .p2 => .p0

noncomputable def phase3 : Nat → Phase3
  | 0 => .p0
  | n + 1 => phase3Next (phase3 n)

theorem phase3_mul3 (k : Nat) : phase3 (3 * k) = .p0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    have h : 3 * (m + 1) = 3 * m + 3 := rfl
    rw [h]
    dsimp [phase3]
    rw [ih]
    rfl

theorem phase3_mul3_add1 (k : Nat) : phase3 (3 * k + 1) = .p1 := by
  dsimp [phase3]
  rw [phase3_mul3 k]
  rfl

theorem le_mul3 (N : Nat) : N ≤ 3 * N := by
  have h1 : 1 * N ≤ 3 * N := Nat.mul_le_mul_right N (by decide)
  rw [Nat.one_mul] at h1
  exact h1

theorem le_mul3_add1 (N : Nat) : N ≤ 3 * N + 1 :=
  Nat.le_trans (le_mul3 N) (Nat.le_succ (3 * N))

noncomputable def contendedStarveTrace (n : Nat) : Config RegState :=
  match phase3 n with
  | .p0 => SpinContendedSys.init
  | .p1 => contendedHeldByT1
  | .p2 => contendedHeldByT1

noncomputable def contendedStarveStep (n : Nat) : Option ThreadId :=
  match phase3 n with
  | .p0 => some 1
  | .p1 => some 0
  | .p2 => some 1

noncomputable def contendedStarveRun : Run RegState :=
  { trace := contendedStarveTrace, stepAt := contendedStarveStep }

def LockAvailable (cfg : Config RegState) (t : ThreadId) : Prop :=
  IsEnabled cfg t ∧ cfg.mem 0 = 0

def LockAcquired (c₁ c₂ : Config RegState) (t : ThreadId) : Prop :=
  c₁.mem 0 = 0 ∧ c₂.mem 0 = 1 ∧ IsEnabled c₁ t

theorem contendedStarveRun_valid : ValidRun SpinContendedSys contendedStarveRun := by
  refine ⟨rfl, ?_⟩
  intro n
  dsimp [contendedStarveRun, contendedStarveTrace, contendedStarveStep, phase3]
  cases hp : phase3 n with
  | p0 =>
    dsimp [phase3Next]
    exact Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, spinReacquirerBody, rfl, rfl, rfl, rfl⟩
  | p1 =>
    dsimp [phase3Next]
    exact Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, spinOnceBody, rfl, rfl, rfl, rfl⟩
  | p2 =>
    dsimp [phase3Next]
    refine Or.inl ⟨⟨⟨1, 0⟩, .enabled, false⟩, spinReacquirerBody, rfl, rfl, rfl, ?_⟩
    change SpinContendedSys.init =
      { threads := [⟨⟨0, 0⟩, .enabled, false⟩, ⟨⟨0, 0⟩, .enabled, false⟩]
        mem := memWrite (memWrite (fun _ => 0) 0 1) 0 0
        parkToken := fun _ => false }
    rw [memWrite_zero_cancel]
    rfl

theorem not_enabled_oob_contended (n : Nat) (t2 : Nat) :
    ¬ IsEnabled (contendedStarveRun.trace n) (t2 + 2) := by
  intro hen
  cases hen with
  | intro e he =>
    have hget := he.1
    dsimp [contendedStarveRun, contendedStarveTrace] at hget
    cases hp : phase3 n <;> rw [hp] at hget
    · nomatch hget
    · nomatch hget
    · nomatch hget

theorem contendedStarveRun_strongFair_and_actionWeakFair_yet_starves :
    StrongFair contendedStarveRun ∧
    WeakFair contendedStarveRun ∧
    ActionWeakFair LockAvailable LockAcquired contendedStarveRun ∧
    ¬ ActionStrongFair LockAvailable LockAcquired contendedStarveRun ∧
    (∀ n : Nat, ¬ IsTerminated (contendedStarveRun.trace n) 0) := by
  have hsf : StrongFair contendedStarveRun := by
    intro t hio
    cases t with
    | zero =>
      intro N
      refine ⟨3 * N + 1, le_mul3_add1 N, ?_⟩
      dsimp [contendedStarveRun, contendedStarveStep]
      rw [phase3_mul3_add1 N]
    | succ t1 =>
      cases t1 with
      | zero =>
        intro N
        refine ⟨3 * N, le_mul3 N, ?_⟩
        dsimp [contendedStarveRun, contendedStarveStep]
        rw [phase3_mul3 N]
      | succ t2 =>
        cases hio 0 with
        | intro n hn =>
          exact False.elim (not_enabled_oob_contended n t2 hn.2)
  have hawf : ActionWeakFair LockAvailable LockAcquired contendedStarveRun := by
    intro t hea
    cases t with
    | zero =>
      cases hea with
      | intro N₀ hN₀ =>
        have hav := (hN₀ (3 * N₀ + 1) (le_mul3_add1 N₀)).2
        dsimp [contendedStarveRun, contendedStarveTrace] at hav
        rw [phase3_mul3_add1 N₀] at hav
        nomatch hav
    | succ t1 =>
      cases t1 with
      | zero =>
        intro N
        refine ⟨3 * N, le_mul3 N, ?_⟩
        dsimp [contendedStarveRun, contendedStarveStep, contendedStarveTrace, phase3]
        rw [phase3_mul3 N]
        exact ⟨rfl, rfl, rfl, ⟨⟨0, 0⟩, .enabled, false⟩, rfl, rfl⟩
      | succ t2 =>
        cases hea with
        | intro N₀ hN₀ =>
          have hav := (hN₀ (3 * N₀) (le_mul3 N₀)).1
          exact False.elim (not_enabled_oob_contended (3 * N₀) t2 hav)
  have hnasf : ¬ ActionStrongFair LockAvailable LockAcquired contendedStarveRun := by
    intro hasf
    have hio0 : InfinitelyOften (fun n => LockAvailable (contendedStarveRun.trace n) 0) := by
      intro N
      refine ⟨3 * N, le_mul3 N, ?_⟩
      dsimp [contendedStarveRun, contendedStarveTrace, LockAvailable]
      rw [phase3_mul3 N]
      exact ⟨⟨⟨⟨0, 0⟩, .enabled, false⟩, rfl, rfl⟩, rfl⟩
    cases hasf 0 hio0 0 with
    | intro n hn =>
      have hstep0 := hn.2.1
      have hacq0 := hn.2.2.1
      dsimp [contendedStarveRun, contendedStarveStep, contendedStarveTrace] at hstep0 hacq0
      cases hp : phase3 n <;> rw [hp] at hstep0 hacq0
      · nomatch hstep0
      · nomatch hacq0
      · nomatch hstep0
  have hnoterm : ∀ n : Nat, ¬ IsTerminated (contendedStarveRun.trace n) 0 := by
    intro n ht
    cases ht with
    | intro e he =>
      have hget := he.1
      have hst := he.2
      dsimp [contendedStarveRun, contendedStarveTrace] at hget
      cases hp : phase3 n <;> rw [hp] at hget
      · injection hget with heq; subst heq; nomatch hst
      · injection hget with heq; subst heq; nomatch hst
      · injection hget with heq; subst heq; nomatch hst
  exact ⟨hsf, strongFair_implies_weakFair hsf, hawf, hnasf, hnoterm⟩

/-! ### Quantified Per-Thread Positive Liveness 1: `WeakFair ∧ ActionStrongFair` on `SpinContendedSys` -/

def scInit (c : Config RegState) : Prop :=
  c.threads = [⟨⟨0, 0⟩, .enabled, false⟩, ⟨⟨0, 0⟩, .enabled, false⟩] ∧ c.mem 0 = 0

def scT1Held (c : Config RegState) : Prop :=
  c.threads = [⟨⟨0, 0⟩, .enabled, false⟩, ⟨⟨1, 0⟩, .enabled, false⟩] ∧ c.mem 0 = 1

def scT0Held (c : Config RegState) : Prop :=
  c.threads = [⟨⟨1, 0⟩, .enabled, false⟩, ⟨⟨0, 0⟩, .enabled, false⟩] ∧ c.mem 0 = 1

def scT0Unlocked (c : Config RegState) : Prop :=
  ∃ pc1 : Nat, (pc1 = 0 ∨ pc1 = 1) ∧
    c.threads = [⟨⟨2, 0⟩, .enabled, false⟩, ⟨⟨pc1, 0⟩, .enabled, false⟩]

def scPhase (c : Config RegState) : Prop :=
  scInit c ∨ scT1Held c ∨ scT0Held c ∨ scT0Unlocked c ∨ IsTerminated c 0

theorem sc_step_closed {tid : ThreadId} {c c' : Config RegState}
    (hp : scPhase c) (hstep : ProgStepBy SpinContendedProg tid c c') :
    scPhase c' := by
  cases hstep with
  | intro e hrest =>
    cases hrest with
    | intro body hb =>
      have hget := hb.1
      have hen := hb.2.1
      have hprog := hb.2.2.1
      have hc' := hb.2.2.2
      subst hc'
      cases hp with
      | inl hinit =>
        rw [hinit.1] at hget
        cases tid with
        | zero =>
          injection hget with he; subst he
          injection hprog with hbd; subst hbd
          refine Or.inr (Or.inr (Or.inl ?_))
          change scT0Held (evalInstr 0 ⟨0, 0⟩ false (.casLoop 0 0 1 1) c)
          rw [eval_casLoop, hinit.2]
          exact ⟨by dsimp; rw [hinit.1]; rfl, memWrite_same c.mem 0 1⟩
        | succ t1 =>
          cases t1 with
          | zero =>
            injection hget with he; subst he
            injection hprog with hbd; subst hbd
            refine Or.inr (Or.inl ?_)
            change scT1Held (evalInstr 1 ⟨0, 0⟩ false (.casLoop 0 0 1 1) c)
            rw [eval_casLoop, hinit.2]
            exact ⟨by dsimp; rw [hinit.1]; rfl, memWrite_same c.mem 0 1⟩
          | succ _ => nomatch hprog
      | inr hp2 =>
        cases hp2 with
        | inl ht1 =>
          rw [ht1.1] at hget
          cases tid with
          | zero =>
            injection hget with he; subst he
            injection hprog with hbd; subst hbd
            refine Or.inr (Or.inl ?_)
            change scT1Held (evalInstr 0 ⟨0, 0⟩ false (.casLoop 0 0 1 1) c)
            rw [eval_casLoop, ht1.2]
            exact ht1
          | succ t1 =>
            cases t1 with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              refine Or.inl ?_
              change scInit (evalInstr 1 ⟨1, 0⟩ false (.store 0 0 0) c)
              rw [eval_store]
              exact ⟨by dsimp; rw [ht1.1]; rfl, memWrite_same c.mem 0 0⟩
            | succ _ => nomatch hprog
        | inr hp3 =>
          cases hp3 with
          | inl ht0 =>
            rw [ht0.1] at hget
            cases tid with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
              change scT0Unlocked (evalInstr 0 ⟨1, 0⟩ false (.store 0 0 2) c)
              rw [eval_store]
              exact ⟨0, Or.inl rfl, by dsimp; rw [ht0.1]; rfl⟩
            | succ t1 =>
              cases t1 with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                refine Or.inr (Or.inr (Or.inl ?_))
                change scT0Held (evalInstr 1 ⟨0, 0⟩ false (.casLoop 0 0 1 1) c)
                rw [eval_casLoop, ht0.2]
                exact ht0
              | succ _ => nomatch hprog
          | inr hp4 =>
            cases hp4 with
            | inl hunl =>
              cases hunl with
              | intro pc1 hpc1 =>
                rw [hpc1.2] at hget
                cases tid with
                | zero =>
                  injection hget with he; subst he
                  injection hprog with hbd; subst hbd
                  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
                  change IsTerminated (evalInstr 0 ⟨2, 0⟩ false .halt c) 0
                  rw [eval_halt]
                  exact ⟨⟨⟨2, 0⟩, .terminated, false⟩, by dsimp; rw [hpc1.2]; rfl, rfl⟩
                | succ t1 =>
                  cases t1 with
                  | zero =>
                    injection hget with he; subst he
                    injection hprog with hbd; subst hbd
                    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
                    cases hpc1.1 with
                    | inl hp0 =>
                      subst hp0
                      change scT0Unlocked (evalInstr 1 ⟨0, 0⟩ false (.casLoop 0 0 1 1) c)
                      rw [eval_casLoop]
                      cases hb0 : Nat.beq (c.mem 0) 0 with
                      | false => exact ⟨0, Or.inl rfl, hpc1.2⟩
                      | true => exact ⟨1, Or.inr rfl, by dsimp; rw [hpc1.2]; rfl⟩
                    | inr hp1 =>
                      subst hp1
                      change scT0Unlocked (evalInstr 1 ⟨1, 0⟩ false (.store 0 0 0) c)
                      rw [eval_store]
                      exact ⟨0, Or.inl rfl, by dsimp; rw [hpc1.2]; rfl⟩
                  | succ _ => nomatch hprog
            | inr hdone =>
              refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
              cases tid with
              | zero =>
                cases hdone with
                | intro e0 he0 =>
                  have heq := listGet_unique hget he0.1
                  subst heq
                  rw [hen] at he0
                  nomatch he0.2
              | succ t1 =>
                cases t1 with
                | zero =>
                  injection hprog with hbd; subst hbd
                  cases hdone with
                  | intro e0 he0 =>
                    cases hpce : e.localState.pc with
                    | zero =>
                      change IsTerminated (evalInstr 1 e.localState e.inWaitEpisode (.casLoop 0 0 1 1) c) 0
                      rw [eval_casLoop]
                      cases Nat.beq (c.mem 0) 0 with
                      | false => exact ⟨e0, he0⟩
                      | true =>
                        dsimp
                        cases hct : c.threads with
                        | nil => rw [hct] at he0; nomatch he0.1
                        | cons hd tl =>
                          rw [hct] at he0
                          injection he0.1 with hhd; subst hhd
                          exact ⟨hd, rfl, he0.2⟩
                    | succ _ =>
                      change IsTerminated (evalInstr 1 e.localState e.inWaitEpisode (.store 0 0 0) c) 0
                      rw [eval_store]
                      cases hct : c.threads with
                      | nil => rw [hct] at he0; nomatch he0.1
                      | cons hd tl =>
                        rw [hct] at he0
                        injection he0.1 with hhd; subst hhd
                        exact ⟨hd, rfl, he0.2⟩
                | succ _ => nomatch hprog

theorem sc_run_invariant {run : Run RegState}
    (hv : ValidRun SpinContendedSys run) (n : Nat) :
    scPhase (run.trace n) := by
  induction n with
  | zero =>
    rw [hv.1]
    exact Or.inl ⟨rfl, rfl⟩
  | succ k ih =>
    have hstep := hv.2 k
    cases hs : run.stepAt k with
    | some tid =>
      rw [hs] at hstep
      cases hstep with
      | inl hp => exact sc_step_closed ih hp
      | inr hw => exact False.elim hw
    | none =>
      rw [hs] at hstep
      rw [hstep.2.2]
      exact ih

theorem sc_unlocked_mono {run : Run RegState}
    (hv : ValidRun SpinContendedSys run)
    (hnt : ∀ m : Nat, ¬ IsTerminated (run.trace m) 0)
    {n : Nat} (hunl : scT0Unlocked (run.trace n)) :
    ∀ d : Nat, scT0Unlocked (run.trace (n + d)) := by
  intro d
  induction d with
  | zero => exact hunl
  | succ k ih =>
    have hstep := hv.2 (n + k)
    cases hs : run.stepAt (n + k) with
    | none =>
      rw [hs] at hstep
      rw [Nat.add_succ, hstep.2.2]
      exact ih
    | some tid =>
      rw [hs] at hstep
      cases hstep with
      | inr hw => exact False.elim hw
      | inl hp =>
        cases ih with
        | intro pc1 hpc1 =>
          cases hp with
          | intro e hrest =>
            cases hrest with
            | intro body hb =>
              have hget := hb.1
              have hprog := hb.2.2.1
              have hc' := hb.2.2.2
              rw [Nat.add_succ, hc']
              rw [hpc1.2] at hget
              cases tid with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                have hterm : IsTerminated (evalInstr 0 ⟨2, 0⟩ false .halt (run.trace (n + k))) 0 := by
                  rw [eval_halt]
                  exact ⟨⟨⟨2, 0⟩, .terminated, false⟩, by dsimp; rw [hpc1.2]; rfl, rfl⟩
                change IsTerminated (evalInstr 0 ⟨2, 0⟩ false (spinOnceBody 2) (run.trace (n + k))) 0 at hterm
                rw [← hc'] at hterm
                exact False.elim (hnt (n + k + 1) hterm)
              | succ t1 =>
                cases t1 with
                | zero =>
                  injection hget with he; subst he
                  injection hprog with hbd; subst hbd
                  cases hpc1.1 with
                  | inl hp0 =>
                    subst hp0
                    change scT0Unlocked (evalInstr 1 ⟨0, 0⟩ false (.casLoop 0 0 1 1) (run.trace (n + k)))
                    rw [eval_casLoop]
                    cases Nat.beq ((run.trace (n + k)).mem 0) 0 with
                    | false => exact ⟨0, Or.inl rfl, hpc1.2⟩
                    | true => exact ⟨1, Or.inr rfl, by dsimp; rw [hpc1.2]; rfl⟩
                  | inr hp1 =>
                    subst hp1
                    change scT0Unlocked (evalInstr 1 ⟨1, 0⟩ false (.store 0 0 0) (run.trace (n + k)))
                    rw [eval_store]
                    exact ⟨0, Or.inl rfl, by dsimp; rw [hpc1.2]; rfl⟩
                | succ _ => nomatch hprog

theorem sc_held0_mono {run : Run RegState}
    (hv : ValidRun SpinContendedSys run)
    (hnunl : ∀ m : Nat, ¬ scT0Unlocked (run.trace m))
    {n : Nat} (hh0 : scT0Held (run.trace n)) :
    ∀ d : Nat, scT0Held (run.trace (n + d)) := by
  intro d
  induction d with
  | zero => exact hh0
  | succ k ih =>
    have hstep := hv.2 (n + k)
    cases hs : run.stepAt (n + k) with
    | none =>
      rw [hs] at hstep
      rw [Nat.add_succ, hstep.2.2]
      exact ih
    | some tid =>
      rw [hs] at hstep
      cases hstep with
      | inr hw => exact False.elim hw
      | inl hp =>
        cases hp with
        | intro e hrest =>
          cases hrest with
          | intro body hb =>
            have hget := hb.1
            have hprog := hb.2.2.1
            have hc' := hb.2.2.2
            rw [Nat.add_succ, hc']
            rw [ih.1] at hget
            cases tid with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              have hunl : scT0Unlocked (evalInstr 0 ⟨1, 0⟩ false (.store 0 0 2) (run.trace (n + k))) := by
                rw [eval_store]
                exact ⟨0, Or.inl rfl, by dsimp; rw [ih.1]; rfl⟩
              change scT0Unlocked (evalInstr 0 ⟨1, 0⟩ false (spinOnceBody 1) (run.trace (n + k))) at hunl
              rw [← hc'] at hunl
              exact False.elim (hnunl (n + k + 1) hunl)
            | succ t1 =>
              cases t1 with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                change scT0Held (evalInstr 1 ⟨0, 0⟩ false (.casLoop 0 0 1 1) (run.trace (n + k)))
                rw [eval_casLoop, ih.2]
                exact ih
              | succ _ => nomatch hprog

theorem spinContended_weakFair_and_actionStrongFair_no_starvation :
    PerThreadStarvationFree
      (fun run => WeakFair run ∧ ActionStrongFair LockAvailable LockAcquired run)
      SpinContendedSys 0 IsTerminated := by
  intro run hv hfair
  have hwf := hfair.1
  have hasf := hfair.2
  cases cs_em (Eventually (fun n => IsTerminated (run.trace n) 0)) with
  | inl h => exact h
  | inr hnev =>
    have hnt : ∀ n : Nat, ¬ IsTerminated (run.trace n) 0 :=
      fun n ht => hnev ⟨n, ht⟩
    have hboth : ∀ n : Nat, IsEnabled (run.trace n) 0 ∧ IsEnabled (run.trace n) 1 := by
      intro n
      cases sc_run_invariant hv n with
      | inl h0 => exact enabled_pair h0.1
      | inr r1 =>
        cases r1 with
        | inl h1 => exact enabled_pair h1.1
        | inr r2 =>
          cases r2 with
          | inl h2 => exact enabled_pair h2.1
          | inr r3 =>
            cases r3 with
            | inl h3 =>
              cases h3 with
              | intro pc1 hp => exact enabled_pair hp.2
            | inr hd => exact False.elim (hnt n hd)
    have hio0 := hwf 0 ⟨0, fun n _ => (hboth n).1⟩
    have hio1 := hwf 1 ⟨0, fun n _ => (hboth n).2⟩
    have hnunl : ∀ n : Nat, ¬ scT0Unlocked (run.trace n) := by
      intro n hunl
      cases hio0 n with
      | intro m hm =>
        have hd : ∃ d, m = n + d := ⟨m - n, Eq.symm (Nat.add_sub_of_le hm.1)⟩
        cases hd with
        | intro d heqm =>
          have hunlm : scT0Unlocked (run.trace m) := by
            rw [heqm]; exact sc_unlocked_mono hv hnt hunl d
          have hstep := hv.2 m
          rw [hm.2] at hstep
          cases hstep with
          | inr hw => exact False.elim hw
          | inl hp =>
            cases hunlm with
            | intro pc1 hpc1 =>
              cases hp with
              | intro e hrest =>
                cases hrest with
                | intro body hb =>
                  have hget := hb.1
                  rw [hpc1.2] at hget
                  injection hget with he; subst he
                  injection hb.2.2.1 with hbd; subst hbd
                  have hterm : IsTerminated (run.trace (m + 1)) 0 := by
                    rw [hb.2.2.2]
                    change IsTerminated (evalInstr 0 ⟨2, 0⟩ false .halt (run.trace m)) 0
                    rw [eval_halt]
                    exact ⟨⟨⟨2, 0⟩, .terminated, false⟩, by dsimp; rw [hpc1.2]; rfl, rfl⟩
                  exact hnt (m + 1) hterm
    have hnh0 : ∀ n : Nat, ¬ scT0Held (run.trace n) := by
      intro n hh0
      cases hio0 n with
      | intro m hm =>
        have hd : ∃ d, m = n + d := ⟨m - n, Eq.symm (Nat.add_sub_of_le hm.1)⟩
        cases hd with
        | intro d heqm =>
          have hh0m : scT0Held (run.trace m) := by
            rw [heqm]; exact sc_held0_mono hv hnunl hh0 d
          have hstep := hv.2 m
          rw [hm.2] at hstep
          cases hstep with
          | inr hw => exact False.elim hw
          | inl hp =>
            cases hp with
            | intro e hrest =>
              cases hrest with
              | intro body hb =>
                have hget := hb.1
                rw [hh0m.1] at hget
                injection hget with he; subst he
                injection hb.2.2.1 with hbd; subst hbd
                have hunl : scT0Unlocked (run.trace (m + 1)) := by
                  rw [hb.2.2.2]
                  change scT0Unlocked (evalInstr 0 ⟨1, 0⟩ false (.store 0 0 2) (run.trace m))
                  rw [eval_store]
                  exact ⟨0, Or.inl rfl, by dsimp; rw [hh0m.1]; rfl⟩
                exact hnunl (m + 1) hunl
    have htwo : ∀ n : Nat, scInit (run.trace n) ∨ scT1Held (run.trace n) := by
      intro n
      cases sc_run_invariant hv n with
      | inl h0 => exact Or.inl h0
      | inr r1 =>
        cases r1 with
        | inl h1 => exact Or.inr h1
        | inr r2 =>
          cases r2 with
          | inl h2 => exact False.elim (hnh0 n h2)
          | inr r3 =>
            cases r3 with
            | inl h3 => exact False.elim (hnunl n h3)
            | inr hd => exact False.elim (hnt n hd)
    have hioAvail : InfinitelyOften (fun n => LockAvailable (run.trace n) 0) := by
      intro N
      cases hio1 N with
      | intro m hm =>
        cases htwo m with
        | inl h0 =>
          exact ⟨m, hm.1, (enabled_pair h0.1).1, h0.2⟩
        | inr h1 =>
          refine ⟨m + 1, Nat.le_trans hm.1 (Nat.le_succ m), ?_⟩
          have hstep := hv.2 m
          rw [hm.2] at hstep
          cases hstep with
          | inr hw => exact False.elim hw
          | inl hp =>
            cases hp with
            | intro e hrest =>
              cases hrest with
              | intro body hb =>
                have hget := hb.1
                rw [h1.1] at hget
                injection hget with he; subst he
                injection hb.2.2.1 with hbd; subst hbd
                dsimp
                rw [hb.2.2.2]
                change LockAvailable (evalInstr 1 ⟨1, 0⟩ false (.store 0 0 0) (run.trace m)) 0
                rw [eval_store]
                refine ⟨?_, memWrite_same (run.trace m).mem 0 0⟩
                exact (enabled_pair (c := { run.trace m with
                  threads := listSet (run.trace m).threads 1 ⟨⟨0, 0⟩, .enabled, false⟩
                  mem := memWrite (run.trace m).mem 0 0 }) (by dsimp; rw [h1.1]; rfl)).1
    cases hasf 0 hioAvail 0 with
    | intro m hm =>
      have hstep0 := hm.2.1
      have hmem0 := hm.2.2.1
      cases htwo m with
      | inr h1 =>
        rw [h1.2] at hmem0
        nomatch hmem0
      | inl h0 =>
        have hstep := hv.2 m
        rw [hstep0] at hstep
        cases hstep with
        | inr hw => exact False.elim hw
        | inl hp =>
          cases hp with
          | intro e hrest =>
            cases hrest with
            | intro body hb =>
              have hget := hb.1
              rw [h0.1] at hget
              injection hget with he; subst he
              injection hb.2.2.1 with hbd; subst hbd
              have hh0 : scT0Held (run.trace (m + 1)) := by
                rw [hb.2.2.2]
                change scT0Held (evalInstr 0 ⟨0, 0⟩ false (.casLoop 0 0 1 1) (run.trace m))
                rw [eval_casLoop, h0.2]
                exact ⟨by dsimp; rw [h0.1]; rfl, memWrite_same (run.trace m).mem 0 1⟩
              exact False.elim (hnh0 (m + 1) hh0)

/-! ### Quantified Per-Thread Positive Liveness 2: Spin-Only `TicketContendedSys` -/

/-- Spin-only FIFO ticket lock (`TicketContendedSys` — no futex sleep or
spurious-wakeup toggling): `T0` acquires once and halts, while environment
contender `T1` loops forever acquiring and releasing. -/
def ticketOnceBody : Nat → ConcInstr
  | 0 => .fetchAdd 0 1
  | 1 => .awaitRegEq 1 2
  | 2 => .storeRegSucc 1 3
  | _ => .halt

def ticketReacquirerBody : Nat → ConcInstr
  | 0 => .fetchAdd 0 1
  | 1 => .awaitRegEq 1 2
  | _ => .storeRegSucc 1 0

def TicketContendedProg : ConcProg := [ticketOnceBody, ticketReacquirerBody]
noncomputable def TicketContendedSys : ConcSystem RegState := mkProgSystem TicketContendedProg

theorem ticketContended_no_bargeIn_step :
    let c1 := evalInstr 0 ⟨0, 0⟩ false (.fetchAdd 0 1) TicketContendedSys.init
    let c2 := evalInstr 1 ⟨0, 0⟩ false (.fetchAdd 0 1) c1
    let c3 := evalInstr 1 ⟨1, 1⟩ false (.awaitRegEq 1 2) c2
    c1.mem 1 = 0 ∧ c2.mem 1 = 0 ∧ c3 = c2 ∧
    (evalInstr 0 ⟨1, 0⟩ false (.awaitRegEq 1 2) c3).threads =
      [⟨⟨2, 0⟩, .enabled, false⟩, ⟨⟨1, 1⟩, .enabled, false⟩] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem nat_beq_self_succ (s : Nat) : Nat.beq s (s + 1) = false := by
  induction s with
  | zero => rfl
  | succ _ ih => exact ih

def tcPre (c : Config RegState) : Prop :=
  ∃ s r1 : Nat,
    (c.threads = [⟨⟨0, 0⟩, .enabled, false⟩, ⟨⟨0, r1⟩, .enabled, false⟩] ∧ c.mem 0 = s ∧ c.mem 1 = s) ∨
    (c.threads = [⟨⟨0, 0⟩, .enabled, false⟩, ⟨⟨1, s⟩, .enabled, false⟩] ∧ c.mem 0 = s + 1 ∧ c.mem 1 = s) ∨
    (c.threads = [⟨⟨0, 0⟩, .enabled, false⟩, ⟨⟨2, s⟩, .enabled, false⟩] ∧ c.mem 0 = s + 1 ∧ c.mem 1 = s)

def tcQueued1 (c : Config RegState) : Prop :=
  ∃ s : Nat,
    c.threads = [⟨⟨1, s + 1⟩, .enabled, false⟩, ⟨⟨1, s⟩, .enabled, false⟩] ∧
    c.mem 0 = s + 2 ∧ c.mem 1 = s

def tcQueued2 (c : Config RegState) : Prop :=
  ∃ s : Nat,
    c.threads = [⟨⟨1, s + 1⟩, .enabled, false⟩, ⟨⟨2, s⟩, .enabled, false⟩] ∧
    c.mem 0 = s + 2 ∧ c.mem 1 = s

def tcMyTurn (c : Config RegState) : Prop :=
  ∃ s : Nat,
    ((∃ r1 : Nat, c.threads = [⟨⟨1, s⟩, .enabled, false⟩, ⟨⟨0, r1⟩, .enabled, false⟩] ∧ c.mem 0 = s + 1) ∨
     (c.threads = [⟨⟨1, s⟩, .enabled, false⟩, ⟨⟨1, s + 1⟩, .enabled, false⟩] ∧ c.mem 0 = s + 2)) ∧
    c.mem 1 = s

def tcInCs (c : Config RegState) : Prop :=
  ∃ s : Nat,
    ((∃ r1 : Nat, c.threads = [⟨⟨2, s⟩, .enabled, false⟩, ⟨⟨0, r1⟩, .enabled, false⟩] ∧ c.mem 0 = s + 1) ∨
     (c.threads = [⟨⟨2, s⟩, .enabled, false⟩, ⟨⟨1, s + 1⟩, .enabled, false⟩] ∧ c.mem 0 = s + 2)) ∧
    c.mem 1 = s

def tcHaltReady (c : Config RegState) : Prop :=
  ∃ r0 : Nat, ∃ st1 : RegState,
    c.threads = [⟨⟨3, r0⟩, .enabled, false⟩, ⟨st1, .enabled, false⟩]

def tcStageGe : Nat → Config RegState → Prop
  | 0, c => tcPre c ∨ tcQueued1 c ∨ tcQueued2 c ∨ tcMyTurn c ∨ tcInCs c ∨ tcHaltReady c ∨ IsTerminated c 0
  | 1, c => tcQueued1 c ∨ tcQueued2 c ∨ tcMyTurn c ∨ tcInCs c ∨ tcHaltReady c ∨ IsTerminated c 0
  | 2, c => tcQueued2 c ∨ tcMyTurn c ∨ tcInCs c ∨ tcHaltReady c ∨ IsTerminated c 0
  | 3, c => tcMyTurn c ∨ tcInCs c ∨ tcHaltReady c ∨ IsTerminated c 0
  | 4, c => tcInCs c ∨ tcHaltReady c ∨ IsTerminated c 0
  | 5, c => tcHaltReady c ∨ IsTerminated c 0
  | _, c => IsTerminated c 0

theorem tcDone_step {tid : ThreadId} {c c' : Config RegState}
    (hd : IsTerminated c 0) (hstep : ProgStepBy TicketContendedProg tid c c') :
    IsTerminated c' 0 := by
  cases hstep with
  | intro e hrest =>
    cases hrest with
    | intro body hb =>
      have hget := hb.1
      have hen := hb.2.1
      have hprog := hb.2.2.1
      have hc' := hb.2.2.2
      subst hc'
      cases tid with
      | zero =>
        cases hd with
        | intro e0 he0 =>
          have heq := listGet_unique hget he0.1
          subst heq; rw [hen] at he0; nomatch he0.2
      | succ t1 =>
        cases t1 with
        | zero =>
          injection hprog with hbd; subst hbd
          cases hd with
          | intro e0 he0 =>
            cases hct : c.threads with
            | nil => rw [hct] at he0; nomatch he0.1
            | cons hd0 tl0 =>
              rw [hct] at he0
              injection he0.1 with hhd; subst hhd
              cases hpce : e.localState.pc with
              | zero =>
                change IsTerminated (evalInstr 1 e.localState e.inWaitEpisode (.fetchAdd 0 1) c) 0
                rw [eval_fetchAdd]
                exact ⟨hd0, by dsimp; rw [hct]; rfl, he0.2⟩
              | succ k =>
                cases k with
                | zero =>
                  change IsTerminated (evalInstr 1 e.localState e.inWaitEpisode (.awaitRegEq 1 2) c) 0
                  rw [eval_awaitRegEq]
                  cases Nat.beq (c.mem 1) e.localState.reg with
                  | false => exact ⟨hd0, by dsimp; rw [hct]; rfl, he0.2⟩
                  | true => exact ⟨hd0, by dsimp; rw [hct]; rfl, he0.2⟩
                | succ _ =>
                  change IsTerminated (evalInstr 1 e.localState e.inWaitEpisode (.storeRegSucc 1 0) c) 0
                  rw [eval_storeRegSucc]
                  exact ⟨hd0, by dsimp; rw [hct]; rfl, he0.2⟩
        | succ _ => nomatch hprog

theorem tcHaltReady_step {tid : ThreadId} {c c' : Config RegState}
    (hh : tcHaltReady c) (hstep : ProgStepBy TicketContendedProg tid c c') :
    tcStageGe 5 c' ∧ (tid = 0 → IsTerminated c' 0) := by
  cases hh with
  | intro r0 hrst =>
    cases hrst with
    | intro st1 hth =>
      cases hstep with
      | intro e hrest =>
        cases hrest with
        | intro body hb =>
          have hget := hb.1
          have hprog := hb.2.2.1
          have hc' := hb.2.2.2
          subst hc'
          rw [hth] at hget
          cases tid with
          | zero =>
            injection hget with he; subst he
            injection hprog with hbd; subst hbd
            have hterm : IsTerminated (evalInstr 0 ⟨3, r0⟩ false (ticketOnceBody 3) c) 0 := by
              change IsTerminated (evalInstr 0 ⟨3, r0⟩ false .halt c) 0
              rw [eval_halt]
              exact ⟨⟨⟨3, r0⟩, .terminated, false⟩, by dsimp; rw [hth]; rfl, rfl⟩
            exact ⟨Or.inr hterm, fun _ => hterm⟩
          | succ t1 =>
            cases t1 with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
              cases hpce : st1.pc with
              | zero =>
                change tcHaltReady (evalInstr 1 st1 false (.fetchAdd 0 1) c)
                rw [eval_fetchAdd]
                exact ⟨r0, ⟨1, c.mem 0⟩, by dsimp; rw [hth]; rfl⟩
              | succ k =>
                cases k with
                | zero =>
                  change tcHaltReady (evalInstr 1 st1 false (.awaitRegEq 1 2) c)
                  rw [eval_awaitRegEq]
                  cases Nat.beq (c.mem 1) st1.reg with
                  | false => exact ⟨r0, st1, hth⟩
                  | true => exact ⟨r0, ⟨2, st1.reg⟩, by dsimp; rw [hth]; rfl⟩
                | succ _ =>
                  change tcHaltReady (evalInstr 1 st1 false (.storeRegSucc 1 0) c)
                  rw [eval_storeRegSucc]
                  exact ⟨r0, ⟨0, st1.reg⟩, by dsimp; rw [hth]; rfl⟩
            | succ _ => nomatch hprog

theorem tcInCs_step {tid : ThreadId} {c c' : Config RegState}
    (hcs : tcInCs c) (hstep : ProgStepBy TicketContendedProg tid c c') :
    tcStageGe 4 c' ∧ (tid = 0 → tcStageGe 5 c') := by
  cases hcs with
  | intro s hs =>
    cases hstep with
    | intro e hrest =>
      cases hrest with
      | intro body hb =>
        have hget := hb.1
        have hprog := hb.2.2.1
        have hc' := hb.2.2.2
        subst hc'
        cases hs.1 with
        | inl hsub0 =>
          cases hsub0 with
          | intro r1 hr1 =>
            rw [hr1.1] at hget
            cases tid with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              have hh : tcHaltReady (evalInstr 0 ⟨2, s⟩ false (ticketOnceBody 2) c) := by
                change tcHaltReady (evalInstr 0 ⟨2, s⟩ false (.storeRegSucc 1 3) c)
                rw [eval_storeRegSucc]
                exact ⟨s, ⟨0, r1⟩, by dsimp; rw [hr1.1]; rfl⟩
              exact ⟨Or.inr (Or.inl hh), fun _ => Or.inl hh⟩
            | succ t1 =>
              cases t1 with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
                change tcInCs (evalInstr 1 ⟨0, r1⟩ false (.fetchAdd 0 1) c)
                rw [eval_fetchAdd, hr1.2]
                exact ⟨s, Or.inr ⟨by dsimp; rw [hr1.1]; rfl, memWrite_same c.mem 0 (s + 2)⟩,
                  by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hs.2⟩
              | succ _ => nomatch hprog
        | inr hsub1 =>
          rw [hsub1.1] at hget
          cases tid with
          | zero =>
            injection hget with he; subst he
            injection hprog with hbd; subst hbd
            have hh : tcHaltReady (evalInstr 0 ⟨2, s⟩ false (ticketOnceBody 2) c) := by
              change tcHaltReady (evalInstr 0 ⟨2, s⟩ false (.storeRegSucc 1 3) c)
              rw [eval_storeRegSucc]
              exact ⟨s, ⟨1, s + 1⟩, by dsimp; rw [hsub1.1]; rfl⟩
            exact ⟨Or.inr (Or.inl hh), fun _ => Or.inl hh⟩
          | succ t1 =>
            cases t1 with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
              change tcInCs (evalInstr 1 ⟨1, s + 1⟩ false (.awaitRegEq 1 2) c)
              rw [eval_awaitRegEq, hs.2, nat_beq_self_succ s]
              exact ⟨s, Or.inr hsub1, hs.2⟩
            | succ _ => nomatch hprog

theorem tcMyTurn_step {tid : ThreadId} {c c' : Config RegState}
    (hmt : tcMyTurn c) (hstep : ProgStepBy TicketContendedProg tid c c') :
    tcStageGe 3 c' ∧ (tid = 0 → tcStageGe 4 c') := by
  cases hmt with
  | intro s hs =>
    cases hstep with
    | intro e hrest =>
      cases hrest with
      | intro body hb =>
        have hget := hb.1
        have hprog := hb.2.2.1
        have hc' := hb.2.2.2
        subst hc'
        cases hs.1 with
        | inl hsub0 =>
          cases hsub0 with
          | intro r1 hr1 =>
            rw [hr1.1] at hget
            cases tid with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              have hcs : tcInCs (evalInstr 0 ⟨1, s⟩ false (ticketOnceBody 1) c) := by
                change tcInCs (evalInstr 0 ⟨1, s⟩ false (.awaitRegEq 1 2) c)
                rw [eval_awaitRegEq, hs.2, Nat.beq_refl s]
                exact ⟨s, Or.inl ⟨r1, by dsimp; rw [hr1.1]; rfl, hr1.2⟩, hs.2⟩
              exact ⟨Or.inr (Or.inl hcs), fun _ => Or.inl hcs⟩
            | succ t1 =>
              cases t1 with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
                change tcMyTurn (evalInstr 1 ⟨0, r1⟩ false (.fetchAdd 0 1) c)
                rw [eval_fetchAdd, hr1.2]
                exact ⟨s, Or.inr ⟨by dsimp; rw [hr1.1]; rfl, memWrite_same c.mem 0 (s + 2)⟩,
                  by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hs.2⟩
              | succ _ => nomatch hprog
        | inr hsub1 =>
          rw [hsub1.1] at hget
          cases tid with
          | zero =>
            injection hget with he; subst he
            injection hprog with hbd; subst hbd
            have hcs : tcInCs (evalInstr 0 ⟨1, s⟩ false (ticketOnceBody 1) c) := by
              change tcInCs (evalInstr 0 ⟨1, s⟩ false (.awaitRegEq 1 2) c)
              rw [eval_awaitRegEq, hs.2, Nat.beq_refl s]
              exact ⟨s, Or.inr ⟨by dsimp; rw [hsub1.1]; rfl, hsub1.2⟩, hs.2⟩
            exact ⟨Or.inr (Or.inl hcs), fun _ => Or.inl hcs⟩
          | succ t1 =>
            cases t1 with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
              change tcMyTurn (evalInstr 1 ⟨1, s + 1⟩ false (.awaitRegEq 1 2) c)
              rw [eval_awaitRegEq, hs.2, nat_beq_self_succ s]
              exact ⟨s, Or.inr hsub1, hs.2⟩
            | succ _ => nomatch hprog

theorem tcQueued2_step {tid : ThreadId} {c c' : Config RegState}
    (hq2 : tcQueued2 c) (hstep : ProgStepBy TicketContendedProg tid c c') :
    tcStageGe 2 c' ∧ (tid = 1 → tcStageGe 3 c') := by
  cases hq2 with
  | intro s hs =>
    cases hstep with
    | intro e hrest =>
      cases hrest with
      | intro body hb =>
        have hget := hb.1
        have hprog := hb.2.2.1
        have hc' := hb.2.2.2
        subst hc'
        rw [hs.1] at hget
        cases tid with
        | zero =>
          injection hget with he; subst he
          injection hprog with hbd; subst hbd
          refine ⟨Or.inl ?_, fun h1 => nomatch h1⟩
          change tcQueued2 (evalInstr 0 ⟨1, s + 1⟩ false (.awaitRegEq 1 2) c)
          rw [eval_awaitRegEq, hs.2.2, nat_beq_self_succ s]
          exact ⟨s, hs⟩
        | succ t1 =>
          cases t1 with
          | zero =>
            injection hget with he; subst he
            injection hprog with hbd; subst hbd
            have hmt : tcMyTurn (evalInstr 1 ⟨2, s⟩ false (ticketReacquirerBody 2) c) := by
              change tcMyTurn (evalInstr 1 ⟨2, s⟩ false (.storeRegSucc 1 0) c)
              rw [eval_storeRegSucc]
              exact ⟨s + 1, Or.inl ⟨s, by dsimp; rw [hs.1]; rfl,
                by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hs.2.1⟩,
                memWrite_same c.mem 1 (s + 1)⟩
            exact ⟨Or.inr (Or.inl hmt), fun _ => Or.inl hmt⟩
          | succ _ => nomatch hprog

theorem tcQueued1_step {tid : ThreadId} {c c' : Config RegState}
    (hq1 : tcQueued1 c) (hstep : ProgStepBy TicketContendedProg tid c c') :
    tcStageGe 1 c' ∧ (tid = 1 → tcStageGe 2 c') := by
  cases hq1 with
  | intro s hs =>
    cases hstep with
    | intro e hrest =>
      cases hrest with
      | intro body hb =>
        have hget := hb.1
        have hprog := hb.2.2.1
        have hc' := hb.2.2.2
        subst hc'
        rw [hs.1] at hget
        cases tid with
        | zero =>
          injection hget with he; subst he
          injection hprog with hbd; subst hbd
          refine ⟨Or.inl ?_, fun h1 => nomatch h1⟩
          change tcQueued1 (evalInstr 0 ⟨1, s + 1⟩ false (.awaitRegEq 1 2) c)
          rw [eval_awaitRegEq, hs.2.2, nat_beq_self_succ s]
          exact ⟨s, hs⟩
        | succ t1 =>
          cases t1 with
          | zero =>
            injection hget with he; subst he
            injection hprog with hbd; subst hbd
            have hq2 : tcQueued2 (evalInstr 1 ⟨1, s⟩ false (ticketReacquirerBody 1) c) := by
              change tcQueued2 (evalInstr 1 ⟨1, s⟩ false (.awaitRegEq 1 2) c)
              rw [eval_awaitRegEq, hs.2.2, Nat.beq_refl s]
              exact ⟨s, by dsimp; rw [hs.1]; rfl, hs.2.1, hs.2.2⟩
            exact ⟨Or.inr (Or.inl hq2), fun _ => Or.inl hq2⟩
          | succ _ => nomatch hprog

theorem tcPre_step {tid : ThreadId} {c c' : Config RegState}
    (hpre : tcPre c) (hstep : ProgStepBy TicketContendedProg tid c c') :
    tcStageGe 0 c' ∧ (tid = 0 → tcStageGe 1 c') := by
  cases hpre with
  | intro s hs0 =>
    cases hs0 with
    | intro r1 hs =>
      cases hstep with
      | intro e hrest =>
        cases hrest with
        | intro body hb =>
          have hget := hb.1
          have hprog := hb.2.2.1
          have hc' := hb.2.2.2
          subst hc'
          cases hs with
          | inl hp0 =>
            rw [hp0.1] at hget
            cases tid with
            | zero =>
              injection hget with he; subst he
              injection hprog with hbd; subst hbd
              have hmt : tcMyTurn (evalInstr 0 ⟨0, 0⟩ false (ticketOnceBody 0) c) := by
                change tcMyTurn (evalInstr 0 ⟨0, 0⟩ false (.fetchAdd 0 1) c)
                rw [eval_fetchAdd, hp0.2.1]
                exact ⟨s, Or.inl ⟨r1, by dsimp; rw [hp0.1]; rfl, memWrite_same c.mem 0 (s + 1)⟩,
                  by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hp0.2.2⟩
              exact ⟨Or.inr (Or.inr (Or.inr (Or.inl hmt))), fun _ => Or.inr (Or.inr (Or.inl hmt))⟩
            | succ t1 =>
              cases t1 with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
                change tcPre (evalInstr 1 ⟨0, r1⟩ false (.fetchAdd 0 1) c)
                rw [eval_fetchAdd, hp0.2.1]
                exact ⟨s, r1, Or.inr (Or.inl ⟨by dsimp; rw [hp0.1]; rfl,
                  memWrite_same c.mem 0 (s + 1),
                  by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hp0.2.2⟩)⟩
              | succ _ => nomatch hprog
          | inr hrestp =>
            cases hrestp with
            | inl hp1 =>
              rw [hp1.1] at hget
              cases tid with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                have hq1 : tcQueued1 (evalInstr 0 ⟨0, 0⟩ false (ticketOnceBody 0) c) := by
                  change tcQueued1 (evalInstr 0 ⟨0, 0⟩ false (.fetchAdd 0 1) c)
                  rw [eval_fetchAdd, hp1.2.1]
                  exact ⟨s, by dsimp; rw [hp1.1]; rfl, memWrite_same c.mem 0 (s + 2),
                    by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hp1.2.2⟩
                exact ⟨Or.inr (Or.inl hq1), fun _ => Or.inl hq1⟩
              | succ t1 =>
                cases t1 with
                | zero =>
                  injection hget with he; subst he
                  injection hprog with hbd; subst hbd
                  refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
                  change tcPre (evalInstr 1 ⟨1, s⟩ false (.awaitRegEq 1 2) c)
                  rw [eval_awaitRegEq, hp1.2.2, Nat.beq_refl s]
                  exact ⟨s, r1, Or.inr (Or.inr ⟨by dsimp; rw [hp1.1]; rfl, hp1.2.1, hp1.2.2⟩)⟩
                | succ _ => nomatch hprog
            | inr hp2 =>
              rw [hp2.1] at hget
              cases tid with
              | zero =>
                injection hget with he; subst he
                injection hprog with hbd; subst hbd
                have hq2 : tcQueued2 (evalInstr 0 ⟨0, 0⟩ false (ticketOnceBody 0) c) := by
                  change tcQueued2 (evalInstr 0 ⟨0, 0⟩ false (.fetchAdd 0 1) c)
                  rw [eval_fetchAdd, hp2.2.1]
                  exact ⟨s, by dsimp; rw [hp2.1]; rfl, memWrite_same c.mem 0 (s + 2),
                    by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hp2.2.2⟩
                exact ⟨Or.inr (Or.inr (Or.inl hq2)), fun _ => Or.inr (Or.inl hq2)⟩
              | succ t1 =>
                cases t1 with
                | zero =>
                  injection hget with he; subst he
                  injection hprog with hbd; subst hbd
                  refine ⟨Or.inl ?_, fun h0 => nomatch h0⟩
                  change tcPre (evalInstr 1 ⟨2, s⟩ false (.storeRegSucc 1 0) c)
                  rw [eval_storeRegSucc]
                  exact ⟨s + 1, s, Or.inl ⟨by dsimp; rw [hp2.1]; rfl,
                    by dsimp; rw [memWrite_diff c.mem _ rfl]; exact hp2.2.1,
                    memWrite_same c.mem 1 (s + 1)⟩⟩
                | succ _ => nomatch hprog

theorem tcStageGe_step_mono (k : Nat) {tid : ThreadId} {c c' : Config RegState}
    (hk : tcStageGe k c) (hstep : ProgStepBy TicketContendedProg tid c c') :
    tcStageGe k c' := by
  cases k with
  | zero =>
    cases hk with
    | inl hp => exact (tcPre_step hp hstep).1
    | inr r1 =>
      cases r1 with
      | inl hq1 => exact Or.inr (tcQueued1_step hq1 hstep).1
      | inr r2 =>
        cases r2 with
        | inl hq2 => exact Or.inr (Or.inr (tcQueued2_step hq2 hstep).1)
        | inr r3 =>
          cases r3 with
          | inl hmt => exact Or.inr (Or.inr (Or.inr (tcMyTurn_step hmt hstep).1))
          | inr r4 =>
            cases r4 with
            | inl hcs => exact Or.inr (Or.inr (Or.inr (Or.inr (tcInCs_step hcs hstep).1)))
            | inr r5 =>
              cases r5 with
              | inl hh => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tcHaltReady_step hh hstep).1))))
              | inr hd => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tcDone_step hd hstep))))))
  | succ k1 =>
    cases k1 with
    | zero =>
      cases hk with
      | inl hq1 => exact (tcQueued1_step hq1 hstep).1
      | inr r2 =>
        cases r2 with
        | inl hq2 => exact Or.inr (tcQueued2_step hq2 hstep).1
        | inr r3 =>
          cases r3 with
          | inl hmt => exact Or.inr (Or.inr (tcMyTurn_step hmt hstep).1)
          | inr r4 =>
            cases r4 with
            | inl hcs => exact Or.inr (Or.inr (Or.inr (tcInCs_step hcs hstep).1))
            | inr r5 =>
              cases r5 with
              | inl hh => exact Or.inr (Or.inr (Or.inr (Or.inr (tcHaltReady_step hh hstep).1)))
              | inr hd => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tcDone_step hd hstep)))))
    | succ k2 =>
      cases k2 with
      | zero =>
        cases hk with
        | inl hq2 => exact (tcQueued2_step hq2 hstep).1
        | inr r3 =>
          cases r3 with
          | inl hmt => exact Or.inr (tcMyTurn_step hmt hstep).1
          | inr r4 =>
            cases r4 with
            | inl hcs => exact Or.inr (Or.inr (tcInCs_step hcs hstep).1)
            | inr r5 =>
              cases r5 with
              | inl hh => exact Or.inr (Or.inr (Or.inr (tcHaltReady_step hh hstep).1))
              | inr hd => exact Or.inr (Or.inr (Or.inr (Or.inr (tcDone_step hd hstep))))
      | succ k3 =>
        cases k3 with
        | zero =>
          cases hk with
          | inl hmt => exact (tcMyTurn_step hmt hstep).1
          | inr r4 =>
            cases r4 with
            | inl hcs => exact Or.inr (tcInCs_step hcs hstep).1
            | inr r5 =>
              cases r5 with
              | inl hh => exact Or.inr (Or.inr (tcHaltReady_step hh hstep).1)
              | inr hd => exact Or.inr (Or.inr (Or.inr (tcDone_step hd hstep)))
        | succ k4 =>
          cases k4 with
          | zero =>
            cases hk with
            | inl hcs => exact (tcInCs_step hcs hstep).1
            | inr r5 =>
              cases r5 with
              | inl hh => exact Or.inr (tcHaltReady_step hh hstep).1
              | inr hd => exact Or.inr (Or.inr (tcDone_step hd hstep))
          | succ k5 =>
            cases k5 with
            | zero =>
              cases hk with
              | inl hh => exact (tcHaltReady_step hh hstep).1
              | inr hd => exact Or.inr (tcDone_step hd hstep)
            | succ _ => exact tcDone_step hk hstep

theorem tcStageGe_persist {run : Run RegState}
    (hv : ValidRun TicketContendedSys run)
    (k n : Nat) (hkn : tcStageGe k (run.trace n)) :
    ∀ m : Nat, n ≤ m → tcStageGe k (run.trace m) := by
  have hadd : ∀ d : Nat, tcStageGe k (run.trace (n + d)) := by
    intro d
    induction d with
    | zero => exact hkn
    | succ d' ih =>
      have hstep := hv.2 (n + d')
      cases hs : run.stepAt (n + d') with
      | none =>
        rw [hs] at hstep
        rw [Nat.add_succ, hstep.2.2]
        exact ih
      | some tid =>
        rw [hs] at hstep
        cases hstep with
        | inr hw => exact False.elim hw
        | inl hp =>
          rw [Nat.add_succ]
          exact tcStageGe_step_mono k ih hp
  intro m hle
  have heq : m = n + (m - n) := Eq.symm (Nat.add_sub_of_le hle)
  rw [heq]
  exact hadd (m - n)

theorem tc_both_enabled_of_not_done {c : Config RegState}
    (h0 : tcStageGe 0 c) (hnt : ¬ IsTerminated c 0) :
    IsEnabled c 0 ∧ IsEnabled c 1 := by
  cases h0 with
  | inl hp =>
    cases hp with
    | intro s hs0 =>
      cases hs0 with
      | intro r1 hs =>
        cases hs with
        | inl p0 => exact enabled_pair p0.1
        | inr rp =>
          cases rp with
          | inl p1 => exact enabled_pair p1.1
          | inr p2 => exact enabled_pair p2.1
  | inr r1 =>
    cases r1 with
    | inl hq1 =>
      cases hq1 with | intro s hs => exact enabled_pair hs.1
    | inr r2 =>
      cases r2 with
      | inl hq2 =>
        cases hq2 with | intro s hs => exact enabled_pair hs.1
      | inr r3 =>
        cases r3 with
        | inl hmt =>
          cases hmt with
          | intro s hs =>
            cases hs.1 with
            | inl sub0 =>
              cases sub0 with | intro r1 hr1 => exact enabled_pair hr1.1
            | inr sub1 => exact enabled_pair sub1.1
        | inr r4 =>
          cases r4 with
          | inl hcs =>
            cases hcs with
            | intro s hs =>
              cases hs.1 with
              | inl sub0 =>
                cases sub0 with | intro r1 hr1 => exact enabled_pair hr1.1
              | inr sub1 => exact enabled_pair sub1.1
          | inr r5 =>
            cases r5 with
            | inl hh =>
              cases hh with
              | intro r0 hst =>
                cases hst with | intro st1 hth => exact enabled_pair hth
            | inr hd => exact False.elim (hnt hd)

/-- Honest per-thread non-starvation theorem: on the spin-only
`TicketContendedSys`, Thread `WeakFair` ALONE guarantees `PerThreadStarvationFree`
for `T0` (`Eventually (fun n => IsTerminated (run.trace n) 0)`), strictly
separating FIFO ticket locks from `SpinContendedSys` (which requires
`ActionStrongFair`), while `T1` loops forever (see `ticketContended_T1_never_terminates`). -/
theorem ticketContended_weakFair_T0_starvation_free :
    PerThreadStarvationFree WeakFair TicketContendedSys 0 IsTerminated := by
  intro run hv hwf
  cases cs_em (Eventually (fun n => IsTerminated (run.trace n) 0)) with
  | inl h => exact h
  | inr hnev =>
    have hnt : ∀ n : Nat, ¬ IsTerminated (run.trace n) 0 :=
      fun n ht => hnev ⟨n, ht⟩
    have hinit0 : tcStageGe 0 (run.trace 0) := by
      rw [hv.1]
      exact Or.inl ⟨0, 0, Or.inl ⟨rfl, rfl, rfl⟩⟩
    have hall0 : ∀ n : Nat, tcStageGe 0 (run.trace n) :=
      fun n => tcStageGe_persist hv 0 0 hinit0 n (Nat.zero_le n)
    have hen0 : EventuallyAlways (fun n => IsEnabled (run.trace n) 0) :=
      ⟨0, fun n _ => (tc_both_enabled_of_not_done (hall0 n) (hnt n)).1⟩
    have hen1 : EventuallyAlways (fun n => IsEnabled (run.trace n) 1) :=
      ⟨0, fun n _ => (tc_both_enabled_of_not_done (hall0 n) (hnt n)).2⟩
    have hio0 := hwf 0 hen0
    have hio1 := hwf 1 hen1
    cases hio0 0 with
    | intro m0 hm0 =>
      have hs1 : tcStageGe 1 (run.trace (m0 + 1)) := by
        have hstep := hv.2 m0
        rw [hm0.2] at hstep
        cases hstep with
        | inr hw => exact False.elim hw
        | inl hprogStep =>
          cases hall0 m0 with
          | inl hp => exact (tcPre_step hp hprogStep).2 rfl
          | inr r1 => exact tcStageGe_step_mono 1 r1 hprogStep
      cases hio1 (m0 + 1) with
      | intro m1 hm1 =>
        have hs2 : tcStageGe 2 (run.trace (m1 + 1)) := by
          have hstep := hv.2 m1
          rw [hm1.2] at hstep
          cases hstep with
          | inr hw => exact False.elim hw
          | inl hprogStep =>
            cases tcStageGe_persist hv 1 (m0 + 1) hs1 m1 hm1.1 with
            | inl hq1 => exact (tcQueued1_step hq1 hprogStep).2 rfl
            | inr r2 => exact tcStageGe_step_mono 2 r2 hprogStep
        cases hio1 (m1 + 1) with
        | intro m2 hm2 =>
          have hs3 : tcStageGe 3 (run.trace (m2 + 1)) := by
            have hstep := hv.2 m2
            rw [hm2.2] at hstep
            cases hstep with
            | inr hw => exact False.elim hw
            | inl hprogStep =>
              cases tcStageGe_persist hv 2 (m1 + 1) hs2 m2 hm2.1 with
              | inl hq2 => exact (tcQueued2_step hq2 hprogStep).2 rfl
              | inr r3 => exact tcStageGe_step_mono 3 r3 hprogStep
          cases hio0 (m2 + 1) with
          | intro m3 hm3 =>
            have hs4 : tcStageGe 4 (run.trace (m3 + 1)) := by
              have hstep := hv.2 m3
              rw [hm3.2] at hstep
              cases hstep with
              | inr hw => exact False.elim hw
              | inl hprogStep =>
                cases tcStageGe_persist hv 3 (m2 + 1) hs3 m3 hm3.1 with
                | inl hmt => exact (tcMyTurn_step hmt hprogStep).2 rfl
                | inr r4 => exact tcStageGe_step_mono 4 r4 hprogStep
            cases hio0 (m3 + 1) with
            | intro m4 hm4 =>
              have hs5 : tcStageGe 5 (run.trace (m4 + 1)) := by
                have hstep := hv.2 m4
                rw [hm4.2] at hstep
                cases hstep with
                | inr hw => exact False.elim hw
                | inl hprogStep =>
                  cases tcStageGe_persist hv 4 (m3 + 1) hs4 m4 hm4.1 with
                  | inl hcs => exact (tcInCs_step hcs hprogStep).2 rfl
                  | inr r5 => exact tcStageGe_step_mono 5 r5 hprogStep
              cases hio0 (m4 + 1) with
              | intro m5 hm5 =>
                have hs6 : IsTerminated (run.trace (m5 + 1)) 0 := by
                  have hstep := hv.2 m5
                  rw [hm5.2] at hstep
                  cases hstep with
                  | inr hw => exact False.elim hw
                  | inl hprogStep =>
                    cases tcStageGe_persist hv 5 (m4 + 1) hs5 m5 hm5.1 with
                    | inl hh => exact (tcHaltReady_step hh hprogStep).2 rfl
                    | inr hd => exact tcDone_step hd hprogStep
                exact False.elim (hnt (m5 + 1) hs6)

theorem wakeFutexAll_preserves_enabled {addr : Addr}
    {es : List (ThreadEntry RegState)} {i : Nat} {e : ThreadEntry RegState}
    (hget : listGet? es i = some e) (hen : e.status = .enabled) :
    listGet? (wakeFutexAll addr es) i = some e := by
  induction es generalizing i with
  | nil => nomatch hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      injection hget with heq; subst heq
      rw [wakeFutexAll_cons, hen, listGet_zero]
    | succ k =>
      rw [wakeFutexAll_cons, listGet_succ]
      exact ih hget

theorem wakeJoiners_preserves_enabled {doneTid : ThreadId}
    {es : List (ThreadEntry RegState)} {i : Nat} {e : ThreadEntry RegState}
    (hget : listGet? es i = some e) (hen : e.status = .enabled) :
    listGet? (wakeJoiners doneTid es) i = some e := by
  induction es generalizing i with
  | nil => nomatch hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      injection hget with heq; subst heq
      rw [wakeJoiners_cons, hen, listGet_zero]
    | succ k =>
      rw [wakeJoiners_cons, listGet_succ]
      exact ih hget

theorem wakeParked_preserves_enabled {target : ThreadId}
    {es : List (ThreadEntry RegState)} {i : Nat} {e : ThreadEntry RegState}
    (hget : listGet? es i = some e) (hen : e.status = .enabled) :
    listGet? (wakeParked target es) i = some e := by
  rw [wakeParked_eq]
  cases ht : listGet? es target with
  | none => dsimp only; exact hget
  | some te =>
    dsimp only
    cases hst : te.status with
    | enabled => dsimp only; exact hget
    | terminated => dsimp only; exact hget
    | blocked r =>
      cases r with
      | futex _ _ => dsimp only; exact hget
      | join _ => dsimp only; exact hget
      | park =>
        dsimp only
        have hne : target ≠ i := by
          intro heq; subst heq
          have hete := listGet_unique ht hget
          subst hete
          rw [hen] at hst
          nomatch hst
        rw [listSet_other hne]
        exact hget

theorem evalInstr_preserves_other_enabled {tid i : ThreadId} {st : RegState}
    {iw : Bool} {instr : ConcInstr} {c : Config RegState}
    {e : ThreadEntry RegState}
    (hne : tid ≠ i)
    (hget : listGet? c.threads i = some e) (hen : e.status = .enabled) :
    listGet? (evalInstr tid st iw instr c).threads i = some e := by
  cases instr with
  | casLoop addr exp _ _ =>
    rw [eval_casLoop]
    cases Nat.beq (c.mem addr) exp with
    | false => dsimp; exact hget
    | true => dsimp; rw [listSet_other hne]; exact hget
  | store _ _ _ => rw [eval_store]; dsimp; rw [listSet_other hne]; exact hget
  | storeRegSucc _ _ => rw [eval_storeRegSucc]; dsimp; rw [listSet_other hne]; exact hget
  | fetchAdd _ _ => rw [eval_fetchAdd]; dsimp; rw [listSet_other hne]; exact hget
  | awaitRegEq addr _ =>
    rw [eval_awaitRegEq]
    cases Nat.beq (c.mem addr) st.reg with
    | false => dsimp; exact hget
    | true => dsimp; rw [listSet_other hne]; exact hget
  | futexLock addr _ =>
    rw [eval_futexLock]
    cases Nat.beq (c.mem addr) 0 with
    | false => dsimp; rw [listSet_other hne]; exact hget
    | true => dsimp; rw [listSet_other hne]; exact hget
  | futexWaitEnter addr _ _ =>
    rw [eval_futexWaitEnter]
    cases iw with
    | true => dsimp; rw [listSet_other hne]; exact hget
    | false =>
      dsimp
      cases Nat.beq (c.mem addr) 0 with
      | false => dsimp; rw [listSet_other hne]; exact hget
      | true => dsimp; rw [listSet_other hne]; exact hget
  | futexRetryAcquire addr _ _ =>
    rw [eval_futexRetryAcquire]
    cases Nat.beq (c.mem addr) 0 with
    | false => dsimp; rw [listSet_other hne]; exact hget
    | true => dsimp; rw [listSet_other hne]; exact hget
  | futexUnlock addr _ =>
    rw [eval_futexUnlock]; dsimp
    rw [listSet_other hne]
    exact wakeFutexAll_preserves_enabled hget hen
  | parkWait _ =>
    rw [eval_parkWait]
    cases c.parkToken tid with
    | false => dsimp; rw [listSet_other hne]; exact hget
    | true => dsimp; rw [listSet_other hne]; exact hget
  | unparkThread target _ =>
    rw [eval_unparkThread]; dsimp
    rw [listSet_other hne]
    exact wakeParked_preserves_enabled hget hen
  | joinThread target _ =>
    rw [eval_joinThread]
    cases listGet? c.threads target with
    | none => dsimp; rw [listSet_other hne]; exact hget
    | some te =>
      dsimp
      cases te.status with
      | enabled => dsimp; rw [listSet_other hne]; exact hget
      | blocked _ => dsimp; rw [listSet_other hne]; exact hget
      | terminated => dsimp; rw [listSet_other hne]; exact hget
  | spinSelf => exact hget
  | halt =>
    rw [eval_halt]; dsimp
    apply wakeJoiners_preserves_enabled _ hen
    rw [listSet_other hne]
    exact hget

/-- Honest scope separation: in `TicketContendedSys`, the infinite
environment contender `T1` NEVER terminates on ANY valid run (so whole-system
`RunTerminates` / `AllTerminated` is strictly FALSE, separating per-thread
non-starvation `ticketContended_weakFair_T0_starvation_free` from whole-system
termination!). -/
theorem ticketContended_T1_never_terminates :
    (∀ run : Run RegState, ValidRun TicketContendedSys run →
      ∀ n : Nat, ¬ IsTerminated (run.trace n) 1) ∧
    (∀ run : Run RegState, ValidRun TicketContendedSys run →
      ¬ RunTerminates run) := by
  have h1en : ∀ (run : Run RegState), ValidRun TicketContendedSys run →
      ∀ n : Nat, ∃ e1 : ThreadEntry RegState,
        listGet? (run.trace n).threads 1 = some e1 ∧ e1.status = .enabled := by
    intro run hv n
    induction n with
    | zero =>
      rw [hv.1]
      exact ⟨⟨⟨0, 0⟩, .enabled, false⟩, rfl, rfl⟩
    | succ k ih =>
      cases ih with
      | intro e1 he1 =>
        have hstep := hv.2 k
        cases hs : run.stepAt k with
        | none =>
          rw [hs] at hstep
          rw [hstep.2.2]
          exact ⟨e1, he1⟩
        | some tid =>
          rw [hs] at hstep
          cases hstep with
          | inr hw => exact False.elim hw
          | inl hp =>
            cases hp with
            | intro e hrest =>
              cases hrest with
              | intro body hb =>
                rw [hb.2.2.2]
                cases Decidable.em (tid = 1) with
                | inr hne =>
                  exact ⟨e1, evalInstr_preserves_other_enabled hne he1.1 he1.2, he1.2⟩
                | inl heq =>
                  subst heq
                  injection hb.2.2.1 with hbd; subst hbd
                  cases hpc : e.localState.pc with
                  | zero =>
                    change ∃ x, listGet? (evalInstr 1 e.localState e.inWaitEpisode (.fetchAdd 0 1) (run.trace k)).threads 1 = some x ∧ x.status = .enabled
                    rw [eval_fetchAdd]
                    exact ⟨_, listSet_same hb.1, rfl⟩
                  | succ k1 =>
                    cases k1 with
                    | zero =>
                      change ∃ x, listGet? (evalInstr 1 e.localState e.inWaitEpisode (.awaitRegEq 1 2) (run.trace k)).threads 1 = some x ∧ x.status = .enabled
                      rw [eval_awaitRegEq]
                      cases Nat.beq ((run.trace k).mem 1) e.localState.reg with
                      | false => exact ⟨e1, he1⟩
                      | true => exact ⟨_, listSet_same hb.1, rfl⟩
                    | succ _ =>
                      change ∃ x, listGet? (evalInstr 1 e.localState e.inWaitEpisode (.storeRegSucc 1 0) (run.trace k)).threads 1 = some x ∧ x.status = .enabled
                      rw [eval_storeRegSucc]
                      exact ⟨_, listSet_same hb.1, rfl⟩
  have hnt1 : ∀ run : Run RegState, ValidRun TicketContendedSys run →
      ∀ n : Nat, ¬ IsTerminated (run.trace n) 1 := by
    intro run hv n hterm
    cases h1en run hv n with
    | intro e1 he1 =>
      cases hterm with
      | intro e2 he2 =>
        have hee := listGet_unique he1.1 he2.1
        subst hee
        rw [he1.2] at he2
        nomatch he2.2
  refine ⟨hnt1, ?_⟩
  intro run hv hrt
  cases hrt with
  | intro n hall =>
    cases h1en run hv n with
    | intro e1 he1 =>
      exact hnt1 run hv n ⟨e1, he1.1, hall 1 e1 he1.1⟩

/-! ### Guard Leak (`mem::forget`) Counter-Model -/

def leakHolderBody : Nat → ConcInstr
  | 0 => .casLoop 0 0 1 1
  | _ => .halt

def LeakSpinProg : ConcProg := [leakHolderBody, spinOnceBody]
noncomputable def LeakSpinSys : ConcSystem RegState := mkProgSystem LeakSpinProg

def leakCfg1 : Config RegState :=
  { threads := [⟨⟨1, 0⟩, .enabled, false⟩, ⟨⟨0, 0⟩, .enabled, false⟩]
    mem := memWrite (fun _ => 0) 0 1
    parkToken := fun _ => false }

def leakCfg2 : Config RegState :=
  { threads := [⟨⟨1, 0⟩, .terminated, false⟩, ⟨⟨0, 0⟩, .enabled, false⟩]
    mem := memWrite (fun _ => 0) 0 1
    parkToken := fun _ => false }

noncomputable def leakRun : Run RegState :=
  { trace := fun n => match n with | 0 => LeakSpinSys.init | 1 => leakCfg1 | _ + 2 => leakCfg2
    stepAt := fun n => match n with | 0 => some 0 | 1 => some 0 | _ + 2 => some 1 }

theorem leakRun_hangs_under_strong_and_actionStrong_fairness :
    ValidRun LeakSpinSys leakRun ∧
    StrongFair leakRun ∧
    ActionStrongFair LockAvailable LockAcquired leakRun ∧
    ¬ RunTerminates leakRun := by
  have hv : ValidRun LeakSpinSys leakRun := by
    refine ⟨rfl, ?_⟩
    intro n
    cases n with
    | zero => exact Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, leakHolderBody, rfl, rfl, rfl, rfl⟩
    | succ n1 =>
      cases n1 with
      | zero => exact Or.inl ⟨⟨⟨1, 0⟩, .enabled, false⟩, leakHolderBody, rfl, rfl, rfl, rfl⟩
      | succ _ => exact Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, spinOnceBody, rfl, rfl, rfl, rfl⟩
  have hsf : StrongFair leakRun := by
    intro t hio
    cases t with
    | zero =>
      cases hio 2 with
      | intro n hn =>
        cases n with
        | zero => nomatch hn.1
        | succ n1 =>
          cases n1 with
          | zero => nomatch (Nat.le_of_succ_le_succ hn.1)
          | succ _ =>
            cases hn.2 with
            | intro e he =>
              injection he.1 with heq; subst heq; nomatch he.2
    | succ t1 =>
      cases t1 with
      | zero =>
        intro N
        exact ⟨N + 2, Nat.le_add_right N 2, rfl⟩
      | succ _ =>
        cases hio 2 with
        | intro n hn =>
          cases n with
          | zero => nomatch hn.1
          | succ n1 =>
            cases n1 with
            | zero => nomatch (Nat.le_of_succ_le_succ hn.1)
            | succ _ =>
              cases hn.2 with
              | intro e he => nomatch he.1
  have hasf : ActionStrongFair LockAvailable LockAcquired leakRun := by
    intro t hio
    cases hio 1 with
    | intro n hn =>
      cases n with
      | zero => nomatch hn.1
      | succ n1 =>
        cases n1 with
        | zero => nomatch hn.2.2
        | succ _ => nomatch hn.2.2
  have hnt : ¬ RunTerminates leakRun := by
    intro hterm
    cases hterm with
    | intro n hall =>
      dsimp at hall
      cases n with
      | zero => nomatch (hall 1 ⟨⟨0, 0⟩, .enabled, false⟩ rfl)
      | succ n1 =>
        cases n1 with
        | zero => nomatch (hall 1 ⟨⟨0, 0⟩, .enabled, false⟩ rfl)
        | succ _ => nomatch (hall 1 ⟨⟨0, 0⟩, .enabled, false⟩ rfl)
  exact ⟨hv, hsf, hasf, hnt⟩

/-! ### 2-PC Lock-Retry + Spurious Wakeup + Background Spinner AB-BA System -/

/-- Realistic 2-PC futex-retry AB-BA thread `T0`:
- `pc=0`: acquires Mutex 0 (`futexLock 0 1`),
- `pc=1`: enters wait episode on Mutex 1 (`futexWaitEnter 1 2 3`); on spurious
  wakeup (`inWaitEpisode = true`, `.enabled`), increments retry counter `reg + 1`
  and jumps to `pc=2` (changing `localState`!),
- `pc=2`: reloads `mem 1` (`futexRetryAcquire 1 1 3`); if locked, re-blocks at
  `pc=1` preserving `inWaitEpisode = true`; if unlocked, acquires, clears
  `inWaitEpisode := false`, and jumps to `pc=3`. -/
def mutexMultiPcAbBody : Nat → ConcInstr
  | 0 => .futexLock 0 1
  | 1 => .futexWaitEnter 1 2 3
  | 2 => .futexRetryAcquire 1 1 3
  | 3 => .futexUnlock 1 4
  | 4 => .futexUnlock 0 5
  | _ => .halt

def mutexMultiPcBaBody : Nat → ConcInstr
  | 0 => .futexLock 1 1
  | 1 => .futexWaitEnter 0 2 3
  | 2 => .futexRetryAcquire 0 1 3
  | 3 => .futexUnlock 0 4
  | 4 => .futexUnlock 1 5
  | _ => .halt

def spinnerBody : Nat → ConcInstr
  | _ => .spinSelf

def AbBaMultiPcSpinnerProg : ConcProg :=
  [mutexMultiPcAbBody, mutexMultiPcBaBody, spinnerBody]

noncomputable def AbBaMultiPcSpuriousSpinnerSys : ConcSystem RegState :=
  mkSpuriousProgSystem AbBaMultiPcSpinnerProg

def AbBaMultiPc2Prog : ConcProg :=
  [mutexMultiPcAbBody, mutexMultiPcBaBody]

noncomputable def AbBaMultiPcSpurious2Sys : ConcSystem RegState :=
  mkSpuriousProgSystem AbBaMultiPc2Prog

noncomputable def abBaMultiPcStep1 : Config RegState :=
  evalInstr 0 ⟨0, 0⟩ false (.futexLock 0 1) AbBaMultiPcSpuriousSpinnerSys.init

noncomputable def abBaMultiPcStep2 : Config RegState :=
  evalInstr 1 ⟨0, 0⟩ false (.futexLock 1 1) abBaMultiPcStep1

noncomputable def abBaMultiPcStep3 : Config RegState :=
  evalInstr 0 ⟨1, 0⟩ false (.futexWaitEnter 1 2 3) abBaMultiPcStep2

noncomputable def abBaMultiPcDeadlockedCfg : Config RegState :=
  evalInstr 1 ⟨1, 0⟩ false (.futexWaitEnter 0 2 3) abBaMultiPcStep3

noncomputable def abBaMultiPcWoken0Cfg : Config RegState :=
  { abBaMultiPcDeadlockedCfg with
    threads := listSet abBaMultiPcDeadlockedCfg.threads 0
      ⟨⟨1, 0⟩, .enabled, true⟩ }

noncomputable def abBaMultiPcRetryPc2Cfg : Config RegState :=
  evalInstr 0 ⟨1, 0⟩ true (.futexWaitEnter 1 2 3) abBaMultiPcWoken0Cfg

noncomputable def abBaMultiPcReblockedCfg : Config RegState :=
  evalInstr 0 ⟨2, 1⟩ true (.futexRetryAcquire 1 1 3) abBaMultiPcRetryPc2Cfg

theorem abBaMultiPcDeadlockedCfg_reachable :
    Reachable AbBaMultiPcSpuriousSpinnerSys abBaMultiPcDeadlockedCfg := by
  have r0 : Reaches AbBaMultiPcSpuriousSpinnerSys
      AbBaMultiPcSpuriousSpinnerSys.init AbBaMultiPcSpuriousSpinnerSys.init := .refl _
  have r1 : Reaches AbBaMultiPcSpuriousSpinnerSys
      AbBaMultiPcSpuriousSpinnerSys.init abBaMultiPcStep1 :=
    .tail r0 (Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, mutexMultiPcAbBody, rfl, rfl, rfl, rfl⟩)
  have r2 : Reaches AbBaMultiPcSpuriousSpinnerSys
      AbBaMultiPcSpuriousSpinnerSys.init abBaMultiPcStep2 :=
    .tail r1 (Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, mutexMultiPcBaBody, rfl, rfl, rfl, rfl⟩)
  have r3 : Reaches AbBaMultiPcSpuriousSpinnerSys
      AbBaMultiPcSpuriousSpinnerSys.init abBaMultiPcStep3 :=
    .tail r2 (Or.inl ⟨⟨⟨1, 0⟩, .enabled, false⟩, mutexMultiPcAbBody, rfl, rfl, rfl, rfl⟩)
  exact .tail r3 (Or.inl ⟨⟨⟨1, 0⟩, .enabled, false⟩, mutexMultiPcBaBody, rfl, rfl, rfl, rfl⟩)

/-- Refutation of the naive `localState ≠ localState` progress predicate:
in `AbBaMultiPcSpuriousSpinnerSys`, from `abBaMultiPcDeadlockedCfg` (`T0` at
`⟨1, 0⟩`), demonic `OsSpuriousFutexWake` + 1 retry step moves `T0` to `pc=2,
reg=1` (`localState = ⟨2, 1⟩ ≠ ⟨1, 0⟩`) before `pc=2` reloads `mem 1 = 1` and
re-blocks at `pc=1, reg=1` keeping `inWaitEpisode = true`. Hence old
`IsDeadlockedSubsystemProgress` FAILS to flag `{0, 1}`! -/
theorem multiPcSpuriousRetry_breaks_localState_progress :
    Reachable AbBaMultiPcSpuriousSpinnerSys abBaMultiPcDeadlockedCfg ∧
    AbBaMultiPcSpuriousSpinnerSys.stepBy 0 abBaMultiPcDeadlockedCfg abBaMultiPcWoken0Cfg ∧
    AbBaMultiPcSpuriousSpinnerSys.stepBy 0 abBaMultiPcWoken0Cfg abBaMultiPcRetryPc2Cfg ∧
    AbBaMultiPcSpuriousSpinnerSys.stepBy 0 abBaMultiPcRetryPc2Cfg abBaMultiPcReblockedCfg ∧
    ThreadMadeProgress abBaMultiPcDeadlockedCfg abBaMultiPcRetryPc2Cfg 0 ∧
    ¬ IsDeadlockedSubsystemProgress AbBaMultiPcSpuriousSpinnerSys
        abBaMultiPcDeadlockedCfg (fun t => t = 0 ∨ t = 1) := by
  have hwake : AbBaMultiPcSpuriousSpinnerSys.stepBy 0
      abBaMultiPcDeadlockedCfg abBaMultiPcWoken0Cfg :=
    Or.inr ⟨⟨1, 0⟩, 1, 1, rfl, rfl⟩
  have hstep2 : AbBaMultiPcSpuriousSpinnerSys.stepBy 0
      abBaMultiPcWoken0Cfg abBaMultiPcRetryPc2Cfg :=
    Or.inl ⟨⟨⟨1, 0⟩, .enabled, true⟩, mutexMultiPcAbBody, rfl, rfl, rfl, rfl⟩
  have hreblk : AbBaMultiPcSpuriousSpinnerSys.stepBy 0
      abBaMultiPcRetryPc2Cfg abBaMultiPcReblockedCfg :=
    Or.inl ⟨⟨⟨2, 1⟩, .enabled, true⟩, mutexMultiPcAbBody, rfl, rfl, rfl, rfl⟩
  have hmp : ThreadMadeProgress abBaMultiPcDeadlockedCfg abBaMultiPcRetryPc2Cfg 0 :=
    ⟨⟨⟨1, 0⟩, .blocked (.futex 1 1), true⟩, ⟨⟨2, 1⟩, .enabled, true⟩,
      rfl, rfl, Or.inl (fun h => nomatch h)⟩
  refine ⟨abBaMultiPcDeadlockedCfg_reachable, hwake, hstep2, hreblk, hmp, ?_⟩
  intro hprogDead
  have hr : Reaches AbBaMultiPcSpuriousSpinnerSys
      abBaMultiPcDeadlockedCfg abBaMultiPcRetryPc2Cfg :=
    .tail (.tail (.refl _) hwake) hstep2
  exact hprogDead.2.2 abBaMultiPcRetryPc2Cfg hr 0 (Or.inl rfl) hmp

def AbBaMultiPcTrap (c : Config RegState) : Prop :=
  ∃ pc0 reg0 pc1 reg1 : Nat, ∃ st0 st1 : ThreadStatus,
    ((pc0 = 1 ∧ (st0 = .blocked (.futex 1 1) ∨ st0 = .enabled)) ∨
     (pc0 = 2 ∧ st0 = .enabled)) ∧
    ((pc1 = 1 ∧ (st1 = .blocked (.futex 0 1) ∨ st1 = .enabled)) ∨
     (pc1 = 2 ∧ st1 = .enabled)) ∧
    c.threads = [⟨⟨pc0, reg0⟩, st0, true⟩, ⟨⟨pc1, reg1⟩, st1, true⟩,
      ⟨⟨0, 0⟩, .enabled, false⟩] ∧
    c.mem 0 = 1 ∧
    c.mem 1 = 1

theorem abBaMultiPcTrap_preserved {cfg' : Config RegState}
    (hr : Reaches AbBaMultiPcSpuriousSpinnerSys abBaMultiPcDeadlockedCfg cfg') :
    AbBaMultiPcTrap cfg' := by
  induction hr with
  | refl =>
    exact ⟨1, 0, 1, 0, .blocked (.futex 1 1), .blocked (.futex 0 1),
      Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inl rfl⟩, rfl, rfl, rfl⟩
  | @tail c₂ c₃ tid _ hstep ih =>
    cases ih with
    | intro pc0 hr1 =>
      cases hr1 with
      | intro reg0 hr2 =>
        cases hr2 with
        | intro pc1 hr3 =>
          cases hr3 with
          | intro reg1 hr4 =>
            cases hr4 with
            | intro st0 hr5 =>
              cases hr5 with
              | intro st1 htrap =>
                have hp0 := htrap.1
                have hp1 := htrap.2.1
                have hth := htrap.2.2.1
                have hm0 := htrap.2.2.2.1
                have hm1 := htrap.2.2.2.2
                cases hstep with
                | inl hp =>
                  cases hp with
                  | intro e hrest =>
                    cases hrest with
                    | intro body hb =>
                      have hget := hb.1
                      have hprog := hb.2.2.1
                      have hc3 := hb.2.2.2
                      subst hc3
                      rw [hth] at hget
                      cases tid with
                      | zero =>
                        injection hget with he; subst he
                        injection hprog with hbd; subst hbd
                        cases hp0 with
                        | inl h1 =>
                          have hpc0 := h1.1; subst hpc0
                          change AbBaMultiPcTrap
                            (evalInstr 0 ⟨1, reg0⟩ true (.futexWaitEnter 1 2 3) c₂)
                          rw [eval_futexWaitEnter]
                          exact ⟨2, reg0 + 1, pc1, reg1, .enabled, st1,
                            Or.inr ⟨rfl, rfl⟩, hp1, by dsimp; rw [hth]; rfl, hm0, hm1⟩
                        | inr h2 =>
                          have hpc0 := h2.1; subst hpc0
                          change AbBaMultiPcTrap
                            (evalInstr 0 ⟨2, reg0⟩ true (.futexRetryAcquire 1 1 3) c₂)
                          rw [eval_futexRetryAcquire, hm1]
                          exact ⟨1, reg0, pc1, reg1, .blocked (.futex 1 1), st1,
                            Or.inl ⟨rfl, Or.inl rfl⟩, hp1, by dsimp; rw [hth]; rfl, hm0, hm1⟩
                      | succ t1 =>
                        cases t1 with
                        | zero =>
                          injection hget with he; subst he
                          injection hprog with hbd; subst hbd
                          cases hp1 with
                          | inl h1 =>
                            have hpc1 := h1.1; subst hpc1
                            change AbBaMultiPcTrap
                              (evalInstr 1 ⟨1, reg1⟩ true (.futexWaitEnter 0 2 3) c₂)
                            rw [eval_futexWaitEnter]
                            exact ⟨pc0, reg0, 2, reg1 + 1, st0, .enabled,
                              hp0, Or.inr ⟨rfl, rfl⟩, by dsimp; rw [hth]; rfl, hm0, hm1⟩
                          | inr h2 =>
                            have hpc1 := h2.1; subst hpc1
                            change AbBaMultiPcTrap
                              (evalInstr 1 ⟨2, reg1⟩ true (.futexRetryAcquire 0 1 3) c₂)
                            rw [eval_futexRetryAcquire, hm0]
                            exact ⟨pc0, reg0, 1, reg1, st0, .blocked (.futex 0 1),
                              hp0, Or.inl ⟨rfl, Or.inl rfl⟩, by dsimp; rw [hth]; rfl, hm0, hm1⟩
                        | succ t2 =>
                          cases t2 with
                          | zero =>
                            injection hget with he; subst he
                            injection hprog with hbd; subst hbd
                            exact ⟨pc0, reg0, pc1, reg1, st0, st1, hp0, hp1, hth, hm0, hm1⟩
                          | succ _ => nomatch hprog
                | inr hw =>
                  cases hw with
                  | intro st hrw1 =>
                    cases hrw1 with
                    | intro addr hrw2 =>
                      cases hrw2 with
                      | intro exp hwk =>
                        have hget := hwk.1
                        have hc3 := hwk.2
                        subst hc3
                        rw [hth] at hget
                        cases tid with
                        | zero =>
                          injection hget with he
                          injection he with hst hstEq
                          subst hst
                          cases hp0 with
                          | inl h1 =>
                            have hpc0 := h1.1; subst hpc0
                            exact ⟨1, reg0, pc1, reg1, .enabled, st1,
                              Or.inl ⟨rfl, Or.inr rfl⟩, hp1, by dsimp; rw [hth]; rfl, hm0, hm1⟩
                          | inr h2 =>
                            rw [h2.2] at hstEq; nomatch hstEq
                        | succ t1 =>
                          cases t1 with
                          | zero =>
                            injection hget with he
                            injection he with hst hstEq
                            subst hst
                            cases hp1 with
                            | inl h1 =>
                              have hpc1 := h1.1; subst hpc1
                              exact ⟨pc0, reg0, 1, reg1, st0, .enabled,
                                hp0, Or.inl ⟨rfl, Or.inr rfl⟩, by dsimp; rw [hth]; rfl, hm0, hm1⟩
                            | inr h2 =>
                              rw [h2.2] at hstEq; nomatch hstEq
                          | succ t2 =>
                            cases t2 with
                            | zero =>
                              injection hget with he; nomatch he
                            | succ _ => nomatch hget

theorem abBaMultiPcSpinner_T2_always_enabled {cfg : Config RegState}
    (hr : Reachable AbBaMultiPcSpuriousSpinnerSys cfg) :
    listGet? cfg.threads 2 = some ⟨⟨0, 0⟩, .enabled, false⟩ := by
  change Reaches AbBaMultiPcSpuriousSpinnerSys AbBaMultiPcSpuriousSpinnerSys.init cfg at hr
  induction hr with
  | refl => rfl
  | @tail c₂ c₃ tid _ hstep ih =>
    cases hstep with
    | inl hp =>
      cases hp with
      | intro e hrest =>
        cases hrest with
        | intro body hb =>
          rw [hb.2.2.2]
          cases Decidable.em (tid = 2) with
          | inl heq =>
            subst heq
            injection hb.2.2.1 with hbd; subst hbd
            exact ih
          | inr hne =>
            exact evalInstr_preserves_other_enabled hne ih rfl
    | inr hw =>
      cases hw with
      | intro st hr1 =>
        cases hr1 with
        | intro addr hr2 =>
          cases hr2 with
          | intro exp hwk =>
            rw [hwk.2]
            have hne : tid ≠ 2 := by
              intro heq; subst heq
              have hsame := listGet_unique hwk.1 ih
              nomatch hsame
            rw [listSet_other hne]
            exact ih

/-- Master 4-Way Separation Theorem (`multiPcSpuriousRetry_caught_by_waitEpisode`):
in `AbBaMultiPcSpuriousSpinnerSys` (2-PC `futex_wait` retry loop incrementing `reg`
+ demonic OS spurious wakeups + background spinner `T2`):
1. `GlobalDeadlockFree` falsely holds (masked by `T2`),
2. Naive `IsDeadlockedSubsystem` (`AlwaysIsBlocked`) fails (broken by spurious wakeup),
3. the naive `IsDeadlockedSubsystemProgress` (`localState ≠ localState`) fails
   (broken by `pc=1 -> pc=2`, `reg -> reg + 1` retry step!), and
4. `IsDeadlockedSubsystemWaitEpisode` **catches** `{0, 1}` across ALL reachable
   states (`¬ SubsystemDeadlockFreeWaitEpisode`)! -/
theorem multiPcSpuriousRetry_caught_by_waitEpisode :
    GlobalDeadlockFree AbBaMultiPcSpuriousSpinnerSys ∧
    ¬ IsDeadlockedSubsystem AbBaMultiPcSpuriousSpinnerSys abBaMultiPcDeadlockedCfg
        (fun t => t = 0 ∨ t = 1) ∧
    ¬ IsDeadlockedSubsystemProgress AbBaMultiPcSpuriousSpinnerSys abBaMultiPcDeadlockedCfg
        (fun t => t = 0 ∨ t = 1) ∧
    IsDeadlockedSubsystemWaitEpisode AbBaMultiPcSpuriousSpinnerSys abBaMultiPcDeadlockedCfg
        (fun t => t = 0 ∨ t = 1) ∧
    ¬ SubsystemDeadlockFreeWaitEpisode AbBaMultiPcSpuriousSpinnerSys := by
  have hgdf : GlobalDeadlockFree AbBaMultiPcSpuriousSpinnerSys := by
    intro cfg hr hgdl
    have h2 := abBaMultiPcSpinner_T2_always_enabled hr
    exact hgdl.2.1 2 ⟨⟨⟨0, 0⟩, .enabled, false⟩, h2, rfl⟩
  have hnnaive : ¬ IsDeadlockedSubsystem AbBaMultiPcSpuriousSpinnerSys
      abBaMultiPcDeadlockedCfg (fun t => t = 0 ∨ t = 1) := by
    intro hsub
    have hwake : AbBaMultiPcSpuriousSpinnerSys.stepBy 0
        abBaMultiPcDeadlockedCfg abBaMultiPcWoken0Cfg :=
      Or.inr ⟨⟨1, 0⟩, 1, 1, rfl, rfl⟩
    have hb0 := hsub.2 abBaMultiPcWoken0Cfg (.tail (.refl _) hwake) 0 (Or.inl rfl)
    cases hb0 with
    | intro e hrest =>
      cases hrest with
      | intro r hbr =>
        injection hbr.1 with heq; subst heq; nomatch hbr.2
  have hweDead : IsDeadlockedSubsystemWaitEpisode AbBaMultiPcSpuriousSpinnerSys
      abBaMultiPcDeadlockedCfg (fun t => t = 0 ∨ t = 1) := by
    refine ⟨⟨0, Or.inl rfl⟩, ?_, ?_⟩
    · intro t ht
      cases ht with
      | inl h0 => subst h0; exact ⟨⟨⟨1, 0⟩, .blocked (.futex 1 1), true⟩, rfl, rfl, fun h => nomatch h⟩
      | inr h1 => subst h1; exact ⟨⟨⟨1, 0⟩, .blocked (.futex 0 1), true⟩, rfl, rfl, fun h => nomatch h⟩
    · intro cfg' hr t ht hex
      cases abBaMultiPcTrap_preserved hr with
      | intro pc0 hr1 =>
        cases hr1 with
        | intro reg0 hr2 =>
          cases hr2 with
          | intro pc1 hr3 =>
            cases hr3 with
            | intro reg1 hr4 =>
              cases hr4 with
              | intro st0 hr5 =>
                cases hr5 with
                | intro st1 htrap =>
                  cases hex with
                  | intro e' he' =>
                    have hget' := he'.1
                    rw [htrap.2.2.1] at hget'
                    cases ht with
                    | inl h0 =>
                      subst h0
                      injection hget' with hee; subst hee
                      cases he'.2 with
                      | inl hf => nomatch hf
                      | inr hterm =>
                        dsimp at hterm
                        cases htrap.1 with
                        | inl c1 =>
                          cases c1.2 with
                          | inl hs => rw [hs] at hterm; nomatch hterm
                          | inr hs => rw [hs] at hterm; nomatch hterm
                        | inr c2 => rw [c2.2] at hterm; nomatch hterm
                    | inr h1 =>
                      subst h1
                      injection hget' with hee; subst hee
                      cases he'.2 with
                      | inl hf => nomatch hf
                      | inr hterm =>
                        dsimp at hterm
                        cases htrap.2.1 with
                        | inl c1 =>
                          cases c1.2 with
                          | inl hs => rw [hs] at hterm; nomatch hterm
                          | inr hs => rw [hs] at hterm; nomatch hterm
                        | inr c2 => rw [c2.2] at hterm; nomatch hterm
  exact ⟨hgdf, hnnaive, multiPcSpuriousRetry_breaks_localState_progress.2.2.2.2.2,
    hweDead,
    fun hsdf => hsdf abBaMultiPcDeadlockedCfg abBaMultiPcDeadlockedCfg_reachable _ hweDead⟩

/-- Positive non-vacuity of `IsDeadlockedSubsystemWaitEpisode`:
a healthy 2-PC mutex waiter (`T1` in `MutexMultiPcSpuriousSys`) enters its wait
episode at `pc=1`, gets woken when `T0` unlocks, runs `pc=1 -> pc=2` (`reg=1`,
still `inWaitEpisode = true`), and then acquires at `pc=2 -> pc=3` clearing
`inWaitEpisode := false`, so `ExitedWaitEpisode` holds and `{1}` is NOT
deadlocked! -/
def mutexMultiPcOnceBody : Nat → ConcInstr
  | 0 => .futexWaitEnter 0 2 3
  | 1 => .futexWaitEnter 0 2 3
  | 2 => .futexRetryAcquire 0 1 3
  | 3 => .futexUnlock 0 4
  | _ => .halt

def MutexMultiPcProg : ConcProg := [mutexMultiPcOnceBody, mutexMultiPcOnceBody]
noncomputable def MutexMultiPcSpuriousSys : ConcSystem RegState :=
  mkSpuriousProgSystem MutexMultiPcProg

noncomputable def mpcStep1 : Config RegState :=
  evalInstr 0 ⟨0, 0⟩ false (.futexWaitEnter 0 2 3) MutexMultiPcSpuriousSys.init

noncomputable def mpcBlockedCfg : Config RegState :=
  evalInstr 1 ⟨0, 0⟩ false (.futexWaitEnter 0 2 3) mpcStep1

noncomputable def mpcAfterUnlockCfg : Config RegState :=
  evalInstr 0 ⟨3, 0⟩ false (.futexUnlock 0 4) mpcBlockedCfg

noncomputable def mpcAfterResumeCfg : Config RegState :=
  evalInstr 1 ⟨0, 0⟩ true (.futexWaitEnter 0 2 3) mpcAfterUnlockCfg

noncomputable def mpcAfterAcquireCfg : Config RegState :=
  evalInstr 1 ⟨2, 1⟩ true (.futexRetryAcquire 0 1 3) mpcAfterResumeCfg

theorem healthyMultiPcWaiter_not_deadlockedWaitEpisode :
    Reachable MutexMultiPcSpuriousSys mpcBlockedCfg ∧
    InWaitEpisode mpcBlockedCfg 1 ∧
    ¬ IsDeadlockedSubsystemWaitEpisode MutexMultiPcSpuriousSys
        mpcBlockedCfg (fun t => t = 1) := by
  have hr1 : Reaches MutexMultiPcSpuriousSys MutexMultiPcSpuriousSys.init mpcStep1 :=
    .tail (.refl _) (Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, mutexMultiPcOnceBody, rfl, rfl, rfl, rfl⟩)
  have hr2 : Reachable MutexMultiPcSpuriousSys mpcBlockedCfg :=
    .tail hr1 (Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, mutexMultiPcOnceBody, rfl, rfl, rfl, rfl⟩)
  refine ⟨hr2, ⟨⟨⟨0, 0⟩, .blocked (.futex 0 1), true⟩, rfl, rfl, fun h => nomatch h⟩, ?_⟩
  intro hdead
  have hs1 : Reaches MutexMultiPcSpuriousSys mpcBlockedCfg mpcAfterUnlockCfg :=
    .tail (.refl _) (Or.inl ⟨⟨⟨3, 0⟩, .enabled, false⟩, mutexMultiPcOnceBody, rfl, rfl, rfl, rfl⟩)
  have hs2 : Reaches MutexMultiPcSpuriousSys mpcBlockedCfg mpcAfterResumeCfg :=
    .tail hs1 (Or.inl ⟨⟨⟨0, 0⟩, .enabled, true⟩, mutexMultiPcOnceBody, rfl, rfl, rfl, rfl⟩)
  have hs3 : Reaches MutexMultiPcSpuriousSys mpcBlockedCfg mpcAfterAcquireCfg :=
    .tail hs2 (Or.inl ⟨⟨⟨2, 1⟩, .enabled, true⟩, mutexMultiPcOnceBody, rfl, rfl, rfl, rfl⟩)
  exact hdead.2.2 mpcAfterAcquireCfg hs3 1 rfl
    ⟨⟨⟨3, 1⟩, .enabled, false⟩, rfl, Or.inl rfl⟩

/-- Non-vacuous instantiation of `wellFormedFutexProg_spuriousWakeNonRescuing`
and `subsystemDeadlockFreeWaitEpisode_implies_globalDeadlockFree` on a genuine
2-thread 2-PC spurious-wakeup system (`AbBaMultiPcSpurious2Sys`):
proves `SpuriousWakeNonRescuing`, reaches `IsGlobalDeadlock`, and derives
`¬ SubsystemDeadlockFreeWaitEpisode` directly from the implication theorem! -/
theorem abBaMultiPc2_wellFormedFutex : WellFormedFutexProg AbBaMultiPc2Prog := by
  intro t body hget pc
  cases t with
  | zero =>
    injection hget with hb; subst hb
    cases pc with
    | zero => exact True.intro
    | succ k1 =>
      cases k1 with
      | zero => rfl
      | succ k2 =>
        cases k2 with
        | zero => rfl
        | succ k3 =>
          cases k3 with
          | zero => exact True.intro
          | succ k4 => cases k4 <;> exact True.intro
  | succ t1 =>
    cases t1 with
    | zero =>
      injection hget with hb; subst hb
      cases pc with
      | zero => exact True.intro
      | succ k1 =>
        cases k1 with
        | zero => rfl
        | succ k2 =>
          cases k2 with
          | zero => rfl
          | succ k3 =>
            cases k3 with
            | zero => exact True.intro
            | succ k4 => cases k4 <;> exact True.intro
    | succ _ => nomatch hget

noncomputable def abBa2MpcStep1 : Config RegState :=
  evalInstr 0 ⟨0, 0⟩ false (.futexLock 0 1) AbBaMultiPcSpurious2Sys.init

noncomputable def abBa2MpcStep2 : Config RegState :=
  evalInstr 1 ⟨0, 0⟩ false (.futexLock 1 1) abBa2MpcStep1

noncomputable def abBa2MpcStep3 : Config RegState :=
  evalInstr 0 ⟨1, 0⟩ false (.futexWaitEnter 1 2 3) abBa2MpcStep2

noncomputable def abBa2MpcDeadlockedCfg : Config RegState :=
  evalInstr 1 ⟨1, 0⟩ false (.futexWaitEnter 0 2 3) abBa2MpcStep3

theorem abBaMultiPc2_spurious_implication_instantiation :
    SpuriousWakeNonRescuing AbBaMultiPcSpurious2Sys ∧
    ¬ GlobalDeadlockFree AbBaMultiPcSpurious2Sys ∧
    ¬ SubsystemDeadlockFreeWaitEpisode AbBaMultiPcSpurious2Sys := by
  have hnr : SpuriousWakeNonRescuing AbBaMultiPcSpurious2Sys :=
    wellFormedFutexProg_spuriousWakeNonRescuing abBaMultiPc2_wellFormedFutex
  have hreach : Reachable AbBaMultiPcSpurious2Sys abBa2MpcDeadlockedCfg := by
    have r0 : Reaches AbBaMultiPcSpurious2Sys
        AbBaMultiPcSpurious2Sys.init AbBaMultiPcSpurious2Sys.init := .refl _
    have r1 : Reaches AbBaMultiPcSpurious2Sys
        AbBaMultiPcSpurious2Sys.init abBa2MpcStep1 :=
      .tail r0 (Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, mutexMultiPcAbBody, rfl, rfl, rfl, rfl⟩)
    have r2 : Reaches AbBaMultiPcSpurious2Sys
        AbBaMultiPcSpurious2Sys.init abBa2MpcStep2 :=
      .tail r1 (Or.inl ⟨⟨⟨0, 0⟩, .enabled, false⟩, mutexMultiPcBaBody, rfl, rfl, rfl, rfl⟩)
    have r3 : Reaches AbBaMultiPcSpurious2Sys
        AbBaMultiPcSpurious2Sys.init abBa2MpcStep3 :=
      .tail r2 (Or.inl ⟨⟨⟨1, 0⟩, .enabled, false⟩, mutexMultiPcAbBody, rfl, rfl, rfl, rfl⟩)
    exact .tail r3 (Or.inl ⟨⟨⟨1, 0⟩, .enabled, false⟩, mutexMultiPcBaBody, rfl, rfl, rfl, rfl⟩)
  have hgdl : IsGlobalDeadlock abBa2MpcDeadlockedCfg := by
    refine ⟨⟨0, ⟨⟨⟨1, 0⟩, .blocked (.futex 1 1), true⟩, rfl⟩, ?_⟩, ?_, ?_⟩
    · intro ht
      cases ht with
      | intro e he => injection he.1 with hee; subst hee; nomatch he.2
    · intro t hen
      cases hen with
      | intro e he =>
        have hget := he.1
        cases t with
        | zero => injection hget with hee; subst hee; nomatch he.2
        | succ t1 =>
          cases t1 with
          | zero => injection hget with hee; subst hee; nomatch he.2
          | succ _ => nomatch hget
    · intro t hact
      cases hact with
      | intro e he =>
        cases t with
        | zero =>
          injection he with hee; subst hee
          exact Or.inl ⟨_, rfl, rfl, fun h => nomatch h⟩
        | succ t1 =>
          cases t1 with
          | zero =>
            injection he with hee; subst hee
            exact Or.inl ⟨_, rfl, rfl, fun h => nomatch h⟩
          | succ _ => nomatch he
  have hngdf : ¬ GlobalDeadlockFree AbBaMultiPcSpurious2Sys :=
    fun hgdf => hgdf abBa2MpcDeadlockedCfg hreach hgdl
  exact ⟨hnr, hngdf,
    fun hsdf => hngdf (subsystemDeadlockFreeWaitEpisode_implies_globalDeadlockFree hnr hsdf)⟩

end Anneal.ConcurrencySeparation
