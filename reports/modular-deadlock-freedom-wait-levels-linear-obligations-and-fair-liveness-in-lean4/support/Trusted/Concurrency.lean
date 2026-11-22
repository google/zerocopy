-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Trusted.Concurrency

abbrev ThreadId : Type := Nat
abbrev Addr : Type := Nat
abbrev Val : Type := Nat

inductive WaitReason where
  | futex (addr : Addr) (expected : Val)
  | park
  | join (target : ThreadId)

inductive ThreadStatus where
  | enabled
  | blocked (reason : WaitReason)
  | terminated

noncomputable def listGet? : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

noncomputable def listSet : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

/-- Per-thread runtime entry: carries `localState`, scheduler
`status`, and an explicit `inWaitEpisode : Bool` marker entered when entering a
blocking synchronization wait loop, preserved across arbitrary multi-PC retry,
spin, and OS spurious-wakeup steps, and cleared ONLY on genuine acquisition /
wait-exit or `.terminated`. -/
structure ThreadEntry (L : Type) where
  localState : L
  status : ThreadStatus
  inWaitEpisode : Bool

structure Config (L : Type) where
  threads : List (ThreadEntry L)
  mem : Addr → Val
  parkToken : ThreadId → Bool

def ThreadActive (cfg : Config L) (t : ThreadId) : Prop :=
  ∃ e : ThreadEntry L, listGet? cfg.threads t = some e

def IsEnabled (cfg : Config L) (t : ThreadId) : Prop :=
  ∃ e : ThreadEntry L, listGet? cfg.threads t = some e ∧ e.status = .enabled

def IsBlocked (cfg : Config L) (t : ThreadId) : Prop :=
  ∃ e : ThreadEntry L, ∃ r : WaitReason,
    listGet? cfg.threads t = some e ∧ e.status = .blocked r

def IsBlockedOn (cfg : Config L) (t : ThreadId) (r : WaitReason) : Prop :=
  ∃ e : ThreadEntry L, listGet? cfg.threads t = some e ∧ e.status = .blocked r

def IsTerminated (cfg : Config L) (t : ThreadId) : Prop :=
  ∃ e : ThreadEntry L, listGet? cfg.threads t = some e ∧ e.status = .terminated

def AllTerminated (cfg : Config L) : Prop :=
  ∀ (t : ThreadId) (e : ThreadEntry L),
    listGet? cfg.threads t = some e → e.status = .terminated

/-- Thread `t` is currently inside an unresolved blocking wait episode
(`inWaitEpisode = true` and not terminated). -/
def InWaitEpisode (cfg : Config L) (t : ThreadId) : Prop :=
  ∃ e : ThreadEntry L,
    listGet? cfg.threads t = some e ∧
    e.inWaitEpisode = true ∧
    e.status ≠ .terminated

/-- Thread `t` has exited its blocking wait episode (genuine acquisition /
wait-exit clearing `inWaitEpisode := false`, or thread termination). -/
def ExitedWaitEpisode (cfg' : Config L) (t : ThreadId) : Prop :=
  ∃ e : ThreadEntry L,
    listGet? cfg'.threads t = some e ∧
    (e.inWaitEpisode = false ∨ e.status = .terminated)

/-- Concurrent transition system: cleanly separates genuinely
enabled-gated program transitions (`progStepBy`) from demonic OS spurious
wakeups on blocked waiters (`osSpuriousWakeBy`). -/
structure ConcSystem (L : Type) where
  init : Config L
  progStepBy : ThreadId → Config L → Config L → Prop
  osSpuriousWakeBy : ThreadId → Config L → Config L → Prop
  progStepRequiresEnabled :
    ∀ t c₁ c₂, progStepBy t c₁ c₂ → IsEnabled c₁ t
  osWakeRequiresBlockedWait :
    ∀ t c₁ c₂, osSpuriousWakeBy t c₁ c₂ →
      IsBlocked c₁ t ∧ InWaitEpisode c₁ t

def ConcSystem.stepBy {L : Type} (sys : ConcSystem L) (t : ThreadId)
    (c₁ c₂ : Config L) : Prop :=
  sys.progStepBy t c₁ c₂ ∨ sys.osSpuriousWakeBy t c₁ c₂

def NoSpuriousWakes (sys : ConcSystem L) : Prop :=
  ∀ t c₁ c₂, ¬ sys.osSpuriousWakeBy t c₁ c₂

theorem optionSomeInj {α : Type} {a b : α} (h : some a = some b) : a = b :=
  match h with
  | rfl => rfl

theorem statusEnabledNeTerminated {s : ThreadStatus}
    (h1 : s = .enabled) (h2 : s = .terminated) : False :=
  match Eq.trans (Eq.symm h1) h2 with
  | h => nomatch h

theorem statusBlockedNeTerminated {s : ThreadStatus} {r : WaitReason}
    (h1 : s = .blocked r) (h2 : s = .terminated) : False :=
  match Eq.trans (Eq.symm h1) h2 with
  | h => nomatch h

theorem stepRequiresNotTerminated {L : Type} (sys : ConcSystem L)
    (t : ThreadId) (c₁ c₂ : Config L) (h : sys.stepBy t c₁ c₂) :
    ThreadActive c₁ t ∧ ¬ IsTerminated c₁ t :=
  match h with
  | Or.inl hp =>
      match sys.progStepRequiresEnabled t c₁ c₂ hp with
      | ⟨e, hget, hen⟩ =>
          ⟨⟨e, hget⟩, fun ⟨e', hget', hterm⟩ =>
            let heq : e = e' := optionSomeInj (Eq.trans (Eq.symm hget) hget')
            statusEnabledNeTerminated hen
              (Eq.trans (congrArg ThreadEntry.status heq) hterm)⟩
  | Or.inr hw =>
      match (sys.osWakeRequiresBlockedWait t c₁ c₂ hw).1 with
      | ⟨e, _, hget, hblk⟩ =>
          ⟨⟨e, hget⟩, fun ⟨e', hget', hterm⟩ =>
            let heq : e = e' := optionSomeInj (Eq.trans (Eq.symm hget) hget')
            statusBlockedNeTerminated hblk
              (Eq.trans (congrArg ThreadEntry.status heq) hterm)⟩

inductive Reaches (sys : ConcSystem L) : Config L → Config L → Prop where
  | refl (c : Config L) : Reaches sys c c
  | tail {c₁ c₂ c₃ : Config L} {t : ThreadId} :
      Reaches sys c₁ c₂ →
      sys.stepBy t c₂ c₃ →
      Reaches sys c₁ c₃

def Reachable (sys : ConcSystem L) (cfg : Config L) : Prop :=
  Reaches sys sys.init cfg

/-- Explicit global deadlock predicate: at least one active thread has
not terminated, NO thread is `.enabled` (so no `progStepBy` can execute), and
every active thread is either inside an unresolved wait episode or terminated. -/
def IsGlobalDeadlock (cfg : Config L) : Prop :=
  (∃ t : ThreadId, ThreadActive cfg t ∧ ¬ IsTerminated cfg t) ∧
  (∀ t : ThreadId, ¬ IsEnabled cfg t) ∧
  (∀ t : ThreadId, ThreadActive cfg t → InWaitEpisode cfg t ∨ IsTerminated cfg t)

def GlobalDeadlockFree (sys : ConcSystem L) : Prop :=
  ∀ cfg : Config L, Reachable sys cfg → ¬ IsGlobalDeadlock cfg

/-- Non-tautological 1-step spurious-wakeup closure condition:
a system satisfies `SpuriousWakeNonRescuing` when there exists a state trap
`Trap` covering every reachable `IsGlobalDeadlock` state that is 1-step
inductive under `sys.stepBy` (`progStepBy ∨ osSpuriousWakeBy`) and preserves
every waiting thread's wait episode. Holds automatically when `NoSpuriousWakes`
holds AND holds for well-formed blocking programs WITH `OsSpuriousFutexWake`
(contended futex words prevent spurious wakeups from escaping wait episodes). -/
def SpuriousWakeNonRescuing (sys : ConcSystem L) : Prop :=
  ∃ Trap : Config L → Prop,
    (∀ cfg : Config L, Reachable sys cfg → IsGlobalDeadlock cfg → Trap cfg) ∧
    (∀ (t : ThreadId) (c₁ c₂ : Config L),
      Trap c₁ → sys.stepBy t c₁ c₂ →
      Trap c₂ ∧
      (∀ u : ThreadId, InWaitEpisode c₁ u → InWaitEpisode c₂ u))

/-- Naive Wave-2 status-based subsystem deadlock predicate (`AlwaysIsBlocked`).
Refuted under demonic OS spurious `futex_wait` wakeups. -/
def IsDeadlockedSubsystem (sys : ConcSystem L) (cfg : Config L)
    (S : ThreadId → Prop) : Prop :=
  (∃ t : ThreadId, S t) ∧
  (∀ cfg' : Config L, Reaches sys cfg cfg' →
    ∀ t : ThreadId, S t → IsBlocked cfg' t)

def SubsystemDeadlockFree (sys : ConcSystem L) : Prop :=
  ∀ cfg : Config L, Reachable sys cfg →
    ∀ S : ThreadId → Prop, ¬ IsDeadlockedSubsystem sys cfg S

/-- Wave-3 `localState`-change progress predicate (`ThreadMadeProgress`),
preserved here explicitly so `multiPcSpuriousRetry_breaks_localState_progress`
proves its refutation on 2-PC `futex_wait` retry loops (`pc=1 -> pc=2 -> pc=1`
incrementing a retry counter). -/
def ThreadMadeProgress (cfg cfg' : Config L) (t : ThreadId) : Prop :=
  ∃ e e' : ThreadEntry L,
    listGet? cfg.threads t = some e ∧
    listGet? cfg'.threads t = some e' ∧
    (e'.localState ≠ e.localState ∨ e'.status = .terminated)

def IsDeadlockedSubsystemProgress (sys : ConcSystem L) (cfg : Config L)
    (S : ThreadId → Prop) : Prop :=
  (∃ t : ThreadId, S t) ∧
  (∀ t : ThreadId, S t → IsBlocked cfg t) ∧
  (∀ cfg' : Config L, Reaches sys cfg cfg' →
    ∀ t : ThreadId, S t → ¬ ThreadMadeProgress cfg cfg' t)

def SubsystemDeadlockFreeProgress (sys : ConcSystem L) : Prop :=
  ∀ cfg : Config L, Reachable sys cfg →
    ∀ S : ThreadId → Prop, ¬ IsDeadlockedSubsystemProgress sys cfg S

/-- Multi-PC wait-episode subsystem deadlock predicate:
a non-empty set `S` of threads currently in an unresolved wait episode at `cfg`
(`InWaitEpisode cfg t`) such that along NO reachable continuation
`Reaches sys cfg cfg'` does any `t ∈ S` exit its wait episode
(`¬ ExitedWaitEpisode cfg' t`), even across arbitrary multi-PC retry loops,
retry-counter increments, background spinners, and demonic OS spurious wakeups. -/
def IsDeadlockedSubsystemWaitEpisode (sys : ConcSystem L) (cfg : Config L)
    (S : ThreadId → Prop) : Prop :=
  (∃ t : ThreadId, S t) ∧
  (∀ t : ThreadId, S t → InWaitEpisode cfg t) ∧
  (∀ cfg' : Config L, Reaches sys cfg cfg' →
    ∀ t : ThreadId, S t → ¬ ExitedWaitEpisode cfg' t)

def SubsystemDeadlockFreeWaitEpisode (sys : ConcSystem L) : Prop :=
  ∀ cfg : Config L, Reachable sys cfg →
    ∀ S : ThreadId → Prop, ¬ IsDeadlockedSubsystemWaitEpisode sys cfg S

def ClosedBlockedTrap (sys : ConcSystem L) (cfg : Config L)
    (S : ThreadId → Prop) : Prop :=
  (∃ t : ThreadId, S t) ∧
  (∀ t : ThreadId, S t → IsBlocked cfg t) ∧
  (∀ (c₁ c₂ : Config L) (tid : ThreadId),
    Reaches sys cfg c₁ →
    (∀ t : ThreadId, S t → IsBlocked c₁ t) →
    sys.stepBy tid c₁ c₂ →
    (∀ t : ThreadId, S t → IsBlocked c₂ t))

def IsCycleAux (edge : ThreadId → ThreadId → Prop) (head : ThreadId)
    (cur : ThreadId) (nodes : List ThreadId) : Prop :=
  @List.rec ThreadId (fun _ => ThreadId → Prop)
    (fun c => edge c head)
    (fun nxt _ ih c => edge c nxt ∧ ih nxt)
    nodes cur

def HasBlockedCycle (edge : Config L → ThreadId → ThreadId → Prop)
    (cfg : Config L) : List ThreadId → Prop
  | [] => False
  | hd :: tl =>
      (∀ u : ThreadId, u ∈ (hd :: tl) → IsBlocked cfg u) ∧
      IsCycleAux (edge cfg) hd hd tl

def NoBlockedCycle (edge : Config L → ThreadId → ThreadId → Prop)
    (sys : ConcSystem L) : Prop :=
  ∀ cfg : Config L, Reachable sys cfg →
    ∀ cycle : List ThreadId, ¬ HasBlockedCycle edge cfg cycle

structure Run (L : Type) where
  trace : Nat → Config L
  stepAt : Nat → Option ThreadId

/-- Valid infinite execution: each step either takes `sys.stepBy`
(`progStepBy ∨ osSpuriousWakeBy`), or stutters (`none`) only when no thread is
enabled (so no `progStepBy` can execute; demonic OS spurious wakeups are never
required to fire). -/
def ValidRun (sys : ConcSystem L) (run : Run L) : Prop :=
  run.trace 0 = sys.init ∧
  ∀ n : Nat,
    match run.stepAt n with
    | some t => sys.stepBy t (run.trace n) (run.trace (n + 1))
    | none =>
        (∀ t : ThreadId, ¬ IsEnabled (run.trace n) t) ∧
        (∀ t c', ¬ sys.progStepBy t (run.trace n) c') ∧
        run.trace (n + 1) = run.trace n

def Eventually (P : Nat → Prop) : Prop :=
  ∃ n : Nat, P n

def EventuallyAlways (P : Nat → Prop) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → P n

def InfinitelyOften (P : Nat → Prop) : Prop :=
  ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ P n

def WeakFair (run : Run L) : Prop :=
  ∀ t : ThreadId,
    EventuallyAlways (fun n => IsEnabled (run.trace n) t) →
    InfinitelyOften (fun n => run.stepAt n = some t)

def StrongFair (run : Run L) : Prop :=
  ∀ t : ThreadId,
    InfinitelyOften (fun n => IsEnabled (run.trace n) t) →
    InfinitelyOften (fun n => run.stepAt n = some t)

def ActionWeakFair (en : Config L → ThreadId → Prop)
    (act : Config L → Config L → ThreadId → Prop) (run : Run L) : Prop :=
  ∀ t : ThreadId,
    EventuallyAlways (fun n => en (run.trace n) t) →
    InfinitelyOften (fun n =>
      run.stepAt n = some t ∧ act (run.trace n) (run.trace (n + 1)) t)

def ActionStrongFair (en : Config L → ThreadId → Prop)
    (act : Config L → Config L → ThreadId → Prop) (run : Run L) : Prop :=
  ∀ t : ThreadId,
    InfinitelyOften (fun n => en (run.trace n) t) →
    InfinitelyOften (fun n =>
      run.stepAt n = some t ∧ act (run.trace n) (run.trace (n + 1)) t)

def RunTerminates (run : Run L) : Prop :=
  Eventually (fun n => AllTerminated (run.trace n))

def UnconditionalTerminates (sys : ConcSystem L) : Prop :=
  ∀ run : Run L, ValidRun sys run → RunTerminates run

def WeakFairTerminates (sys : ConcSystem L) : Prop :=
  ∀ run : Run L, ValidRun sys run → WeakFair run → RunTerminates run

def StrongFairTerminates (sys : ConcSystem L) : Prop :=
  ∀ run : Run L, ValidRun sys run → StrongFair run → RunTerminates run

/-- Per-thread non-starvation under fairness `fair`: explicitly scoped
to a distinguished target thread `t` (distinct from whole-system `AllTerminated`
when an infinite environment contender loops forever). -/
def PerThreadStarvationFree (fair : Run L → Prop) (sys : ConcSystem L)
    (t : ThreadId) (goal : Config L → ThreadId → Prop) : Prop :=
  ∀ run : Run L, ValidRun sys run → fair run →
    Eventually (fun n => goal (run.trace n) t)

def StarvationFreeUnder (fair : Run L → Prop) (sys : ConcSystem L)
    (goal : Config L → ThreadId → Prop) : Prop :=
  ∀ run : Run L, ValidRun sys run → fair run →
    ∀ t : ThreadId, ThreadActive sys.init t →
      Eventually (fun n => goal (run.trace n) t)

structure RegState where
  pc : Nat
  reg : Val

inductive ConcInstr where
  | casLoop (addr : Addr) (expected desired : Val) (nextPc : Nat)
  | store (addr : Addr) (val : Val) (nextPc : Nat)
  | storeRegSucc (addr : Addr) (nextPc : Nat)
  | fetchAdd (addr : Addr) (nextPc : Nat)
  | awaitRegEq (addr : Addr) (nextPc : Nat)
  | futexLock (addr : Addr) (nextPc : Nat)
  | futexWaitEnter (addr : Addr) (checkPc : Nat) (acquiredPc : Nat)
  | futexRetryAcquire (addr : Addr) (waitPc : Nat) (acquiredPc : Nat)
  | futexUnlock (addr : Addr) (nextPc : Nat)
  | parkWait (nextPc : Nat)
  | unparkThread (target : ThreadId) (nextPc : Nat)
  | joinThread (target : ThreadId) (nextPc : Nat)
  | spinSelf
  | halt

abbrev ConcProg : Type := List (Nat → ConcInstr)

def memWrite (m : Addr → Val) (a : Addr) (v : Val) : Addr → Val :=
  fun x => if Nat.beq x a then v else m x

noncomputable def wakeFutexAll (addr : Addr) :
    List (ThreadEntry RegState) → List (ThreadEntry RegState)
  | [] => []
  | e :: es =>
      let e' := match e.status with
        | .blocked (.futex a _) =>
            if Nat.beq a addr then { e with status := .enabled } else e
        | _ => e
      e' :: wakeFutexAll addr es

noncomputable def wakeJoiners (doneTid : ThreadId) :
    List (ThreadEntry RegState) → List (ThreadEntry RegState)
  | [] => []
  | e :: es =>
      let e' := match e.status with
        | .blocked (.join target) =>
            if Nat.beq target doneTid then { e with status := .enabled } else e
        | _ => e
      e' :: wakeJoiners doneTid es

noncomputable def wakeParked (target : ThreadId)
    (entries : List (ThreadEntry RegState)) : List (ThreadEntry RegState) :=
  match listGet? entries target with
  | some e =>
      match e.status with
      | .blocked .park => listSet entries target { e with status := .enabled }
      | _ => entries
  | none => entries

noncomputable def evalInstr (t : ThreadId) (st : RegState) (inWait : Bool)
    (instr : ConcInstr) (c : Config RegState) : Config RegState :=
  match instr with
  | .casLoop addr expected desired nextPc =>
      if Nat.beq (c.mem addr) expected then
        { c with
          threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr desired }
      else
        c
  | .store addr val nextPc =>
      { c with
        threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩
        mem := memWrite c.mem addr val }
  | .storeRegSucc addr nextPc =>
      { c with
        threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩
        mem := memWrite c.mem addr (st.reg + 1) }
  | .fetchAdd addr nextPc =>
      let old := c.mem addr
      { c with
        threads := listSet c.threads t ⟨⟨nextPc, old⟩, .enabled, false⟩
        mem := memWrite c.mem addr (old + 1) }
  | .awaitRegEq addr nextPc =>
      if Nat.beq (c.mem addr) st.reg then
        { c with threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩ }
      else
        c
  | .futexLock addr nextPc =>
      if Nat.beq (c.mem addr) 0 then
        { c with
          threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr 1 }
      else
        { c with
          threads := listSet c.threads t
            ⟨st, .blocked (.futex addr (c.mem addr)), true⟩ }
  | .futexWaitEnter addr checkPc acquiredPc =>
      if inWait then
        { c with
          threads := listSet c.threads t
            ⟨⟨checkPc, st.reg + 1⟩, .enabled, true⟩ }
      else if Nat.beq (c.mem addr) 0 then
        { c with
          threads := listSet c.threads t ⟨⟨acquiredPc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr 1 }
      else
        { c with
          threads := listSet c.threads t
            ⟨st, .blocked (.futex addr (c.mem addr)), true⟩ }
  | .futexRetryAcquire addr waitPc acquiredPc =>
      if Nat.beq (c.mem addr) 0 then
        { c with
          threads := listSet c.threads t ⟨⟨acquiredPc, st.reg⟩, .enabled, false⟩
          mem := memWrite c.mem addr 1 }
      else
        { c with
          threads := listSet c.threads t
            ⟨⟨waitPc, st.reg⟩, .blocked (.futex addr (c.mem addr)), true⟩ }
  | .futexUnlock addr nextPc =>
      let woken := wakeFutexAll addr c.threads
      { c with
        threads := listSet woken t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩
        mem := memWrite c.mem addr 0 }
  | .parkWait nextPc =>
      if c.parkToken t then
        { c with
          threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩
          parkToken := fun u => if Nat.beq u t then false else c.parkToken u }
      else
        { c with threads := listSet c.threads t ⟨st, .blocked .park, true⟩ }
  | .unparkThread target nextPc =>
      let woken := wakeParked target c.threads
      { c with
        threads := listSet woken t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩
        parkToken := fun u => if Nat.beq u target then true else c.parkToken u }
  | .joinThread target nextPc =>
      match listGet? c.threads target with
      | some te =>
          match te.status with
          | .terminated =>
              { c with threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩ }
          | _ =>
              { c with threads := listSet c.threads t ⟨st, .blocked (.join target), true⟩ }
      | none =>
          { c with threads := listSet c.threads t ⟨⟨nextPc, st.reg⟩, .enabled, false⟩ }
  | .spinSelf => c
  | .halt =>
      let halted := listSet c.threads t ⟨st, .terminated, false⟩
      { c with threads := wakeJoiners t halted }

noncomputable def initProgThreads : ConcProg → List (ThreadEntry RegState)
  | [] => []
  | _ :: rest => ⟨⟨0, 0⟩, .enabled, false⟩ :: initProgThreads rest

def ProgStepBy (prog : ConcProg) (t : ThreadId)
    (c₁ c₂ : Config RegState) : Prop :=
  ∃ e : ThreadEntry RegState,
  ∃ body : Nat → ConcInstr,
    listGet? c₁.threads t = some e ∧
    e.status = .enabled ∧
    listGet? prog t = some body ∧
    c₂ = evalInstr t e.localState e.inWaitEpisode (body e.localState.pc) c₁

/-- Demonic OS spurious wakeup on `futex_wait`: any thread `t` blocked in
`.blocked (.futex addr exp)` inside a wait episode (`inWaitEpisode = true`) may
be spuriously woken by the kernel to `.enabled` at the same `RegState`,
preserving `inWaitEpisode = true` without modifying shared memory or park
tokens. -/
def OsSpuriousFutexWake (t : ThreadId)
    (c₁ c₂ : Config RegState) : Prop :=
  ∃ st : RegState,
  ∃ addr : Addr,
  ∃ exp : Val,
    listGet? c₁.threads t = some ⟨st, .blocked (.futex addr exp), true⟩ ∧
    c₂ = { c₁ with threads := listSet c₁.threads t ⟨st, .enabled, true⟩ }

def NoOsWake (_ : ThreadId) (_ _ : Config RegState) : Prop := False

theorem progStepRequiresEnabled (prog : ConcProg) (t : ThreadId)
    (c₁ c₂ : Config RegState) (h : ProgStepBy prog t c₁ c₂) : IsEnabled c₁ t :=
  match h with
  | ⟨e, _, hget, hen, _, _⟩ => ⟨e, hget, hen⟩

theorem osSpuriousWakeRequiresBlockedWait (t : ThreadId)
    (c₁ c₂ : Config RegState) (h : OsSpuriousFutexWake t c₁ c₂) :
    IsBlocked c₁ t ∧ InWaitEpisode c₁ t :=
  match h with
  | ⟨st, addr, exp, hget, _⟩ =>
      ⟨⟨⟨st, .blocked (.futex addr exp), true⟩, .futex addr exp, hget, rfl⟩,
       ⟨⟨st, .blocked (.futex addr exp), true⟩, hget, rfl,
         fun hterm => statusBlockedNeTerminated rfl hterm⟩⟩

theorem noOsWakeRequiresBlockedWait (t : ThreadId)
    (c₁ c₂ : Config RegState) (h : NoOsWake t c₁ c₂) :
    IsBlocked c₁ t ∧ InWaitEpisode c₁ t :=
  False.elim h

noncomputable def mkProgSystem (prog : ConcProg) : ConcSystem RegState :=
  { init := {
      threads := initProgThreads prog
      mem := fun _ => 0
      parkToken := fun _ => false }
    progStepBy := ProgStepBy prog
    osSpuriousWakeBy := NoOsWake
    progStepRequiresEnabled := progStepRequiresEnabled prog
    osWakeRequiresBlockedWait := noOsWakeRequiresBlockedWait }

noncomputable def mkSpuriousProgSystem (prog : ConcProg) : ConcSystem RegState :=
  { init := {
      threads := initProgThreads prog
      mem := fun _ => 0
      parkToken := fun _ => false }
    progStepBy := ProgStepBy prog
    osSpuriousWakeBy := OsSpuriousFutexWake
    progStepRequiresEnabled := progStepRequiresEnabled prog
    osWakeRequiresBlockedWait := osSpuriousWakeRequiresBlockedWait }

end Trusted.Concurrency
