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
import Init.Data.Nat.Bitwise.Basic
import Init.SimpLemmas
import Init.Tactics

namespace Anneal.ConcurrentSpecs

/-! ### 1. Safe-Rust `std::sync::Mutex` Poisoning + `mem::forget(guard)` + `get_mut`/`into_inner` -/

/-- Physical state of `std::sync::Mutex<T>` (repair, matching
`library/std/src/sync/poison/mutex.rs`): preserves the underlying `UnsafeCell<T>`
value `val : T` inside `.locked val holderWasPanicking` so safe `mem::forget` on
`MutexGuard` followed by `Mutex::get_mut(&mut self)` / `Mutex::into_inner(self)`
(`library/std/src/sync/poison/mutex.rs:631-667`) observes `val` directly! -/
inductive MutexPhysState (T : Type) where
  | unlockedOk (val : T)
  | unlockedPoisoned (val : T)
  | locked (val : T) (holderWasPanicking : Bool)

def MutexInv {T : Type} (OkInv PoisonInv : T → Prop) :
    MutexPhysState T → Prop
  | .unlockedOk v => OkInv v
  | .unlockedPoisoned v => PoisonInv v
  | .locked _ _ => True

/-- Idealized proof-gated `MutexStep` (where `clearPoison`
hypothetically demanded `OkInv v`, `locked true` unwind was omitted, and
`mem::forget(guard)` + `get_mut`/`into_inner` was omitted). -/
inductive MutexStep {T : Type} (OkInv PoisonInv : T → Prop) :
    MutexPhysState T → MutexPhysState T → Prop where
  | acquireOk (v : T) (panicking : Bool) :
      MutexStep OkInv PoisonInv (.unlockedOk v) (.locked v panicking)
  | acquirePoisoned (v : T) (panicking : Bool) :
      MutexStep OkInv PoisonInv (.unlockedPoisoned v) (.locked v panicking)
  | unlockCleanOk (v : T) (panicking : Bool) (v' : T) :
      OkInv v' →
      MutexStep OkInv PoisonInv (.locked v panicking) (.unlockedOk v')
  | unlockKeepPoison (v : T) (panicking : Bool) (v' : T) :
      PoisonInv v' →
      MutexStep OkInv PoisonInv (.locked v panicking) (.unlockedPoisoned v')
  | unlockUnwindPoison (v vBroken : T) :
      PoisonInv vBroken →
      MutexStep OkInv PoisonInv (.locked v false) (.unlockedPoisoned vBroken)
  | clearPoison (v : T) :
      OkInv v →
      MutexStep OkInv PoisonInv (.unlockedPoisoned v) (.unlockedOk v)

theorem mutexStep_preserves_inv {T : Type} {OkInv PoisonInv : T → Prop}
    {s₁ s₂ : MutexPhysState T}
    (_hinv : MutexInv OkInv PoisonInv s₁)
    (hstep : MutexStep OkInv PoisonInv s₁ s₂) :
    MutexInv OkInv PoisonInv s₂ := by
  cases hstep with
  | acquireOk _ _ => exact True.intro
  | acquirePoisoned _ _ => exact True.intro
  | unlockCleanOk _ _ _ hok => exact hok
  | unlockKeepPoison _ _ _ hp => exact hp
  | unlockUnwindPoison _ _ hp => exact hp
  | clearPoison _ hok => exact hok

def pairEqInv (p : Nat × Nat) : Prop := p.1 = p.2
def trivialPoisonInv (_ : Nat × Nat) : Prop := True

theorem naive_ignore_poison_spec_refuted :
    ∃ s₁ s₂ : MutexPhysState (Nat × Nat),
      MutexInv pairEqInv trivialPoisonInv (.unlockedOk (0, 0)) ∧
      MutexStep pairEqInv trivialPoisonInv (.unlockedOk (0, 0)) s₁ ∧
      MutexStep pairEqInv trivialPoisonInv s₁ s₂ ∧
      s₂ = .unlockedPoisoned (1, 0) ∧
      MutexInv pairEqInv trivialPoisonInv s₂ ∧
      ¬ pairEqInv (1, 0) := by
  refine ⟨.locked (0, 0) false, .unlockedPoisoned (1, 0), rfl,
    .acquireOk (0, 0) false, .unlockUnwindPoison (0, 0) (1, 0) True.intro,
    rfl, True.intro, ?_⟩
  intro heq
  nomatch heq

/-- Complete real `std::sync::Mutex` transition relation (repair,
matching `library/std/src/sync/poison/mutex.rs:610-612, 631-667` and
`library/std/src/sync/poison.rs:126`):
1. `mutateLocked`: mutates the underlying `UnsafeCell<T>` value through `&mut T`
   from `DerefMut` on `MutexGuard` (`locked v p ↦ locked v' p`).
2. `clearPoisonUnchecked`: `pub fn clear_poison(&self)` (`mutex.rs:610-612`) is
   safe on `&Mutex<T>` and flips `.unlockedPoisoned v ↦ .unlockedOk v` with
   ZERO check of `NormalInv v`.
3. `unlockUnwindAlreadyPanicking`: in `poison::Flag::done` (`poison.rs:126`),
   `!guard.panicking && thread::panicking()` evaluates to `false` when acquired
   while `thread::panicking() == true`, transitioning
   `.locked vBroken true ↦ .unlockedOk vBroken` UNPOISONED.
4. `forgetGuardGetMut` / `forgetGuardIntoInner` (`mutex.rs:631-667`): once the
   shared borrow `&'a Mutex<T>` ends via safe `mem::forget(guard)` (skipping
   `Drop`), safe `get_mut(&mut self)` / `into_inner(self)` bypasses the OS lock
   word and exposes `self.data` (`v`) directly! -/
inductive RealStdMutexStep {T : Type} (NormalInv UnwindInv : T → Prop) :
    MutexPhysState T → MutexPhysState T → Prop where
  | acquireOk (v : T) (wasPanicking : Bool) :
      RealStdMutexStep NormalInv UnwindInv (.unlockedOk v) (.locked v wasPanicking)
  | acquirePoisoned (v : T) (wasPanicking : Bool) :
      RealStdMutexStep NormalInv UnwindInv (.unlockedPoisoned v) (.locked v wasPanicking)
  | mutateLocked (v v' : T) (wasPanicking : Bool) :
      RealStdMutexStep NormalInv UnwindInv (.locked v wasPanicking) (.locked v' wasPanicking)
  | unlockCleanOk (v : T) (wasPanicking : Bool) :
      NormalInv v →
      RealStdMutexStep NormalInv UnwindInv (.locked v wasPanicking) (.unlockedOk v)
  | unlockKeepPoison (v : T) (wasPanicking : Bool) :
      UnwindInv v →
      RealStdMutexStep NormalInv UnwindInv (.locked v wasPanicking) (.unlockedPoisoned v)
  | unlockUnwindFreshPanic (vBroken : T) :
      UnwindInv vBroken →
      RealStdMutexStep NormalInv UnwindInv (.locked vBroken false) (.unlockedPoisoned vBroken)
  | unlockUnwindAlreadyPanicking (vBroken : T) :
      UnwindInv vBroken →
      RealStdMutexStep NormalInv UnwindInv (.locked vBroken true) (.unlockedOk vBroken)
  | clearPoisonUnchecked (v : T) :
      RealStdMutexStep NormalInv UnwindInv (.unlockedPoisoned v) (.unlockedOk v)
  | getMutUnlockedOk (v : T) :
      RealStdMutexStep NormalInv UnwindInv (.unlockedOk v) (.unlockedOk v)
  | intoInnerUnlockedOk (v : T) :
      RealStdMutexStep NormalInv UnwindInv (.unlockedOk v) (.unlockedOk v)
  | forgetGuardGetMut (v : T) (wasPanicking : Bool) :
      RealStdMutexStep NormalInv UnwindInv (.locked v wasPanicking) (.unlockedOk v)
  | forgetGuardIntoInner (v : T) (wasPanicking : Bool) :
      RealStdMutexStep NormalInv UnwindInv (.locked v wasPanicking) (.unlockedOk v)

theorem safe_rust_refutes_distinct_poisonInv {T : Type}
    {OkInv PoisonInv : T → Prop}
    (v₀ vBroken : T)
    (hok₀ : OkInv v₀)
    (hpBroken : PoisonInv vBroken)
    (hnokBroken : ¬ OkInv vBroken) :
    MutexInv OkInv PoisonInv (.unlockedOk v₀) ∧
    (∃ s₁ s₂ s₃ s₄ : MutexPhysState T,
      RealStdMutexStep OkInv PoisonInv (.unlockedOk v₀) s₁ ∧
      RealStdMutexStep OkInv PoisonInv s₁ s₂ ∧
      RealStdMutexStep OkInv PoisonInv s₂ s₃ ∧
      RealStdMutexStep OkInv PoisonInv s₃ s₄ ∧
      s₄ = .unlockedOk vBroken ∧
      ¬ MutexInv OkInv PoisonInv s₄) ∧
    (∃ t₁ t₂ t₃ : MutexPhysState T,
      RealStdMutexStep OkInv PoisonInv (.unlockedOk v₀) t₁ ∧
      RealStdMutexStep OkInv PoisonInv t₁ t₂ ∧
      RealStdMutexStep OkInv PoisonInv t₂ t₃ ∧
      t₃ = .unlockedOk vBroken ∧
      ¬ MutexInv OkInv PoisonInv t₃) := by
  refine ⟨hok₀, ?_, ?_⟩
  · exact ⟨.locked v₀ false, .locked vBroken false,
      .unlockedPoisoned vBroken, .unlockedOk vBroken,
      .acquireOk v₀ false,
      .mutateLocked v₀ vBroken false,
      .unlockUnwindFreshPanic vBroken hpBroken,
      .clearPoisonUnchecked vBroken,
      rfl, hnokBroken⟩
  · exact ⟨.locked v₀ true, .locked vBroken true, .unlockedOk vBroken,
      .acquireOk v₀ true,
      .mutateLocked v₀ vBroken true,
      .unlockUnwindAlreadyPanicking vBroken hpBroken,
      rfl, hnokBroken⟩

theorem safe_rust_refutes_distinct_poisonInv_concrete :
    MutexInv pairEqInv trivialPoisonInv (.unlockedOk (0, 0)) ∧
    (∃ s₁ s₂ s₃ s₄ : MutexPhysState (Nat × Nat),
      RealStdMutexStep pairEqInv trivialPoisonInv (.unlockedOk (0, 0)) s₁ ∧
      RealStdMutexStep pairEqInv trivialPoisonInv s₁ s₂ ∧
      RealStdMutexStep pairEqInv trivialPoisonInv s₂ s₃ ∧
      RealStdMutexStep pairEqInv trivialPoisonInv s₃ s₄ ∧
      s₄ = .unlockedOk (1, 0) ∧
      ¬ MutexInv pairEqInv trivialPoisonInv s₄) ∧
    (∃ t₁ t₂ t₃ : MutexPhysState (Nat × Nat),
      RealStdMutexStep pairEqInv trivialPoisonInv (.unlockedOk (0, 0)) t₁ ∧
      RealStdMutexStep pairEqInv trivialPoisonInv t₁ t₂ ∧
      RealStdMutexStep pairEqInv trivialPoisonInv t₂ t₃ ∧
      t₃ = .unlockedOk (1, 0) ∧
      ¬ MutexInv pairEqInv trivialPoisonInv t₃) :=
  safe_rust_refutes_distinct_poisonInv (0, 0) (1, 0) rfl True.intro
    (fun h => nomatch h)

/-- Safe `mem::forget(guard) + get_mut / into_inner` Refutation
(`safe_forget_then_get_mut_breaks_unrestored_inv`):
EVEN under a unified normal+unwind invariant `MutexInv Inv Inv`, if safe callers
obtain a raw `MutexGuard`, mutate `*guard = vBroken` (`¬ Inv vBroken`), call
safe `mem::forget(guard)` (ending `&'a Mutex<T>` without running `Drop`), and
then call safe `Mutex::get_mut(&mut self)` OR `Mutex::into_inner(self)`
(`library/std/src/sync/poison/mutex.rs:631-667`), safe Rust observes `vBroken`
violating `Inv` with zero panics and zero `Drop` execution! -/
theorem safe_forget_then_get_mut_breaks_unrestored_inv {T : Type}
    {Inv : T → Prop} (v₀ vBroken : T)
    (hinv₀ : Inv v₀) (hnbroken : ¬ Inv vBroken) :
    MutexInv Inv Inv (.unlockedOk v₀) ∧
    (∃ s₁ s₂ s₃ : MutexPhysState T,
      RealStdMutexStep Inv Inv (.unlockedOk v₀) s₁ ∧
      RealStdMutexStep Inv Inv s₁ s₂ ∧
      RealStdMutexStep Inv Inv s₂ s₃ ∧
      s₃ = .unlockedOk vBroken ∧
      ¬ MutexInv Inv Inv s₃) ∧
    (∃ u₁ u₂ u₃ : MutexPhysState T,
      RealStdMutexStep Inv Inv (.unlockedOk v₀) u₁ ∧
      RealStdMutexStep Inv Inv u₁ u₂ ∧
      RealStdMutexStep Inv Inv u₂ u₃ ∧
      u₃ = .unlockedOk vBroken ∧
      ¬ MutexInv Inv Inv u₃) := by
  refine ⟨hinv₀, ?_, ?_⟩
  · exact ⟨.locked v₀ false, .locked vBroken false, .unlockedOk vBroken,
      .acquireOk v₀ false,
      .mutateLocked v₀ vBroken false,
      .forgetGuardGetMut vBroken false,
      rfl, hnbroken⟩
  · exact ⟨.locked v₀ false, .locked vBroken false, .unlockedOk vBroken,
      .acquireOk v₀ false,
      .mutateLocked v₀ vBroken false,
      .forgetGuardIntoInner vBroken false,
      rfl, hnbroken⟩

/-- Linear `MustRelease` guard discipline (`NoForgetGuard`) or encapsulated
wrapper discipline (`MustReleaseOrWrapper Inv`):
- `NoForgetGuard` forbids `forgetGuardGetMut` and `forgetGuardIntoInner`
  altogether (every acquired `MutexGuard` must be linearly released).
- `MustReleaseOrWrapper Inv` allows forgetting ONLY if `Inv v` holds (automatic
  under `NoForgetGuard`, and also satisfied when a safe wrapper encapsulates
  `Mutex<T>` and never returns a `MutexGuard` while `Inv` is broken). -/
inductive RealStdMutexNoForgetStep {T : Type} (NormalInv UnwindInv : T → Prop) :
    MutexPhysState T → MutexPhysState T → Prop where
  | acquireOk (v : T) (wasPanicking : Bool) :
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.unlockedOk v) (.locked v wasPanicking)
  | acquirePoisoned (v : T) (wasPanicking : Bool) :
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.unlockedPoisoned v) (.locked v wasPanicking)
  | mutateLocked (v v' : T) (wasPanicking : Bool) :
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.locked v wasPanicking) (.locked v' wasPanicking)
  | unlockCleanOk (v : T) (wasPanicking : Bool) :
      NormalInv v →
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.locked v wasPanicking) (.unlockedOk v)
  | unlockKeepPoison (v : T) (wasPanicking : Bool) :
      UnwindInv v →
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.locked v wasPanicking) (.unlockedPoisoned v)
  | unlockUnwindFreshPanic (vBroken : T) :
      UnwindInv vBroken →
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.locked vBroken false) (.unlockedPoisoned vBroken)
  | unlockUnwindAlreadyPanicking (vBroken : T) :
      UnwindInv vBroken →
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.locked vBroken true) (.unlockedOk vBroken)
  | clearPoisonUnchecked (v : T) :
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.unlockedPoisoned v) (.unlockedOk v)
  | getMutUnlockedOk (v : T) :
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.unlockedOk v) (.unlockedOk v)
  | intoInnerUnlockedOk (v : T) :
      RealStdMutexNoForgetStep NormalInv UnwindInv
        (.unlockedOk v) (.unlockedOk v)

inductive MustReleaseOrWrapperStep {T : Type} (N U Inv : T → Prop) :
    MutexPhysState T → MutexPhysState T → Prop where
  | nonForget {s₁ s₂ : MutexPhysState T} :
      RealStdMutexNoForgetStep N U s₁ s₂ →
      MustReleaseOrWrapperStep N U Inv s₁ s₂
  | forgetGuardGetMut (v : T) (wasPanicking : Bool) :
      Inv v →
      MustReleaseOrWrapperStep N U Inv (.locked v wasPanicking) (.unlockedOk v)
  | forgetGuardIntoInner (v : T) (wasPanicking : Bool) :
      Inv v →
      MustReleaseOrWrapperStep N U Inv (.locked v wasPanicking) (.unlockedOk v)

def NoForgetGuard {T : Type} {N U : T → Prop} {s₁ s₂ : MutexPhysState T}
    (_ : RealStdMutexStep N U s₁ s₂) : Prop :=
  RealStdMutexNoForgetStep N U s₁ s₂

def MustReleaseOrWrapper {T : Type} {N U : T → Prop} (Inv : T → Prop)
    {s₁ s₂ : MutexPhysState T} (_ : RealStdMutexStep N U s₁ s₂) : Prop :=
  MustReleaseOrWrapperStep N U Inv s₁ s₂

theorem noForget_implies_mustReleaseOrWrapper {T : Type} {N U Inv : T → Prop}
    {s₁ s₂ : MutexPhysState T} {hstep : RealStdMutexStep N U s₁ s₂}
    (hnf : NoForgetGuard hstep) : MustReleaseOrWrapper Inv hstep :=
  MustReleaseOrWrapperStep.nonForget hnf

/-- Positive Soundness Theorem (`linear_mustRelease_and_unified_inv_sound_for_realStdMutex`):
when `MustRelease` forbids forgetting an active guard (`NoForgetGuard`, or a
wrapper never exposes `MutexGuard` while `Inv` is broken via
`MustReleaseOrWrapper Inv`) AND `OkInv = PoisonInv = Inv`, **ALL**
`RealStdMutexStep` transitions (including `mutateLocked`, `clearPoisonUnchecked`,
`unlockUnwindAlreadyPanicking`, `getMutUnlockedOk`, and `intoInnerUnlockedOk`)
preserve `MutexInv Inv Inv`! -/
theorem linear_mustRelease_and_unified_inv_sound_for_realStdMutex
    {T : Type} {Inv : T → Prop} :
    (∀ {s₁ s₂ : MutexPhysState T} (hstep : RealStdMutexStep Inv Inv s₁ s₂),
      MutexInv Inv Inv s₁ → MustReleaseOrWrapper Inv hstep →
        MutexInv Inv Inv s₂) ∧
    (∀ {s₁ s₂ : MutexPhysState T} (hstep : RealStdMutexStep Inv Inv s₁ s₂),
      MutexInv Inv Inv s₁ → NoForgetGuard hstep →
        MutexInv Inv Inv s₂) := by
  have hgen : ∀ {s₁ s₂ : MutexPhysState T}
      (hstep : RealStdMutexStep Inv Inv s₁ s₂),
      MutexInv Inv Inv s₁ → MustReleaseOrWrapper Inv hstep →
        MutexInv Inv Inv s₂ := by
    intro s₁ s₂ _hstep hinv hmr
    cases hmr with
    | nonForget hnf =>
      cases hnf with
      | acquireOk _ _ => exact True.intro
      | acquirePoisoned _ _ => exact True.intro
      | mutateLocked _ _ _ => exact True.intro
      | unlockCleanOk _ _ hi => exact hi
      | unlockKeepPoison _ _ hi => exact hi
      | unlockUnwindFreshPanic _ hi => exact hi
      | unlockUnwindAlreadyPanicking _ hi => exact hi
      | clearPoisonUnchecked _ => exact hinv
      | getMutUnlockedOk _ => exact hinv
      | intoInnerUnlockedOk _ => exact hinv
    | forgetGuardGetMut _ _ hi => exact hi
    | forgetGuardIntoInner _ _ hi => exact hi
  exact ⟨hgen, fun hstep hinv hnf =>
    hgen hstep hinv (noForget_implies_mustReleaseOrWrapper hnf)⟩

/-! ### 2. `RwLock<T>` Fractional Shares & `OnceLock<T>` Borrow/Generation-Scoped Persistence -/

inductive RwGhost (T : Type) where
  | empty
  | shared (numMinus1 : Nat) (denMinus1 : Nat) (val : T)
  | exclusive (val : T)
  | invalid

def rwGhostValid {T : Type} : RwGhost T → Prop
  | .empty => True
  | .shared n d _ => n ≤ d
  | .exclusive _ => True
  | .invalid => False

def rwGhostOp {T : Type} (eqVal : T → T → Bool) :
    RwGhost T → RwGhost T → RwGhost T
  | .empty, x => x
  | x, .empty => x
  | .shared n₁ d₁ v₁, .shared n₂ d₂ v₂ =>
      if Nat.beq d₁ d₂ && eqVal v₁ v₂ then
        let totalNum := (n₁ + 1) + (n₂ + 1)
        if Nat.beq totalNum (d₁ + 1) then
          .exclusive v₁
        else if totalNum ≤ d₁ + 1 then
          .shared (totalNum - 1) d₁ v₁
        else
          .invalid
      else
        .invalid
  | _, _ => .invalid

theorem rwGhost_split_rejoin_half (v : Nat) :
    let half : RwGhost Nat := .shared 0 1 v
    rwGhostValid half ∧
    rwGhostOp Nat.beq half half = .exclusive v := by
  dsimp [rwGhostValid, rwGhostOp]
  refine ⟨Nat.zero_le 1, ?_⟩
  rw [Nat.beq_refl v]
  rfl

theorem rwGhost_reader_agreement {v₁ v₂ : Nat} {n₁ d₁ n₂ d₂ : Nat}
    (hvalid : rwGhostValid (rwGhostOp Nat.beq (.shared n₁ d₁ v₁) (.shared n₂ d₂ v₂))) :
    v₁ = v₂ := by
  dsimp [rwGhostOp] at hvalid
  cases hd : Nat.beq d₁ d₂ with
  | false =>
    rw [hd] at hvalid
    exact False.elim hvalid
  | true =>
    rw [hd] at hvalid
    cases hv : Nat.beq v₁ v₂ with
    | false =>
      rw [hv] at hvalid
      exact False.elim hvalid
    | true =>
      exact Nat.eq_of_beq_eq_true hv

inductive RwPhysState (T : Type) where
  | unlocked (val : T)
  | readLocked (readersSucc : Nat) (val : T)
  | writeLocked (val : T)

inductive RwPhysStep {T : Type} (Inv : T → Prop) :
    RwPhysState T → RwPhysState T → Prop where
  | writeAcquire (v : T) : RwPhysStep Inv (.unlocked v) (.writeLocked v)
  | writeMutate (v v' : T) : RwPhysStep Inv (.writeLocked v) (.writeLocked v')
  | writeUnlock (v : T) : Inv v → RwPhysStep Inv (.writeLocked v) (.unlocked v)
  | downgrade (v : T) : Inv v → RwPhysStep Inv (.writeLocked v) (.readLocked 0 v)
  | readAcquireFirst (v : T) : RwPhysStep Inv (.unlocked v) (.readLocked 0 v)
  | readAcquireMore (n : Nat) (v : T) :
      RwPhysStep Inv (.readLocked n v) (.readLocked (n + 1) v)

theorem rwlock_downgrade_preserves_exact_value {T : Type} {Inv : T → Prop}
    (vWritten : T) (hinv : Inv vWritten) :
    ∃ sRead,
      RwPhysStep Inv (.writeLocked vWritten) sRead ∧
      sRead = .readLocked 0 vWritten :=
  ⟨.readLocked 0 vWritten, .downgrade vWritten hinv, rfl⟩

theorem rwlock_unlock_then_read_loses_exact_value :
    let Inv := fun x : Nat => x ≥ 10
    ∃ s1 s2 s3 s4 s5 : RwPhysState Nat,
      RwPhysStep Inv (.writeLocked 10) s1 ∧
      RwPhysStep Inv s1 s2 ∧
      RwPhysStep Inv s2 s3 ∧
      RwPhysStep Inv s3 s4 ∧
      RwPhysStep Inv s4 s5 ∧
      s5 = .readLocked 0 99 ∧ (99 ≠ 10) := by
  refine ⟨.unlocked 10, .writeLocked 10, .writeLocked 99, .unlocked 99,
    .readLocked 0 99,
    .writeUnlock 10 (by decide),
    .writeAcquire 10,
    .writeMutate 10 99,
    .writeUnlock 99 (by decide),
    .readAcquireFirst 99,
    rfl, by decide⟩

inductive OnceGhost (T : Type) where
  | uninit
  | initialized (val : T)
  | invalid

def onceGhostValid {T : Type} : OnceGhost T → Prop
  | .invalid => False
  | _ => True

def onceGhostOp {T : Type} (eqVal : T → T → Bool) :
    OnceGhost T → OnceGhost T → OnceGhost T
  | .uninit, x => x
  | x, .uninit => x
  | .initialized v₁, .initialized v₂ =>
      if eqVal v₁ v₂ then .initialized v₁ else .invalid
  | _, _ => .invalid

theorem onceGhost_persistent_duplicable (v : Nat) :
    onceGhostOp Nat.beq (.initialized v) (.initialized v) = .initialized v := by
  dsimp [onceGhostOp]
  rw [Nat.beq_refl v]
  rfl

theorem onceGhost_agreement {v₁ v₂ : Nat}
    (hv : onceGhostValid (onceGhostOp Nat.beq (.initialized v₁) (.initialized v₂))) :
    v₁ = v₂ := by
  dsimp [onceGhostOp] at hv
  cases heq : Nat.beq v₁ v₂ with
  | false =>
    rw [heq] at hv
    exact False.elim hv
  | true =>
    exact Nat.eq_of_beq_eq_true heq

inductive GenOnceGhost (T : Type) where
  | empty
  | initialized (gen : Nat) (val : T)
  | invalid

def genOnceGhostValid {T : Type} : GenOnceGhost T → Prop
  | .invalid => False
  | _ => True

def genOnceGhostOp {T : Type} (eqVal : T → T → Bool) :
    GenOnceGhost T → GenOnceGhost T → GenOnceGhost T
  | .empty, x => x
  | x, .empty => x
  | .initialized g₁ v₁, .initialized g₂ v₂ =>
      if Nat.beq g₁ g₂ && eqVal v₁ v₂ then .initialized g₁ v₁ else .invalid
  | _, _ => .invalid

structure OnceLockPhys (T : Type) where
  gen : Nat
  slot : Option T

def onceLockTakeMut {T : Type} (s : OnceLockPhys T) : Option T × OnceLockPhys T :=
  (s.slot, { gen := s.gen + 1, slot := none })

theorem genOnceGhost_scoped_soundness (g : Nat) (v₁ v₂ : Nat) :
    genOnceGhostOp Nat.beq (.initialized g v₁) (.initialized g v₁) =
      .initialized g v₁ ∧
    (genOnceGhostValid
      (genOnceGhostOp Nat.beq (.initialized g v₁) (.initialized g v₂)) →
      v₁ = v₂) ∧
    (let (_, sAfterTake) := onceLockTakeMut { gen := g, slot := some v₁ }
     sAfterTake.slot = none ∧
     ¬ genOnceGhostValid
         (genOnceGhostOp Nat.beq
           (.initialized g v₁) (.initialized sAfterTake.gen v₂))) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [genOnceGhostOp]
    rw [Nat.beq_refl g, Nat.beq_refl v₁]
    rfl
  · intro hv
    dsimp [genOnceGhostOp] at hv
    rw [Nat.beq_refl g] at hv
    cases heq : Nat.beq v₁ v₂ with
    | false => rw [heq] at hv; exact False.elim hv
    | true => exact Nat.eq_of_beq_eq_true heq
  · dsimp [onceLockTakeMut, genOnceGhostOp, genOnceGhostValid]
    refine ⟨rfl, ?_⟩
    have hneq : Nat.beq g (g + 1) = false := by
      induction g with
      | zero => rfl
      | succ _ ih => exact ih
    rw [hneq]
    intro hf
    exact hf

/-! ### 3. Lock-Free External Helping (`HelpingCellState`) -/

abbrev ReqId : Type := Nat
abbrev Epoch : Type := Nat

inductive CellEvent where
  | proposeWin (req : ReqId) (val : Nat)
  | proposeLose (req : ReqId) (winnerVal : Nat)

def ValidCellHistoryAux (st : Option Nat) (events : List CellEvent) : Prop :=
  @List.rec CellEvent (fun _ => Option Nat → Prop)
    (fun _ => True)
    (fun ev _ ih cur =>
      match cur, ev with
      | none, .proposeWin _ v => ih (some v)
      | none, .proposeLose _ _ => False
      | some _, .proposeWin _ _ => False
      | some w, .proposeLose _ obs => w = obs ∧ ih (some w))
    events st

def ValidCellHistory (hist : List CellEvent) : Prop :=
  ValidCellHistoryAux none hist

inductive ReqStatus where
  | pending (invEpoch : Epoch) (proposed : Nat)
  | linearized (invEpoch lpEpoch : Epoch) (returnedVal : Nat) (won : Bool)

structure HelpingCellState where
  physCell : Option Nat
  history : List CellEvent
  pool : ReqId → Option ReqStatus

def HelpingCellInv (s : HelpingCellState) : Prop :=
  ValidCellHistory s.history ∧
  (s.physCell = none → s.history = []) ∧
  (∀ w : Nat, s.physCell = some w →
    ∃ r₀ tail, s.history = .proposeWin r₀ w :: tail) ∧
  (∀ r inv lp ret won,
    s.pool r = some (.linearized inv lp ret won) → inv ≤ lp ∧ lp ≤ s.history.length)

def initHelpingCell : HelpingCellState :=
  { physCell := none, history := [], pool := fun _ => none }

def helpWinFirst (s : HelpingCellState) (reqA : ReqId) (invA : Epoch) (vA : Nat) :
    HelpingCellState :=
  { physCell := some vA
    history := [.proposeWin reqA vA]
    pool := fun r =>
      if Nat.beq r reqA then some (.linearized invA 0 vA true) else s.pool r }

theorem external_helper_linearizes_suspended_caller :
    let s1 : HelpingCellState :=
      { initHelpingCell with
        pool := fun r => if Nat.beq r 7 then some (.pending 0 42) else none }
    let s2 := helpWinFirst s1 7 0 42
    HelpingCellInv s2 ∧
    s2.pool 7 = some (.linearized 0 0 42 true) := by
  dsimp [helpWinFirst, initHelpingCell, HelpingCellInv, ValidCellHistory, ValidCellHistoryAux]
  refine ⟨⟨True.intro, ?_, ?_, ?_⟩, rfl⟩
  · intro h; nomatch h
  · intro w hw
    injection hw with heq
    subst heq
    exact ⟨7, [], rfl⟩
  · intro r inv lp ret won hp
    cases hr : Nat.beq r 7 with
    | false =>
      rw [hr] at hp
      nomatch hp
    | true =>
      rw [hr] at hp
      dsimp at hp
      injection hp with hreq
      injection hreq with h1 h2 h3 h4
      subst h1; subst h2; subst h3; subst h4
      exact ⟨Nat.le_refl 0, Nat.zero_le 1⟩

/-! ### 4. Real Even/Odd `SeqLock` Optimistic Read & Non-Tautological Whole-Program Prophecy Erasure -/

/-- Real physical `SeqLock` state:
- even `version` (`Nat.land version 1 = 0`): quiescent, `payload` is consistent,
- odd `version` (`Nat.land version 1 ≠ 0`): writer in progress, `payload` may be torn! -/
structure SeqLockPhys where
  version : Nat
  payload : Nat

def writerBegin (s : SeqLockPhys) : SeqLockPhys :=
  { version := s.version + 1, payload := s.payload }

def writerWritePayload (s : SeqLockPhys) (p' : Nat) : SeqLockPhys :=
  { version := s.version, payload := p' }

def writerEnd (s : SeqLockPhys) : SeqLockPhys :=
  { version := s.version + 1, payload := s.payload }

inductive SeqLockWriteStep : SeqLockPhys → SeqLockPhys → Prop where
  | beginWrite (s : SeqLockPhys) :
      Nat.beq (Nat.land s.version 1) 0 = true →
      SeqLockWriteStep s (writerBegin s)
  | writePayload (s : SeqLockPhys) (p' : Nat) :
      Nat.beq (Nat.land s.version 1) 0 = false →
      SeqLockWriteStep s (writerWritePayload s p')
  | endWrite (s : SeqLockPhys) :
      Nat.beq (Nat.land s.version 1) 0 = false →
      SeqLockWriteStep s (writerEnd s)

/-- Real even/odd `SeqLock` optimistic read attempt:
checks BOTH that `s₁.version` is even (`(s₁.version & 1) == 0`, not mid-write)
AND that `s₁.version == s₂.version` (no writer entered between `s₁` and `s₂`);
returns `some s₁.payload` ONLY when validated, else `none` (forcing retry — NEVER
returning `s₂.payload` or a torn odd-version payload!). -/
def evalSeqLockReadAttempt (s₁ s₂ : SeqLockPhys) : Option Nat :=
  if Nat.beq (Nat.land s₁.version 1) 0 && Nat.beq s₁.version s₂.version then
    some s₁.payload
  else
    none

/-- Odd/torn `SeqLock` rejection (`seqlock_odd_version_rejected`):
an in-progress odd-version snapshot `s₁ = ⟨1, torn⟩, s₂ = ⟨1, torn⟩` ALWAYS
returns `none` (never returning `torn`, even though `s₁.version == s₂.version`!). -/
theorem seqlock_odd_version_rejected (torn : Nat) :
    evalSeqLockReadAttempt ⟨1, torn⟩ ⟨1, torn⟩ = none := by
  simp [evalSeqLockReadAttempt]

theorem nat_beq_self_add2 (v : Nat) : Nat.beq v (v + 2) = false := by
  induction v with
  | zero => rfl
  | succ _ ih => exact ih

/-- Concurrent write retry requirement (`seqlock_concurrent_write_retry_required`):
if a writer advances `0 -> 1 -> 2` (`writerBegin`, `writerWritePayload`,
`writerEnd`) between `s₁ = ⟨0, p₀⟩` and `s₂ = ⟨2, p₁⟩`, `evalSeqLockReadAttempt`
returns `none` (forcing a clean retry, NEVER returning unvalidated `s₂.payload`!). -/
theorem seqlock_concurrent_write_retry_required (p₀ p₁ : Nat) :
    let s₁ : SeqLockPhys := ⟨0, p₀⟩
    let sMid1 := writerBegin s₁
    let sMid2 := writerWritePayload sMid1 p₁
    let s₂ := writerEnd sMid2
    SeqLockWriteStep s₁ sMid1 ∧
    SeqLockWriteStep sMid1 sMid2 ∧
    SeqLockWriteStep sMid2 s₂ ∧
    evalSeqLockReadAttempt s₁ s₂ = none := by
  refine ⟨.beginWrite _ ?_, .writePayload _ p₁ ?_, .endWrite _ ?_, ?_⟩
  · dsimp; rfl
  · dsimp [writerBegin]; rfl
  · dsimp [writerBegin, writerWritePayload]; rfl
  · simp [writerBegin, writerWritePayload, writerEnd, evalSeqLockReadAttempt]

/-- Validated `SeqLock` read linearization (`seqlock_validated_read_linearizes_at_clean_snapshot`):
1. Whenever `evalSeqLockReadAttempt s₁ s₂ = some v`, `s₁.version` is even
   (`Nat.land s₁.version 1 = 0`), `s₁.version = s₂.version` (zero intervening
   writes), and `v = s₁.payload` (consistent quiescent snapshot at `s₁.version`)!
2. Whether the attempt linearizes at `s₁` (`some 10`) or aborts (`none`) depends
   on future writer interference between `s₁` and `s₂` and is NOT determined by
   `s₁` alone! -/
theorem seqlock_validated_read_linearizes_at_clean_snapshot :
    (∀ (s₁ s₂ : SeqLockPhys) (v : Nat),
      evalSeqLockReadAttempt s₁ s₂ = some v →
      Nat.land s₁.version 1 = 0 ∧
      s₁.version = s₂.version ∧
      v = s₁.payload) ∧
    (let s₁ : SeqLockPhys := ⟨0, 10⟩
     evalSeqLockReadAttempt s₁ ⟨0, 10⟩ = some 10 ∧
     evalSeqLockReadAttempt s₁ (writerEnd (writerWritePayload (writerBegin s₁) 99)) = none) := by
  refine ⟨?_, ⟨rfl, rfl⟩⟩
  intro s₁ s₂ v heval
  unfold evalSeqLockReadAttempt at heval
  cases heven : Nat.beq (Nat.land s₁.version 1) 0 with
  | false =>
    rw [heven] at heval
    nomatch heval
  | true =>
    rw [heven] at heval
    cases hsame : Nat.beq s₁.version s₂.version with
    | false =>
      rw [hsame] at heval
      nomatch heval
    | true =>
      rw [hsame] at heval
      dsimp at heval
      injection heval with hv
      exact ⟨Nat.eq_of_beq_eq_true heven, Nat.eq_of_beq_eq_true hsame, Eq.symm hv⟩

/-! ### Genuine Non-Tautological Whole-Program Prophecy / Ghost Erasure -/

/-- Pure physical whole-program execution (`runPhys`): depends STRICTLY on
`PhysState` and scheduler `choiceStream`, with zero ghost state or prophecy
primitives! -/
noncomputable def runPhys {PhysState Choice : Type}
    (physStep : PhysState → Choice → PhysState)
    (choiceStream : Nat → Choice)
    (ps₀ : PhysState) : Nat → PhysState
  | 0 => ps₀
  | n + 1 => physStep (runPhys physStep choiceStream ps₀ n) (choiceStream n)

/-- Ghost-instrumented whole-program execution (`runGhost`): runs `physStep` on
the physical component alongside arbitrary proof-level `ghostUpdate` on
`GhostState`. -/
noncomputable def runGhost {PhysState GhostState Choice : Type}
    (ghostUpdate : PhysState → GhostState → Choice → GhostState)
    (physStep : PhysState → Choice → PhysState)
    (choiceStream : Nat → Choice)
    (st₀ : PhysState × GhostState) : Nat → PhysState × GhostState
  | 0 => st₀
  | n + 1 =>
      let cur := runGhost ghostUpdate physStep choiceStream st₀ n
      let c := choiceStream n
      (physStep cur.1 c, ghostUpdate cur.1 cur.2 c)

/-- Non-tautological Ghost Erasure Invariant (`ghost_erasure_invariant`):
for ALL step counts `n`, the physical projection `.1` of the ghost-instrumented
execution `runGhost` is identically equal to the pure physical execution
`runPhys` (proved by induction on `n`, certifying ZERO causal back-flow from
`GhostState` or `ghostUpdate` into `PhysState`!). -/
theorem ghost_erasure_invariant {PhysState GhostState Choice : Type}
    (ghostUpdate : PhysState → GhostState → Choice → GhostState)
    (physStep : PhysState → Choice → PhysState)
    (choiceStream : Nat → Choice)
    (ps₀ : PhysState) (gs₀ : GhostState) :
    ∀ n : Nat,
      (runGhost ghostUpdate physStep choiceStream (ps₀, gs₀) n).1 =
        runPhys physStep choiceStream ps₀ n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [runGhost, runPhys]
    rw [ih]

/-- Whole-program adequacy discharge of future-dependent `SeqLock` reads directly
from the erased physical trace (`whole_program_future_lp_from_erased_physTrace`):
any open-crate `SeqLock` proof universally quantified over abstract future
physical snapshots (`∀ futSnap : SeqLockPhys, ...`) discharges at whole-program
adequacy by instantiating `futSnap := runPhys physStep choiceStream ps₀ (invStep + 1)`,
and by `ghost_erasure_invariant` coincides identically with any ghost-instrumented
execution `runGhost` — requiring ZERO prophecy instructions in `Trusted/`! -/
theorem whole_program_future_lp_from_erased_physTrace {GhostState Choice : Type}
    (openCrateSeqLockProof :
      ∀ (s₁ futSnap : SeqLockPhys),
        ∀ v : Nat,
          evalSeqLockReadAttempt s₁ futSnap = some v →
          Nat.land s₁.version 1 = 0 ∧
          s₁.version = futSnap.version ∧
          v = s₁.payload)
    (ghostUpdate : SeqLockPhys → GhostState → Choice → GhostState)
    (physStep : SeqLockPhys → Choice → SeqLockPhys)
    (choiceStream : Nat → Choice)
    (ps₀ : SeqLockPhys) (gs₀ : GhostState) (invStep : Nat) :
    let gSnap₁ := (runGhost ghostUpdate physStep choiceStream (ps₀, gs₀) invStep).1
    let gSnap₂ := (runGhost ghostUpdate physStep choiceStream (ps₀, gs₀) (invStep + 1)).1
    let pSnap₁ := runPhys physStep choiceStream ps₀ invStep
    let pSnap₂ := runPhys physStep choiceStream ps₀ (invStep + 1)
    evalSeqLockReadAttempt gSnap₁ gSnap₂ = evalSeqLockReadAttempt pSnap₁ pSnap₂ ∧
    (∀ v : Nat,
      evalSeqLockReadAttempt gSnap₁ gSnap₂ = some v →
      Nat.land pSnap₁.version 1 = 0 ∧
      pSnap₁.version = pSnap₂.version ∧
      v = pSnap₁.payload) := by
  dsimp
  have he1 := ghost_erasure_invariant ghostUpdate physStep choiceStream ps₀ gs₀ invStep
  have he2 := ghost_erasure_invariant ghostUpdate physStep choiceStream ps₀ gs₀ (invStep + 1)
  rw [he1, he2]
  exact ⟨rfl, openCrateSeqLockProof _ _⟩

/-! ### 5. `Chase–Lev` Deque Trace Spec -/

inductive DequeEvent where
  | push (v : Nat)
  | popSome (v : Nat)
  | popEmpty
  | stealSome (v : Nat)
  | stealEmpty

noncomputable def removeLast : List Nat → Option (List Nat × Nat)
  | [] => none
  | [x] => some ([], x)
  | x :: y :: rest =>
      match removeLast (y :: rest) with
      | some (init, last) => some (x :: init, last)
      | none => none

def ValidDequeHistoryAux (initItems : List Nat)
    (events : List DequeEvent) : Prop :=
  @List.rec DequeEvent (fun _ => List Nat → Prop)
    (fun items => items = items)
    (fun ev _ ih items =>
      match items, ev with
      | items, .push v => ih (items ++ [v])
      | [], .popEmpty => ih []
      | _ :: _, .popEmpty => False
      | items, .popSome v =>
          match removeLast items with
          | some (rem, last) => last = v ∧ ih rem
          | none => False
      | [], .stealEmpty => ih []
      | _ :: _, .stealEmpty => False
      | [], .stealSome _ => False
      | hd :: tl, .stealSome v => hd = v ∧ ih tl)
    events initItems

def ValidDequeHistory (hist : List DequeEvent) : Prop :=
  ValidDequeHistoryAux [] hist

theorem chaseLev_valid_trace_linearizable :
    ValidDequeHistory
      [.push 10, .push 20, .stealSome 10, .popSome 20, .stealEmpty] :=
  ⟨rfl, rfl, rfl⟩

theorem chaseLev_buggy_no_cas_steal_refuted :
    ¬ ValidDequeHistory [.push 42, .popSome 42, .stealSome 42] := by
  intro h
  dsimp [ValidDequeHistory, ValidDequeHistoryAux, removeLast] at h
  exact h.2

/-! ### 6. Coupled Caller Ghost State in `ConcurrentRelLAT` (`OMO -> RelLAT`) -/

def RelLAT {S Op Res : Type}
    (stepSpec : Op → S → S → Res → Prop)
    (impl : Op → S → S → Res → Prop) : Prop :=
  ∀ (op : Op) (CallerInv : S → Prop) (CallerPost : S → Res → Prop),
    (∀ s s' res, CallerInv s → stepSpec op s s' res → CallerPost s' res) →
    ∀ s₁ s₂ res, CallerInv s₁ → impl op s₁ s₂ res → CallerPost s₂ res

theorem omo_refinement_implies_relLAT {S Op Res : Type}
    {stepSpec impl : Op → S → S → Res → Prop}
    (hrefine : ∀ op s₁ s₂ res, impl op s₁ s₂ res → stepSpec op s₁ s₂ res) :
    RelLAT stepSpec impl := by
  intro op CallerInv CallerPost hvs s₁ s₂ res hinv himpl
  exact hvs s₁ s₂ res hinv (hrefine op s₁ s₂ res himpl)

inductive EnvStar {S : Type} (envStep : S → S → Prop) : S → S → Prop where
  | refl (s : S) : EnvStar envStep s s
  | tail {s₁ s₂ s₃ : S} :
      EnvStar envStep s₁ s₂ → envStep s₂ s₃ → EnvStar envStep s₁ s₃

/-- Rely-stability of a predicate `P : S → CallerGhost → Prop` coupling physical
shared state `S` with caller-owned ghost state `CallerGhost`:
environment steps `envStep s s'` preserve `P` at fixed caller ghost state `g`! -/
def RelyStable {S CallerGhost : Type} (envStep : S → S → Prop)
    (P : S → CallerGhost → Prop) : Prop :=
  ∀ (s s' : S) (g : CallerGhost), envStep s s' → P s g → P s' g

theorem relyStable_envStar {S CallerGhost : Type}
    {envStep : S → S → Prop} {P : S → CallerGhost → Prop}
    (hstable : RelyStable envStep P) {s₁ s₂ : S} {g : CallerGhost}
    (hp : P s₁ g) (hstar : EnvStar envStep s₁ s₂) : P s₂ g := by
  induction hstar with
  | refl => exact hp
  | tail _ hstep ih => exact hstable _ _ g hstep ih

def ConcurrentOMOImpl {S Op Res : Type}
    (envStep : S → S → Prop)
    (stepSpec : Op → S → S → Res → Prop)
    (op : Op) (s₁ s₂ : S) (res : Res) : Prop :=
  ∃ s_lp s'_lp : S,
    EnvStar envStep s₁ s_lp ∧
    stepSpec op s_lp s'_lp res ∧
    EnvStar envStep s'_lp s₂

/-- Coupled-ghost `ConcurrentRelLAT`:
parameterized over arbitrary caller ghost state `CallerGhost`, coupled pre-state
invariant `CallerInv : S → CallerGhost → Prop`, coupled post-condition
`CallerPost : Res → S → CallerGhost → Prop`, and caller ghost update at the
linearization point `ghostLP : S → Res → CallerGhost → CallerGhost`, requiring
`RelyStable` on BOTH `CallerInv` and `CallerPost`! -/
def ConcurrentRelLAT {S Op Res : Type}
    (envStep : S → S → Prop)
    (stepSpec : Op → S → S → Res → Prop)
    (impl : Op → S → S → Res → Prop) : Prop :=
  ∀ (op : Op) (CallerGhost : Type)
    (CallerInv : S → CallerGhost → Prop)
    (CallerPost : Res → S → CallerGhost → Prop)
    (ghostLP : S → Res → CallerGhost → CallerGhost),
    RelyStable envStep CallerInv →
    (∀ res : Res, RelyStable envStep (CallerPost res)) →
    (∀ s s' res g,
      CallerInv s g → stepSpec op s s' res →
        CallerPost res s' (ghostLP s res g)) →
    ∀ s₁ s₂ res g₁,
      CallerInv s₁ g₁ → impl op s₁ s₂ res →
        ∃ s_lp : S,
          EnvStar envStep s₁ s_lp ∧
          CallerInv s_lp g₁ ∧
          CallerPost res s₂ (ghostLP s_lp res g₁)

/-- Coupled-Ghost Concurrent `OMO -> RelLAT` Bridge
(`omo_refinement_implies_coupled_ghost_concurrent_relLAT`):
1. Transports `CallerInv s₁ g₁` across pre-LP interference `EnvStar s₁ s_lp` to
   `CallerInv s_lp g₁`,
2. Applies the caller's atomic ghost view-shift `g₁ ↦ ghostLP s_lp res g₁` at
   `stepSpec op s_lp s'_lp res`, and
3. Transports `CallerPost res s'_lp (ghostLP s_lp res g₁)` across post-LP
   interference `EnvStar s'_lp s₂` to `CallerPost res s₂ (ghostLP s_lp res g₁)`! -/
theorem omo_refinement_implies_coupled_ghost_concurrent_relLAT {S Op Res : Type}
    {envStep : S → S → Prop}
    {stepSpec impl : Op → S → S → Res → Prop}
    (hrefine : ∀ op s₁ s₂ res,
      impl op s₁ s₂ res → ConcurrentOMOImpl envStep stepSpec op s₁ s₂ res) :
    ConcurrentRelLAT envStep stepSpec impl := by
  intro op CallerGhost CallerInv CallerPost ghostLP
    hInvStable hPostStable hvs s₁ s₂ res g₁ hinv₁ himpl
  cases hrefine op s₁ s₂ res himpl with
  | intro s_lp hrest =>
    cases hrest with
    | intro s'_lp hseq =>
      have hinvLp : CallerInv s_lp g₁ :=
        relyStable_envStar hInvStable hinv₁ hseq.1
      have hpostLp : CallerPost res s'_lp (ghostLP s_lp res g₁) :=
        hvs s_lp s'_lp res g₁ hinvLp hseq.2.1
      exact ⟨s_lp, hseq.1, hinvLp,
        relyStable_envStar (hPostStable res) hpostLp hseq.2.2⟩

/-- Sharpness counterexample for coupled-ghost `ConcurrentRelLAT`:
with coupled caller ghost state `CallerGhost := Nat` (`CallerInv s g := g ≤ s`),
atomic `fetch_add` (`s' = s + 1 ∧ res = s`) updating caller ghost state to the
drawn ticket `ghostLP s res _ := res + 1` satisfies `FragilePost res s g :=
(s = g)` at the LP (`1 = 1`), yet post-LP interference `1 ->_env 3` breaks
`FragilePost` (`3 ≠ 1`) while preserving rely-stable `StablePost res s g :=
(g = res + 1 ∧ g ≤ s)` (`1 ≤ 3`)! -/
theorem non_relyStable_callerPost_fails_concurrent_relLAT :
    let envStep (s s' : Nat) : Prop := s' = s + 2
    let stepSpec (_ : Unit) (s s' res : Nat) : Prop := s' = s + 1 ∧ res = s
    let CallerInv (s g : Nat) : Prop := g ≤ s
    let ghostLP (_ res _ : Nat) : Nat := res + 1
    let FragilePost (_ s g : Nat) : Prop := s = g
    let StablePost (res s g : Nat) : Prop := g = res + 1 ∧ g ≤ s
    RelyStable envStep CallerInv ∧
    (∀ res, RelyStable envStep (StablePost res)) ∧
    (∀ s s' res g, CallerInv s g → stepSpec () s s' res →
      FragilePost res s' (ghostLP s res g) ∧
      StablePost res s' (ghostLP s res g)) ∧
    ConcurrentOMOImpl envStep stepSpec () 0 3 0 ∧
    CallerInv 0 0 ∧
    StablePost 0 3 (ghostLP 0 0 0) ∧
    ¬ FragilePost 0 3 (ghostLP 0 0 0) := by
  refine ⟨?_, ?_, ?_, ?_, Nat.le_refl 0, ⟨rfl, by decide⟩, by decide⟩
  · intro s s' g heq hle
    subst heq
    exact Nat.le_trans hle (Nat.le_add_right s 2)
  · intro res s s' g heq hst
    subst heq
    exact ⟨hst.1, Nat.le_trans hst.2 (Nat.le_add_right s 2)⟩
  · intro s s' res g _ hspec
    dsimp
    rw [hspec.1, hspec.2]
    exact ⟨rfl, rfl, Nat.le_refl (s + 1)⟩
  · exact ⟨0, 1, .refl 0, ⟨rfl, rfl⟩, .tail (.refl 1) rfl⟩

/-! ### 7. Cantor Impredicativity Barrier & Strictly Positive Rational `RatLevel` ($\mathbb{Q}_{>0}$) -/

universe u

theorem cantor_no_unstratified_ghost_predicate_heap (G : Type u)
    (decode : G → (G → Prop)) :
    ∃ P : G → Prop, ∀ g : G, decode g ≠ P := by
  refine ⟨fun g => ¬ decode g g, ?_⟩
  intro g h_eq
  have hiff : decode g g ↔ ¬ decode g g := by
    refine ⟨?_, ?_⟩
    · intro hdg
      exact Eq.mp (congrFun h_eq g) hdg
    · intro hndg
      exact Eq.mpr (congrFun h_eq g) hndg
  exact (fun h => hiff.1 h h) (hiff.2 (fun h => hiff.1 h h))

/-- Strictly positive rational lock levels $\mathbb{Q}_{>0}$:
represents $\frac{\text{numMinus1} + 1}{\text{denMinus1} + 1} > 0$, eliminating
the naive `num = 0` global minimum (`⟨0, 0⟩`) so downstream crates can interpose
new lock levels strictly BELOW any upstream crate's level, strictly BETWEEN any
two ordered levels, AND strictly ABOVE any upstream crate's level! -/
structure RatLevel where
  numMinus1 : Nat
  denMinus1 : Nat

def ratNum (r : RatLevel) : Nat := r.numMinus1 + 1
def ratDen (r : RatLevel) : Nat := r.denMinus1 + 1

abbrev ratPrec (a b : RatLevel) : Prop :=
  ratNum a * ratDen b < ratNum b * ratDen a

def ratMediant (a b : RatLevel) : RatLevel :=
  { numMinus1 := a.numMinus1 + b.numMinus1 + 1
    denMinus1 := a.denMinus1 + b.denMinus1 + 1 }

def ratBelow (b : RatLevel) : RatLevel :=
  { numMinus1 := 0
    denMinus1 := b.denMinus1 + 1 }

def ratAbove (a : RatLevel) : RatLevel :=
  { numMinus1 := a.numMinus1 + 1
    denMinus1 := 0 }

theorem ratNum_mediant (a b : RatLevel) :
    ratNum (ratMediant a b) = ratNum a + ratNum b := by
  unfold ratNum ratMediant
  dsimp
  rw [Nat.add_right_comm a.numMinus1 b.numMinus1 1, Nat.add_assoc]

theorem ratDen_mediant (a b : RatLevel) :
    ratDen (ratMediant a b) = ratDen a + ratDen b := by
  unfold ratDen ratMediant
  dsimp
  rw [Nat.add_right_comm a.denMinus1 b.denMinus1 1, Nat.add_assoc]

theorem ratPrec_irrefl (a : RatLevel) : ¬ ratPrec a a :=
  Nat.lt_irrefl (ratNum a * ratDen a)

theorem mul_lt_cancel_pos_right {x y k : Nat} (_hk : 0 < k) (h : x * k < y * k) :
    x < y := by
  cases Nat.lt_or_ge x y with
  | inl hlt => exact hlt
  | inr hge =>
    have hmul : y * k ≤ x * k := Nat.mul_le_mul_right k hge
    exact False.elim (Nat.not_lt_of_ge hmul h)

theorem ratPrec_trans {a b c : RatLevel}
    (hab : ratPrec a b) (hbc : ratPrec b c) : ratPrec a c := by
  unfold ratPrec at hab hbc
  unfold ratPrec
  have hc_pos : 0 < ratDen c := Nat.zero_lt_succ c.denMinus1
  have ha_pos : 0 < ratDen a := Nat.zero_lt_succ a.denMinus1
  have hb_pos : 0 < ratDen b := Nat.zero_lt_succ b.denMinus1
  have h1 : (ratNum a * ratDen b) * ratDen c < (ratNum b * ratDen a) * ratDen c :=
    Nat.mul_lt_mul_of_pos_right hab hc_pos
  have h2 : (ratNum b * ratDen c) * ratDen a < (ratNum c * ratDen b) * ratDen a :=
    Nat.mul_lt_mul_of_pos_right hbc ha_pos
  have eq1 : (ratNum b * ratDen a) * ratDen c = (ratNum b * ratDen c) * ratDen a := by
    rw [Nat.mul_assoc, Nat.mul_comm (ratDen a) (ratDen c), ← Nat.mul_assoc]
  rw [eq1] at h1
  have h12 : (ratNum a * ratDen b) * ratDen c < (ratNum c * ratDen b) * ratDen a :=
    Nat.lt_trans h1 h2
  have eqL : (ratNum a * ratDen b) * ratDen c = (ratNum a * ratDen c) * ratDen b := by
    rw [Nat.mul_assoc, Nat.mul_comm (ratDen b) (ratDen c), ← Nat.mul_assoc]
  have eqR : (ratNum c * ratDen b) * ratDen a = (ratNum c * ratDen a) * ratDen b := by
    rw [Nat.mul_assoc, Nat.mul_comm (ratDen b) (ratDen a), ← Nat.mul_assoc]
  rw [eqL, eqR] at h12
  exact mul_lt_cancel_pos_right hb_pos h12

/-- No-Minimum Theorem (`ratLevel_no_minimum`):
EVERY `b : RatLevel` (including `⟨0, 0⟩` representing $1/1$) admits a strictly
smaller `a := ratBelow b` (`ratPrec a b`), with zero lower-bound obstruction. -/
theorem ratLevel_no_minimum (b : RatLevel) :
    ∃ a : RatLevel, ratPrec a b := by
  refine ⟨ratBelow b, ?_⟩
  unfold ratPrec ratBelow ratNum ratDen
  dsimp
  rw [Nat.one_mul]
  have hlt1 : b.denMinus1 + 1 < 1 * (b.denMinus1 + 1 + 1) := by
    rw [Nat.one_mul]
    exact Nat.lt_succ_self (b.denMinus1 + 1)
  have hge1 : 1 ≤ b.numMinus1 + 1 := Nat.succ_le_succ (Nat.zero_le b.numMinus1)
  have hle : 1 * (b.denMinus1 + 1 + 1) ≤ (b.numMinus1 + 1) * (b.denMinus1 + 1 + 1) :=
    Nat.mul_le_mul_right (b.denMinus1 + 1 + 1) hge1
  exact Nat.lt_of_lt_of_le hlt1 hle

/-- No-Maximum Theorem (`ratLevel_no_maximum`):
EVERY `a : RatLevel` admits a strictly larger `b := ratAbove a` (`ratPrec a b`). -/
theorem ratLevel_no_maximum (a : RatLevel) :
    ∃ b : RatLevel, ratPrec a b := by
  refine ⟨ratAbove a, ?_⟩
  unfold ratPrec ratAbove ratNum ratDen
  dsimp
  rw [Nat.mul_one]
  have hlt1 : a.numMinus1 + 1 < (a.numMinus1 + 1 + 1) * 1 := by
    rw [Nat.mul_one]
    exact Nat.lt_succ_self (a.numMinus1 + 1)
  have hge1 : 1 ≤ a.denMinus1 + 1 := Nat.succ_le_succ (Nat.zero_le a.denMinus1)
  have hle : (a.numMinus1 + 1 + 1) * 1 ≤ (a.numMinus1 + 1 + 1) * (a.denMinus1 + 1) :=
    Nat.mul_le_mul_left (a.numMinus1 + 1 + 1) hge1
  exact Nat.lt_of_lt_of_le hlt1 hle

/-- Unbounded Density Theorem (`ratMediant_strictly_between`):
for ANY `a b : RatLevel` with `ratPrec a b`, `ratMediant a b` lies strictly
between `a` and `b`. -/
theorem ratMediant_strictly_between {a b : RatLevel} (hab : ratPrec a b) :
    ratPrec a (ratMediant a b) ∧ ratPrec (ratMediant a b) b := by
  refine ⟨?_, ?_⟩
  · unfold ratPrec
    rw [ratDen_mediant, ratNum_mediant]
    rw [Nat.left_distrib, Nat.right_distrib]
    exact Nat.add_lt_add_left hab (ratNum a * ratDen a)
  · unfold ratPrec
    rw [ratDen_mediant, ratNum_mediant]
    rw [Nat.right_distrib, Nat.left_distrib]
    exact Nat.add_lt_add_right hab (ratNum b * ratDen b)

structure ExportedConcurrentCrateSpec where
  lockInv : Nat → Prop
  lockLevel : RatLevel
  queueHistoryValid : List DequeEvent → Prop

def upstreamCrateSpec : ExportedConcurrentCrateSpec :=
  { lockInv := fun x => Nat.mod x 2 = 0
    lockLevel := ⟨0, 0⟩
    queueHistoryValid := ValidDequeHistory }

def upstreamOuterLockLevel : RatLevel := ⟨1, 0⟩

/-- Cross-Crate Open Extension Theorem
(`downstream_interposes_below_between_and_above_upstream`):
even when an upstream crate exports `lockLevel := ⟨0, 0⟩` ($1/1$, the former
minimum!) alongside `upstreamOuterLockLevel := ⟨1, 0⟩` ($2/1$), ANY
downstream crate can interpose new lock levels strictly BELOW `u₁`, strictly
BETWEEN `u₁` and `u₂`, AND strictly ABOVE `u₂` without modifying upstream! -/
theorem downstream_interposes_below_between_and_above_upstream :
    (∀ u₁ u₂ : RatLevel, ratPrec u₁ u₂ →
      ratPrec (ratBelow u₁) u₁ ∧
      ratPrec u₁ (ratMediant u₁ u₂) ∧
      ratPrec (ratMediant u₁ u₂) u₂ ∧
      ratPrec u₂ (ratAbove u₂)) ∧
    (let u₁ := upstreamCrateSpec.lockLevel
     let u₂ := upstreamOuterLockLevel
     ratPrec (ratBelow u₁) u₁ ∧
     ratPrec u₁ (ratMediant u₁ u₂) ∧
     ratPrec (ratMediant u₁ u₂) u₂ ∧
     ratPrec u₂ (ratAbove u₂)) := by
  have hgen : ∀ u₁ u₂ : RatLevel, ratPrec u₁ u₂ →
      ratPrec (ratBelow u₁) u₁ ∧
      ratPrec u₁ (ratMediant u₁ u₂) ∧
      ratPrec (ratMediant u₁ u₂) u₂ ∧
      ratPrec u₂ (ratAbove u₂) := by
    intro u₁ u₂ hu
    have hmin : ratPrec (ratBelow u₁) u₁ := by
      unfold ratPrec ratBelow ratNum ratDen; dsimp
      rw [Nat.one_mul]
      have hlt1 : u₁.denMinus1 + 1 < 1 * (u₁.denMinus1 + 1 + 1) := by
        rw [Nat.one_mul]; exact Nat.lt_succ_self (u₁.denMinus1 + 1)
      have hle : 1 * (u₁.denMinus1 + 1 + 1) ≤ (u₁.numMinus1 + 1) * (u₁.denMinus1 + 1 + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le u₁.numMinus1))
      exact Nat.lt_of_lt_of_le hlt1 hle
    have hmax : ratPrec u₂ (ratAbove u₂) := by
      unfold ratPrec ratAbove ratNum ratDen; dsimp
      rw [Nat.mul_one]
      have hlt1 : u₂.numMinus1 + 1 < (u₂.numMinus1 + 1 + 1) * 1 := by
        rw [Nat.mul_one]; exact Nat.lt_succ_self (u₂.numMinus1 + 1)
      have hle : (u₂.numMinus1 + 1 + 1) * 1 ≤ (u₂.numMinus1 + 1 + 1) * (u₂.denMinus1 + 1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le u₂.denMinus1))
      exact Nat.lt_of_lt_of_le hlt1 hle
    have hmed := ratMediant_strictly_between hu
    exact ⟨hmin, hmed.1, hmed.2, hmax⟩
  exact ⟨hgen, hgen upstreamCrateSpec.lockLevel upstreamOuterLockLevel (by decide)⟩

end Anneal.ConcurrentSpecs
