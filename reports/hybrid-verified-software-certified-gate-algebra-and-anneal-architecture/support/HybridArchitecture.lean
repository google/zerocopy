-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- Standalone Lean v4.34.1 mechanization of the Hybrid Building Block Core Algebra:
--   1. `RawOutcome` + `CertifiedGate` (unifying S1/S2/S3 with built-in O(1) witness cap)
--   2. Gate-aware portfolio monoid `firstAccepted` vs. naive pre-gate `orElse` counterexample (S6)
--   3. Direct fallback elimination `withFallback` & unified `foldGate` for hint loops (S4)
--      and prefix-safe incremental streaming (S5)
--   4. Rung 1.5 (`WellFormed`-only in-process producer) caller-memory mutation counterexample
--      vs. `CallerMemPreserved` frame-safe composition theorem
--   5. Joint `(EffectMask.le ∧ AvailabilityRefines)` monotone ratcheting preorder
--
-- Core Init only (zero external packages, zero `sorryAx`, zero `._unsafe_rec`,
-- zero `Lean.ofReduceBool`).

namespace HybridArch

/-! ## 1. Core Outcomes, EffectMask, and `CertifiedGate` -/

structure EffectMask where
  terminates : Bool
  noUnwind   : Bool
  noAbort    : Bool

def EffectMask.totalNormal : EffectMask :=
  { terminates := true, noUnwind := true, noAbort := true }

def EffectMask.partialAnyExit : EffectMask :=
  { terminates := false, noUnwind := false, noAbort := false }

def EffectMask.le (mReq mImpl : EffectMask) : Prop :=
  (mReq.terminates = true → mImpl.terminates = true) ∧
  (mReq.noUnwind   = true → mImpl.noUnwind   = true) ∧
  (mReq.noAbort    = true → mImpl.noAbort    = true)

theorem effectMask_le_refl (m : EffectMask) : EffectMask.le m m :=
  ⟨fun h => h, fun h => h, fun h => h⟩

theorem effectMask_le_trans {m1 m2 m3 : EffectMask}
    (h12 : EffectMask.le m1 m2) (h23 : EffectMask.le m2 m3) :
    EffectMask.le m1 m3 :=
  ⟨fun h => h23.1 (h12.1 h), fun h => h23.2.1 (h12.2.1 h), fun h => h23.2.2 (h12.2.2 h)⟩

/-- Uniform codomain of any containment / snapshot boundary `Iso` (pure Lean `partial`,
safe Rust `catch_unwind`, Wasm fuel sandbox, RLBox `copy_and_verify`, or OS process). -/
inductive RawOutcome (E Y W : Type) where
  | candidate (y : Y) (w : W)
  | prodErr   (e : E)
  | trapped

/-- Structured error channel preserving failure provenance without leaking unvalidated `Y`. -/
inductive HybridErr (E : Type) where
  | producerTrapped
  | producerFailed   (e : E)
  | witnessOversized (actual : Nat) (maxAllowed : Nat)
  | rejectedByChecker

/-- Minimal unifying checker kernel (`S1` output-only `W = Unit`, `S2` relational `W = Unit`,
`S3` certificate-carrying `W`). Note that `sound` may assume `wSize w ≤ maxWitness x` because
`evalGate` enforces the O(1) size bound prior to invoking `check`. -/
structure CertifiedGate (X Y W : Type) (Pre : X → Prop) (Spec : X → Y → Prop) where
  maxWitness : X → Nat
  wSize      : W → Nat
  check      : X → Y → W → Bool
  sound      : ∀ x y w, Pre x → wSize w ≤ maxWitness x → check x y w = true → Spec x y

def evalGate {X Y W E : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    (g : CertifiedGate X Y W Pre Spec) (x : X) (raw : RawOutcome E Y W) :
    Except (HybridErr E) Y :=
  match raw with
  | .trapped => .error .producerTrapped
  | .prodErr e => .error (.producerFailed e)
  | .candidate y w =>
    let actual := g.wSize w
    let limit := g.maxWitness x
    if Nat.ble actual limit then
      if g.check x y w then .ok y else .error .rejectedByChecker
    else
      .error (.witnessOversized actual limit)

theorem evalGate_sound {X Y W E : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    (g : CertifiedGate X Y W Pre Spec) (x : X) (raw : RawOutcome E Y W) (y : Y)
    (hPre : Pre x) (hOk : evalGate g x raw = .ok y) :
    Spec x y := by
  unfold evalGate at hOk
  cases raw with
  | trapped => cases hOk
  | prodErr _ => cases hOk
  | candidate yc wc =>
    dsimp only at hOk
    cases hBle : Nat.ble (g.wSize wc) (g.maxWitness x) with
    | false =>
      rw [hBle] at hOk
      cases hOk
    | true =>
      simp only [hBle, ↓reduceIte] at hOk
      cases hChk : g.check x yc wc with
      | false =>
        simp only [hChk, Bool.false_eq_true, ↓reduceIte] at hOk
        cases hOk
      | true =>
        simp only [hChk, ↓reduceIte] at hOk
        injection hOk with hEq
        subst hEq
        exact g.sound x yc wc hPre (Nat.le_of_ble_eq_true hBle) hChk

theorem evalGate_rejects_oversized_without_check
    {X Y W E : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    (g : CertifiedGate X Y W Pre Spec) (x : X) (y : Y) (w : W)
    (hOver : g.maxWitness x < g.wSize w) :
    evalGate (E := E) g x (.candidate y w) =
      .error (.witnessOversized (g.wSize w) (g.maxWitness x)) := by
  unfold evalGate
  dsimp only
  have hNotLe : ¬ g.wSize w ≤ g.maxWitness x := Nat.not_le_of_gt hOver
  cases hBle : Nat.ble (g.wSize w) (g.maxWitness x) with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true hBle) hNotLe

/-! ## 2. Combinator 1: Gate-Aware Portfolio Choice (`firstAccepted`) vs. Pre-Gate `orElse` -/

/-- Naive pre-gate choice: picks the first producer that returns `.candidate` before checking `g`.
If producer 1 emits an invalid candidate `(y_bad, w_bad)`, producer 2 is never consulted! -/
def naivePreGateChoice {E Y W : Type} : List (RawOutcome E Y W) → RawOutcome E Y W
  | [] => .trapped
  | r :: rs =>
    match r with
    | .candidate y w => .candidate y w
    | _ => naivePreGateChoice rs

/-- Gate-aware portfolio combinator (`S6`): evaluates `evalGate g x` across candidates in order,
short-circuiting on the first gate-accepted output `.ok y`. -/
def firstAccepted {X Y W E : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    (g : CertifiedGate X Y W Pre Spec) (x : X) :
    List (RawOutcome E Y W) → Except (HybridErr E) Y
  | [] => .error .producerTrapped
  | r :: rs =>
    match evalGate g x r with
    | .ok y => .ok y
    | .error e =>
      match rs with
      | [] => .error e
      | _ :: _ => firstAccepted g x rs

theorem naive_precheck_orelse_drops_valid_backup :
    let g : CertifiedGate Nat Nat Unit (fun _ => True) (fun x y => y = x) :=
      { maxWitness := fun _ => 0
        wSize := fun _ => 0
        check := fun x y _ => Nat.beq y x
        sound := fun _ _ _ _ _ h => Nat.eq_of_beq_eq_true h }
    let cands : List (RawOutcome Unit Nat Unit) := [.candidate 999 (), .candidate 7 ()]
    evalGate g 7 (naivePreGateChoice cands) = .error .rejectedByChecker ∧
    firstAccepted g 7 cands = .ok 7 := by
  exact ⟨rfl, rfl⟩

theorem firstAccepted_sound {X Y W E : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    (g : CertifiedGate X Y W Pre Spec) (x : X) (cands : List (RawOutcome E Y W)) (y : Y)
    (hPre : Pre x) (hOk : firstAccepted g x cands = .ok y) :
    Spec x y := by
  induction cands with
  | nil => cases hOk
  | cons hd tl ih =>
    unfold firstAccepted at hOk
    cases hHd : evalGate g x hd with
    | ok yHd =>
      rw [hHd] at hOk
      injection hOk with hEq
      subst hEq
      exact evalGate_sound g x hd yHd hPre hHd
    | error e =>
      rw [hHd] at hOk
      cases tl with
      | nil => cases hOk
      | cons hd2 tl2 => exact ih hOk

theorem firstAccepted_ok_iff_exists {X Y W E : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    (g : CertifiedGate X Y W Pre Spec) (x : X) (cands : List (RawOutcome E Y W)) :
    (∃ y, firstAccepted g x cands = .ok y) ↔
    (∃ r ∈ cands, ∃ y, evalGate g x r = .ok y) := by
  induction cands with
  | nil =>
    constructor
    · intro ⟨_, h⟩; cases h
    · intro ⟨_, hMem, _⟩; cases hMem
  | cons hd tl ih =>
    constructor
    · intro ⟨y, hOk⟩
      unfold firstAccepted at hOk
      cases hHd : evalGate g x hd with
      | ok yHd =>
        rw [hHd] at hOk
        injection hOk with hEq
        subst hEq
        exact ⟨hd, List.Mem.head _, yHd, hHd⟩
      | error e =>
        rw [hHd] at hOk
        cases tl with
        | nil => cases hOk
        | cons hd2 tl2 =>
          have ⟨r, hMem, yr, hYr⟩ := ih.mp ⟨y, hOk⟩
          exact ⟨r, List.Mem.tail _ hMem, yr, hYr⟩
    · intro ⟨r, hMem, yr, hYr⟩
      unfold firstAccepted
      cases hHd : evalGate g x hd with
      | ok yHd => exact ⟨yHd, rfl⟩
      | error e =>
        cases hMem with
        | head =>
          rw [hHd] at hYr
          cases hYr
        | tail _ hTl =>
          cases tl with
          | nil => cases hTl
          | cons hd2 tl2 => exact ih.mpr ⟨r, hTl, yr, hYr⟩

/-! ## 3. Combinator 2 & 3: Carrier Projection, Direct Fallback, and Unified `foldGate` (`S4` & `S5`) -/

def toOption {E Y : Type} : Except (HybridErr E) Y → Option Y
  | .ok y => some y
  | .error _ => none

def withFallback {X Y E : Type} (x : X) (res : Except (HybridErr E) Y) (fb : X → Y) : Y :=
  match res with
  | .ok y => y
  | .error _ => fb x

theorem withFallback_total_sound {X Y W E : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    (g : CertifiedGate X Y W Pre Spec) (x : X) (raw : RawOutcome E Y W) (fb : X → Y)
    (hPre : Pre x) (hFb : ∀ x', Pre x' → Spec x' (fb x')) :
    Spec x (withFallback x (evalGate g x raw) fb) := by
  unfold withFallback
  cases hEv : evalGate g x raw with
  | ok y => exact evalGate_sound g x raw y hPre hEv
  | error _ => exact hFb x hPre

/-- `S4` Interleaved Hint Loop as iterated `withFallback ∘ evalGate`: at every step `u`,
either the untrusted hint `h_u` passes `gStep` or verified `fbStep` advances the state,
preserving `Inv` across arbitrary fuel lengths without mutating state on rejected hints. -/
def foldHintSteps {S U W E : Type} {Inv : S → Prop} {StepRel : S → U → S → Prop}
    (gStep : CertifiedGate (S × U) S W (fun su => Inv su.1) (fun su s' => Inv s' ∧ StepRel su.1 su.2 s'))
    (pStep : S → U → RawOutcome E S W)
    (fbStep : S × U → S)
    (s0 : S) : List U → S
  | [] => s0
  | u :: us =>
    let s1 := withFallback (s0, u) (evalGate gStep (s0, u) (pStep s0 u)) fbStep
    foldHintSteps gStep pStep fbStep s1 us

theorem foldHintSteps_preserves_inv {S U W E : Type}
    {Inv : S → Prop} {StepRel : S → U → S → Prop}
    (gStep : CertifiedGate (S × U) S W (fun su => Inv su.1) (fun su s' => Inv s' ∧ StepRel su.1 su.2 s'))
    (pStep : S → U → RawOutcome E S W)
    (fbStep : S × U → S)
    (hFb : ∀ su, Inv su.1 → Inv (fbStep su) ∧ StepRel su.1 su.2 (fbStep su))
    (us : List U) (s0 : S) (hInit : Inv s0) :
    Inv (foldHintSteps gStep pStep fbStep s0 us) := by
  induction us generalizing s0 with
  | nil => exact hInit
  | cons u rest ih =>
    unfold foldHintSteps
    have hStep :=
      withFallback_total_sound gStep (s0, u) (pStep s0 u) fbStep hInit hFb
    exact ih _ hStep.1

/-- `S5` Incremental Prefix-Safe Streaming as short-circuiting `evalGate` fold over state `S`:
emits chunk `c` ONLY after `gChunk` certifies `AccInv s' ∧ ValidChunk s c`, halting immediately
on the first invalid/oversized/trapped chunk so every emitted prefix is valid. -/
def foldStreamPrefix {S U C W E : Type}
    {AccInv : S → Prop} {ValidChunk : C → Prop}
    (gChunk : CertifiedGate (S × U) (S × C) W
      (fun su => AccInv su.1)
      (fun _ sc => AccInv sc.1 ∧ ValidChunk sc.2))
    (pChunk : S → U → RawOutcome E (S × C) W)
    (s0 : S) : List U → List C × Option (HybridErr E)
  | [] => ([], none)
  | u :: us =>
    match evalGate gChunk (s0, u) (pChunk s0 u) with
    | .error err => ([], some err)
    | .ok (s1, c) =>
      let tail := foldStreamPrefix gChunk pChunk s1 us
      (c :: tail.1, tail.2)

theorem foldStreamPrefix_all_emitted_valid {S U C W E : Type}
    {AccInv : S → Prop} {ValidChunk : C → Prop}
    (gChunk : CertifiedGate (S × U) (S × C) W
      (fun su => AccInv su.1)
      (fun _ sc => AccInv sc.1 ∧ ValidChunk sc.2))
    (pChunk : S → U → RawOutcome E (S × C) W)
    (us : List U) (s0 : S) (hInit : AccInv s0) :
    ∀ c ∈ (foldStreamPrefix gChunk pChunk s0 us).1, ValidChunk c := by
  induction us generalizing s0 with
  | nil =>
    intro _ hMem
    cases hMem
  | cons u rest ih =>
    intro c hMem
    unfold foldStreamPrefix at hMem
    cases hEv : evalGate gChunk (s0, u) (pChunk s0 u) with
    | error err =>
      rw [hEv] at hMem
      cases hMem
    | ok sc =>
      rw [hEv] at hMem
      have hSound := evalGate_sound gChunk (s0, u) (pChunk s0 u) sc hInit hEv
      cases hMem with
      | head => exact hSound.2
      | tail _ hTl => exact ih sc.1 hSound.1 c hTl

/-! ## 4. Rung 1.5 (`WellFormed`-Only In-Process Producer) Frame Invariant -/

inductive MirStepOutcome (Mem Ret : Type) where
  | returned (ret : Ret) (mem : Mem)
  | unwound  (mem : Mem)
  | aborted  (mem : Mem)
  | diverged
  | faultUB

def InProcessBodyContract {Mem X Ret : Type}
    (pre : Mem → X → Prop)
    (postRet : Mem → X → Ret → Mem → Prop)
    (mask : EffectMask)
    (f : Mem → X → MirStepOutcome Mem Ret) : Prop :=
  ∀ mem x, pre mem x →
    match f mem x with
    | .returned r mem' => postRet mem x r mem'
    | .unwound _       => mask.noUnwind = false
    | .aborted _       => mask.noAbort  = false
    | .diverged        => mask.terminates = false
    | .faultUB         => False

def rung15Compose {Mem X Y W : Type}
    (f : Mem → X → MirStepOutcome Mem (Y × W))
    (check : Mem → X → Y → W → Bool)
    (commit : Mem → X → Y → Mem)
    (fb : Mem → X → Y × Mem)
    (mem : Mem) (x : X) : MirStepOutcome Mem Y :=
  match f mem x with
  | .returned (y, w) memAfterF =>
    if check memAfterF x y w then .returned y (commit memAfterF x y)
    else
      let r := fb memAfterF x
      .returned r.1 r.2
  | .unwound m => .unwound m
  | .aborted m => .aborted m
  | .diverged  => .diverged
  | .faultUB   => .faultUB

/-- Counterexample: Proving `WellFormed`-only (`postRet := True`, `totalNormal`) on an in-process
`unsafe` producer `f` WITHOUT `CallerMemPreserved` (`mem' = mem`) is UNSOUND when `f` mutates
`CallerMemory` before `check` rejects and `fb` runs! -/
theorem rung15_without_callerMemPreserved_unsound :
    let Pre : Nat → Nat → Prop := fun m _ => m = 10
    let Post : Nat → Nat → Nat → Nat → Prop := fun m x y m' => y = x + m ∧ m' = m
    let badF : Nat → Nat → MirStepOutcome Nat (Nat × Unit) :=
      fun _ x => .returned (x + 999, ()) 0
    let soundCheck : Nat → Nat → Nat → Unit → Bool :=
      fun m x y _ => Nat.beq y (x + m)
    let verifiedFb : Nat → Nat → Nat × Nat :=
      fun m x => (x + m, m)
    -- `badF` is 100% UB-free and totalNormal (`postRet := True`), yet corrupts `mem` (`10 -> 0`)!
    InProcessBodyContract Pre (fun (_ : Nat) (_ : Nat) (_ : Nat × Unit) (_ : Nat) => True)
      EffectMask.totalNormal badF ∧
    (∀ m x y (_ : Unit), soundCheck m x y () = true → Post m x y m) ∧
    (∀ m x, Post m x (verifiedFb m x).1 (verifiedFb m x).2) ∧
    ¬ InProcessBodyContract Pre Post EffectMask.totalNormal
        (rung15Compose badF soundCheck (fun m _ _ => m) verifiedFb) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _; trivial
  · intro m x y _ h; exact ⟨Nat.eq_of_beq_eq_true h, rfl⟩
  · intro m x; exact ⟨rfl, rfl⟩
  · intro hComp
    have h10 := hComp 10 5 rfl
    -- `rung15Compose` returns `(5 + 0, 0) = (5, 0)`, violating `Post 10 5 5 0` (`5 = 15 ∧ 0 = 10`)!
    exact absurd h10.2 (by decide)

/-- Rung 1.5 Soundness Theorem: When `f` proves `WellFormed` + `CallerMemPreserved` (`mem' = mem`)
and `EffectMask.le outerMask fMask` — with ZERO functional correctness proof on `f`'s output `(y, w)` —
in-process composition with verified `check` and `fb` satisfies `Post` and `outerMask` with zero
sandbox or copy overhead! -/
theorem rung15_with_callerMemPreserved_sound
    {Mem X Y W : Type}
    (Pre : Mem → X → Prop)
    (Post : Mem → X → Y → Mem → Prop)
    (fMask outerMask : EffectMask)
    (f : Mem → X → MirStepOutcome Mem (Y × W))
    (check : Mem → X → Y → W → Bool)
    (commit : Mem → X → Y → Mem)
    (fb : Mem → X → Y × Mem)
    (hMask : EffectMask.le outerMask fMask)
    (hF : InProcessBodyContract Pre (fun m _ _ m' => m' = m) fMask f)
    (hCheck : ∀ m x y w, Pre m x → check m x y w = true → Post m x y (commit m x y))
    (hFb : ∀ m x, Pre m x → Post m x (fb m x).1 (fb m x).2) :
    InProcessBodyContract Pre Post outerMask (rung15Compose f check commit fb) := by
  intro mem x hPre
  have hStepF := hF mem x hPre
  unfold rung15Compose
  cases hOut : f mem x with
  | faultUB =>
    rw [hOut] at hStepF
    cases hStepF
  | unwound m' =>
    rw [hOut] at hStepF
    cases hReq : outerMask.noUnwind with
    | false => rfl
    | true =>
      have hImpl := hMask.2.1 hReq
      rw [hImpl] at hStepF
      cases hStepF
  | aborted m' =>
    rw [hOut] at hStepF
    cases hReq : outerMask.noAbort with
    | false => rfl
    | true =>
      have hImpl := hMask.2.2 hReq
      rw [hImpl] at hStepF
      cases hStepF
  | diverged =>
    rw [hOut] at hStepF
    cases hReq : outerMask.terminates with
    | false => rfl
    | true =>
      have hImpl := hMask.1 hReq
      rw [hImpl] at hStepF
      cases hStepF
  | returned yw memAfterF =>
    rw [hOut] at hStepF
    cases yw with
    | mk y w =>
      rw [hStepF]
      dsimp only
      cases hChk : check mem x y w with
      | true =>
        simp only [↓reduceIte]
        exact hCheck mem x y w hPre hChk
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFb mem x hPre

/-! ## 5. Joint `(EffectMask.le ∧ AvailabilityRefines)` Monotone Ratchet Preorder -/

structure HybridComponent (X E Y : Type) where
  mask : EffectMask
  run  : X → Except (HybridErr E) Y

def HybridRefines {X E Y : Type} (Pre : X → Prop) (Spec : X → Y → Prop)
    (cOld cNew : HybridComponent X E Y) : Prop :=
  EffectMask.le cOld.mask cNew.mask ∧
  (∀ x, Pre x → ∀ y, cNew.run x = .ok y → Spec x y) ∧
  (∀ x, Pre x → ∀ y, cOld.run x = .ok y → ∃ y', cNew.run x = .ok y')

theorem hybridRefines_trans {X E Y : Type} {Pre : X → Prop} {Spec : X → Y → Prop}
    {c1 c2 c3 : HybridComponent X E Y}
    (h12 : HybridRefines Pre Spec c1 c2)
    (h23 : HybridRefines Pre Spec c2 c3) :
    HybridRefines Pre Spec c1 c3 := by
  refine ⟨effectMask_le_trans h12.1 h23.1, h23.2.1, ?_⟩
  intro x hPre y1 hOk1
  have ⟨y2, hOk2⟩ := h12.2.2 x hPre y1 hOk1
  exact h23.2.2 x hPre y2 hOk2

#print axioms evalGate_sound
#print axioms evalGate_rejects_oversized_without_check
#print axioms naive_precheck_orelse_drops_valid_backup
#print axioms firstAccepted_sound
#print axioms firstAccepted_ok_iff_exists
#print axioms withFallback_total_sound
#print axioms foldHintSteps_preserves_inv
#print axioms foldStreamPrefix_all_emitted_valid
#print axioms rung15_without_callerMemPreserved_unsound
#print axioms rung15_with_callerMemPreserved_sound
#print axioms hybridRefines_trans

end HybridArch
