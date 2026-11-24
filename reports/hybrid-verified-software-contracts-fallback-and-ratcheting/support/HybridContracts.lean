/-
Copyright 2026 Google LLC / Contributors (Public Reference Mechanization)
Standalone Lean 4.34.1 mechanization of Hybrid Verified Software contracts,
fallback isolation, multi-producer racing, and monotone TCB ratcheting.
Zero Mathlib dependencies; uses core Lean Init only.
-/

namespace HybridFV

/-! ## 1. Core Relations, Checkers, and `Option` Contract Semantics -/

section CoreOption

universe u v w

/-- Functional soundness predicate for a certificate checker `V`. -/
def CheckerSound {X : Type u} {Y : Type v} {W : Type w}
    (R : X → Y → Prop) (V : X → Y → W → Bool) : Prop :=
  ∀ x y w, V x y w = true → R x y

/-- Wrap an untrusted witness-producing component `P : X → Option (Y × W)`
with a certificate checker `V : X → Y → W → Bool`. -/
def optionWrap {X : Type u} {Y : Type v} {W : Type w}
    (V : X → Y → W → Bool) (P : X → Option (Y × W)) (x : X) : Option Y :=
  match P x with
  | none => none
  | some (y, w) => if V x y w then some y else none

/-- Hybrid `Option` contract: when `pre x` holds, `some y` guarantees `R x y`,
while `none` guarantees only the explicit fallback condition `onNone x`
(commonly `fun _ => True` for pure local partial availability). -/
def OptionContract {X : Type u} {Y : Type v}
    (pre : X → Prop) (R : X → Y → Prop) (onNone : X → Prop)
    (f : X → Option Y) : Prop :=
  ∀ x, pre x →
    match f x with
    | none => onNone x
    | some y => R x y

/-- Total component contract returning `Y` unconditionally under `pre`. -/
def TotalContract {X : Type u} {Y : Type v}
    (pre : X → Prop) (R : X → Y → Prop) (f : X → Y) : Prop :=
  ∀ x, pre x → R x (f x)

/-- Soundness of `optionWrap`: for *any* producer `P` (even arbitrary or
adversarial), a sound checker `V` guarantees `OptionContract pre R (fun _ => True)`. -/
theorem optionWrap_sound {X : Type u} {Y : Type v} {W : Type w}
    {pre : X → Prop} {R : X → Y → Prop}
    {V : X → Y → W → Bool}
    (hV : CheckerSound R V) (P : X → Option (Y × W)) :
    OptionContract pre R (fun _ => True) (optionWrap V P) := by
  intro x _
  dsimp [optionWrap]
  cases hP : P x with
  | none => trivial
  | some yw =>
    dsimp
    cases hChk : V x yw.1 yw.2 with
    | false => trivial
    | true =>
      dsimp
      exact hV x yw.1 yw.2 hChk

/-- Availability vacuum: the constant-`none` implementation satisfies
`OptionContract pre R (fun _ => True)` for *every* `pre` and *every* `R`,
including the uninhabitable postcondition `fun _ _ => False`. -/
theorem none_always_satisfies_optionContract {X : Type u} {Y : Type v}
    (pre : X → Prop) (R : X → Y → Prop) :
    OptionContract pre R (fun _ => True) (fun _ => none) := by
  intro _ _
  trivial

/-- Lifting a total spec `R` into `Option Y` by accepting `none` unconditionally. -/
def OptionLift {X : Type u} {Y : Type v} (R : X → Y → Prop) :
    X → Option Y → Prop
  | _, none => True
  | x, some y => R x y

/-- Direct mirror of `PostconditionDichotomy` from `SpecRealizability`. -/
def PostconditionDichotomy {X : Type u} {Y : Type v}
    (pre : X → Prop) (post : X → Y → Prop) : Prop :=
  ∃ x, pre x ∧ (∃ y_ok, post x y_ok) ∧ (∃ y_bad, ¬ post x y_bad)

/-- **Option-Vacuity Blind Spot:** Any spec `R` with one accepted output and
one rejected output satisfies `PostconditionDichotomy` even after `OptionLift`
accepts `none` unconditionally — allowing `fun _ => none` to pass the contract
on every input without ever computing a `some` value. -/
theorem optionLift_satisfies_dichotomy_while_none_passes
    {X : Type u} {Y : Type v}
    (pre : X → Prop) (R : X → Y → Prop)
    (hDich : PostconditionDichotomy pre R) :
    PostconditionDichotomy pre (OptionLift R) ∧
      OptionContract pre R (fun _ => True) (fun _ => none) := by
  let ⟨x, hx, ⟨y_ok, hOk⟩, ⟨y_bad, hBad⟩⟩ := hDich
  refine ⟨⟨x, hx, ⟨some y_ok, hOk⟩, ⟨some y_bad, hBad⟩⟩, ?_⟩
  exact none_always_satisfies_optionContract pre R

/-- Concrete witness refuting `Option` vacuity when a `SomeProgressWitness`
(or verified fallback) is required. -/
def HasSomeWitness {X : Type u} {Y : Type v} (pre : X → Prop)
    (f : X → Option Y) : Prop :=
  ∃ x y, pre x ∧ f x = some y

theorem const_none_fails_some_witness {X : Type u} {Y : Type v}
    (pre : X → Prop) :
    ¬ HasSomeWitness pre (fun (_ : X) => (none : Option Y)) := by
  intro ⟨_, _, _, h⟩
  cases h

/-- Bind two `Option` hybrid stages in series. -/
def optionSeq {A : Type u} {B : Type v} {C : Type w}
    (f : A → Option B) (g : B → Option C) (a : A) : Option C :=
  match f a with
  | none => none
  | some b => g b

/-- **Serial Availability Collapse (2-stage):** If either stage yields `none`,
the pipeline yields `none`; thus one lazy/adversarial `none`-returning stage
forces `0` end-to-end availability even when all other stages are exact. -/
theorem optionSeq_eq_none_of_left_or_right
    {A : Type u} {B : Type v} {C : Type w}
    (f : A → Option B) (g : B → Option C) (a : A) :
    optionSeq f g a = none ↔
      (f a = none ∨ ∃ b, f a = some b ∧ g b = none) := by
  dsimp [optionSeq]
  cases hf : f a with
  | none =>
    constructor
    · intro _; exact Or.inl rfl
    · intro _; rfl
  | some b =>
    constructor
    · intro hg; exact Or.inr ⟨b, rfl, hg⟩
    · intro h
      cases h with
      | inl hNone => cases hNone
      | inr hExists =>
        let ⟨b', hb', hg⟩ := hExists
        injection hb' with hbEq
        subst hbEq
        exact hg

/-- Multi-stage serial pipeline composition over a homogeneous state type `A`. -/
def optionPipeline {A : Type u} : List (A → Option A) → A → Option A
  | [], a => some a
  | stage :: rest, a =>
    match stage a with
    | none => none
    | some a' => optionPipeline rest a'

/-- If any stage in `stages` is the constant-`none` adversary, the entire
pipeline outputs `none` on every input. -/
theorem optionPipeline_adversarial_none_collapse {A : Type u}
    (preStages postStages : List (A → Option A)) (a : A) :
    optionPipeline (preStages ++ (fun _ => none) :: postStages) a = none := by
  induction preStages generalizing a with
  | nil => rfl
  | cons s ss ih =>
    dsimp [optionPipeline]
    cases hs : s a with
    | none => rfl
    | some a' => exact ih a'

/-- On a finite input sample `xs`, count how many inputs return `some _`. -/
def countSome {X : Type u} {Y : Type v} (f : X → Option Y) : List X → Nat
  | [] => 0
  | x :: xs =>
    (match f x with | some _ => 1 | none => 0) + countSome f xs

/-- Availability monotonicity for serial `Option`: `optionSeq f g` produces at
most as many `some` outcomes as `f` alone on any finite workload `xs`. -/
theorem countSome_optionSeq_le_left {A : Type u} {B : Type v} {C : Type w}
    (f : A → Option B) (g : B → Option C) (xs : List A) :
    countSome (optionSeq f g) xs ≤ countSome f xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    dsimp [countSome, optionSeq]
    cases hf : f x with
    | none =>
      dsimp
      exact Nat.add_le_add_left ih 0
    | some b =>
      dsimp
      cases hg : g b with
      | none =>
        rw [Nat.zero_add]
        exact Nat.le_trans ih (Nat.le_add_left _ 1)
      | some _ =>
        dsimp
        exact Nat.add_le_add_left ih 1

theorem countSome_total_full {X : Type u} {Y : Type v}
    (f : X → Y) (xs : List X) :
    countSome (fun x => some (f x)) xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
    dsimp [countSome]
    rw [ih, Nat.add_comm]

end CoreOption

/-! ## 2. Stateful Isolation, Fuel Bounds, Panics, and `verifyOrFallback` -/

section FallbackAndIsolation

/-- Outcome of executing an untrusted stateful producer under a runtime harness. -/
inductive ExecOutcome (S : Type) (A : Type) : Type where
  | ok (val : A) (st' : S)
  | panicked (st' : S)
  | outOfBudget (st' : S)
  deriving Repr

/-- Naive stateful fallback that passes the *post-producer* state `st'` to
`fallback` when the producer fails or its certificate is rejected. -/
def naiveVerifyOrFallbackImpure {S X Y W : Type}
    (V : X → Y → W → Bool)
    (P : S → X → ExecOutcome S (Y × W))
    (fallback : S → X → Y × S)
    (st : S) (x : X) : Y × S :=
  match P st x with
  | .ok (y, w) st' =>
    if V x y w then (y, st') else fallback st' x
  | .panicked st' => fallback st' x
  | .outOfBudget st' => fallback st' x

/-- **State-Pollution Counterexample:** Even with a 100% sound checker
(`V x y w := y == x + 1` -> never accepts garbage) and a 100% verified fallback
(`fallback st x := (x + st, st)` preserving invariant `st = 0`), an unverified
producer `badImpureProducer` that increments `st` before failing/returning an
unverified certificate causes `naiveVerifyOrFallbackImpure` to violate both the
functional postcondition (`y = x`) and the state invariant (`st' = 0`). -/
def badImpureProducer (st x : Nat) : ExecOutcome Nat (Nat × Nat) :=
  .ok (x + 99, 0) (st + 1)

def simpleChecker (x y w : Nat) : Bool :=
  Nat.beq y (x + 1) && Nat.beq w (x + 1)

def pureFallback (st x : Nat) : Nat × Nat :=
  (x + st, st)

theorem naive_impure_fallback_state_pollution :
    let spec : Nat → Nat → Nat → Nat → Prop :=
      fun x st y st' => y = x + st ∧ st' = st
    (∀ x y w, simpleChecker x y w = true → y = x + 1) ∧
    (∀ st x, spec x st (pureFallback st x).1 (pureFallback st x).2) ∧
    ¬ spec 10 0
        (naiveVerifyOrFallbackImpure simpleChecker badImpureProducer pureFallback 0 10).1
        (naiveVerifyOrFallbackImpure simpleChecker badImpureProducer pureFallback 0 10).2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y w h
    simp [simpleChecker] at h
    exact h.1
  · intro st x
    exact ⟨rfl, rfl⟩
  · intro hBad
    dsimp [naiveVerifyOrFallbackImpure, badImpureProducer, simpleChecker, pureFallback] at hBad
    cases hBad.2

/-- Small-step state machine modeling bounded-fuel execution of an untrusted
producer vs unbounded loops. -/
structure MeteredMachine (M : Type) (R : Type) where
  step : M → Option M
  extract : M → Option R

def runFuel {M R : Type} (mach : MeteredMachine M R) : Nat → M → Option R
  | 0, m => mach.extract m
  | n + 1, m =>
    match mach.extract m with
    | some r => some r
    | none =>
      match mach.step m with
      | none => none
      | some m' => runFuel mach n m'

/-- Unbounded loop machine (`step m = some (m + 1)`, `extract _ = none`) never
produces a result for *any* finite fuel budget `n`, demonstrating why raw
non-metered untrusted calls violate `EffectMask.terminates = true`. -/
def spinMachine : MeteredMachine Nat (Nat × Nat) where
  step := fun n => some (n + 1)
  extract := fun _ => none

theorem spinMachine_never_halts (budget init : Nat) :
    runFuel spinMachine budget init = none := by
  induction budget generalizing init with
  | zero => rfl
  | succ n ih =>
    dsimp [runFuel, spinMachine]
    exact ih (init + 1)

/-- Isolated, fuel-metered `verifyOrFallback` boundary:
1. Executes producer `P` inside an isolated state view (either snapshot/rollback
   or pure/read-only borrow of `(st, x)`), capturing panics/OOM/timeouts as
   `none` without modifying caller `st`.
2. Checks `(y, w)` with `V st x y w`.
3. Only if `V` accepts does it apply a verified state-transition/commit or
   return `(y, st_ok)`; on `none` or rejected check, runs verified `fallback st x`. -/
def isolatedVerifyOrFallback {S X Y W : Type}
    (V : S → X → Y → W → Bool)
    (isolatedMeteredP : Nat → S → X → ExecOutcome Unit (Y × W))
    (budget : Nat)
    (commitState : S → X → Y → S)
    (fallback : S → X → Y × S)
    (st : S) (x : X) : Y × S :=
  match isolatedMeteredP budget st x with
  | .ok (y, w) () =>
    if V st x y w then (y, commitState st x y) else fallback st x
  | .panicked () => fallback st x
  | .outOfBudget () => fallback st x

/-- **Soundness and Unconditional Totality of Isolated `verifyOrFallback`:**
For *any* (even panicking, diverging, or garbage-emitting) isolated producer
`isolatedMeteredP` and *any* `budget`, `isolatedVerifyOrFallback` always returns
a valid `(y, st')` satisfying `Post st x y st'` — provided `V` implies `Post`
at `commitState` and `fallback` satisfies `Post`. -/
theorem isolatedVerifyOrFallback_sound_and_total {S X Y W : Type}
    {Pre : S → X → Prop} {Post : S → X → Y → S → Prop}
    {V : S → X → Y → W → Bool}
    {commitState : S → X → Y → S}
    {fallback : S → X → Y × S}
    (hV : ∀ st x y w, Pre st x → V st x y w = true → Post st x y (commitState st x y))
    (hFallback : ∀ st x, Pre st x → Post st x (fallback st x).1 (fallback st x).2)
    (isolatedMeteredP : Nat → S → X → ExecOutcome Unit (Y × W))
    (budget : Nat) :
    ∀ st x, Pre st x →
      let res := isolatedVerifyOrFallback V isolatedMeteredP budget commitState fallback st x
      Post st x res.1 res.2 := by
  intro st x hPre
  dsimp [isolatedVerifyOrFallback]
  cases hP : isolatedMeteredP budget st x with
  | panicked u =>
    cases u
    exact hFallback st x hPre
  | outOfBudget u =>
    cases u
    exact hFallback st x hPre
  | ok yw u =>
    cases u
    dsimp
    cases hChk : V st x yw.1 yw.2 with
    | false =>
      dsimp
      exact hFallback st x hPre
    | true =>
      dsimp
      exact hV st x yw.1 yw.2 hPre hChk

end FallbackAndIsolation

/-! ## 3. Multi-Producer Hedging / Racing (`raceAndVerify`) -/

section Racing

universe u v w

/-- Try heterogeneous untrusted producers in sequence until one emits `(y, w)`
accepted by `V`; return `none` if all fail or are rejected. -/
def raceProducers {X : Type u} {Y : Type v} {W : Type w}
    (V : X → Y → W → Bool) :
    List (X → Option (Y × W)) → X → Option Y
  | [], _ => none
  | p :: ps, x =>
    match p x with
    | some (y, w) => if V x y w then some y else raceProducers V ps x
    | none => raceProducers V ps x

/-- Racing wrapper backed by a verified total fallback `F`. -/
def raceOrFallback {X : Type u} {Y : Type v} {W : Type w}
    (V : X → Y → W → Bool)
    (ps : List (X → Option (Y × W)))
    (F : X → Y) (x : X) : Y :=
  match raceProducers V ps x with
  | some y => y
  | none => F x

theorem raceProducers_sound {X : Type u} {Y : Type v} {W : Type w}
    {pre : X → Prop} {R : X → Y → Prop}
    {V : X → Y → W → Bool} (hV : CheckerSound R V)
    (ps : List (X → Option (Y × W))) :
    OptionContract pre R (fun _ => True) (raceProducers V ps) := by
  intro x _
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    dsimp [raceProducers]
    cases hp : p x with
    | none => exact ih
    | some yw =>
      dsimp
      cases hChk : V x yw.1 yw.2 with
      | false =>
        dsimp
        exact ih
      | true =>
        dsimp
        exact hV x yw.1 yw.2 hChk

theorem raceOrFallback_sound_and_total {X : Type u} {Y : Type v} {W : Type w}
    {pre : X → Prop} {R : X → Y → Prop}
    {V : X → Y → W → Bool} (hV : CheckerSound R V)
    (ps : List (X → Option (Y × W)))
    (F : X → Y) (hF : TotalContract pre R F) :
    TotalContract pre R (raceOrFallback V ps F) := by
  intro x hPre
  dsimp [raceOrFallback]
  have hRace := raceProducers_sound (pre := pre) hV ps x hPre
  cases hRes : raceProducers V ps x with
  | none => exact hF x hPre
  | some y =>
    rw [hRes] at hRace
    exact hRace

/-- **Availability Amplification:** `raceProducers` returns `some _` on `x` if
and only if *at least one* producer in `ps` returns a `V`-accepted witness, so
one working producer rescues arbitrarily many broken/adversarial peers. -/
theorem raceProducers_isSome_iff {X : Type u} {Y : Type v} {W : Type w}
    (V : X → Y → W → Bool) (ps : List (X → Option (Y × W))) (x : X) :
    (∃ y, raceProducers V ps x = some y) ↔
      (∃ p ∈ ps, ∃ y w, p x = some (y, w) ∧ V x y w = true) := by
  induction ps with
  | nil =>
    constructor
    · intro ⟨y, hy⟩
      dsimp [raceProducers] at hy
      cases hy
    · intro ⟨_, hp, _⟩
      cases hp
  | cons p ps ih =>
    constructor
    · intro ⟨y, hy⟩
      dsimp [raceProducers] at hy
      cases hp : p x with
      | none =>
        rw [hp] at hy
        let ⟨p', hpMem, y', w', hp', hV'⟩ := ih.mp ⟨y, hy⟩
        exact ⟨p', List.Mem.tail _ hpMem, y', w', hp', hV'⟩
      | some yw =>
        rw [hp] at hy
        dsimp at hy
        cases hChk : V x yw.1 yw.2 with
        | true =>
          exact ⟨p, List.Mem.head _, yw.1, yw.2, hp, hChk⟩
        | false =>
          rw [hChk] at hy
          dsimp at hy
          let ⟨p', hpMem, y', w', hp', hV'⟩ := ih.mp ⟨y, hy⟩
          exact ⟨p', List.Mem.tail _ hpMem, y', w', hp', hV'⟩
    · intro ⟨p', hpMem, y', w', hp', hV'⟩
      cases hpMem with
      | head =>
        dsimp [raceProducers]
        rw [hp']
        dsimp
        rw [hV']
        exact ⟨y', rfl⟩
      | tail _ hpTail =>
        dsimp [raceProducers]
        cases hp : p x with
        | none =>
          dsimp
          exact ih.mpr ⟨p', hpTail, y', w', hp', hV'⟩
        | some yw =>
          dsimp
          cases hChk : V x yw.1 yw.2 with
          | true =>
            dsimp
            exact ⟨yw.1, rfl⟩
          | false =>
            dsimp
            exact ih.mpr ⟨p', hpTail, y', w', hp', hV'⟩

end Racing

/-! ## 4. The 4-Rung Hybrid Assurance Ladder, `EffectMask`, and Monotone Ratcheting -/

section RatchetLadder

/-- Effect mask mirroring Anneal `FnContract.EffectMask`. -/
structure EffectMask where
  terminates : Bool
  noUnwind   : Bool
  noAbort    : Bool
  deriving DecidableEq, Repr

/-- Mask refinement order: `mImpl ≤ mReq` means `mImpl` satisfies every
effect ban demanded by `mReq` (stronger implementations enforce more `true`
restrictions). -/
def EffectMask.le (mImpl mReq : EffectMask) : Prop :=
  (mReq.terminates = true → mImpl.terminates = true) ∧
  (mReq.noUnwind   = true → mImpl.noUnwind   = true) ∧
  (mReq.noAbort    = true → mImpl.noAbort    = true)

theorem effectMask_le_refl (m : EffectMask) : EffectMask.le m m :=
  ⟨id, id, id⟩

theorem effectMask_le_trans {m₁ m₂ m₃ : EffectMask}
    (h12 : EffectMask.le m₁ m₂) (h23 : EffectMask.le m₂ m₃) :
    EffectMask.le m₁ m₃ :=
  ⟨fun h => h12.1 (h23.1 h), fun h => h12.2.1 (h23.2.1 h), fun h => h12.2.2 (h23.2.2 h)⟩

/-- Lifting a verified total component (`Y`) into an `Option Y` interface
preserves outer caller contracts unconditionally. -/
theorem totalContract_refines_optionContract {X Y : Type}
    {pre : X → Prop} {R : X → Y → Prop}
    {f : X → Y} (hf : TotalContract pre R f) :
    OptionContract pre R (fun _ => True) (fun x => some (f x)) := by
  intro x hPre
  exact hf x hPre

/-- Trusted Computing Base audit items along the 4-rung hybrid ladder. -/
inductive TcbItem : Type where
  | specAndKernel
  | isolationHarness
  | fallbackCode
  | checkerCode
  | producerCode
  deriving DecidableEq, Repr

def tcbForRung : Nat → List TcbItem
  | 0 => [.specAndKernel, .producerCode]
  | 1 => [.specAndKernel, .isolationHarness, .fallbackCode, .checkerCode]
  | 2 => [.specAndKernel, .isolationHarness]
  | _ => [.specAndKernel]

def SubsetList {α : Type} [DecidableEq α] (xs ys : List α) : Prop :=
  ∀ x, x ∈ xs → x ∈ ys

/-- **Monotone TCB Shrinkage along Rungs 1 → 2 → 3:** Every rung upgrade
strictly shrinks the TCB item set (`tcb(3) ⊂ tcb(2) ⊂ tcb(1)`). (Note that
Rung 0 trusts `producerCode` directly without checker/fallback overhead,
trading audit surface of the producer for simplicity when the producer is tiny.) -/
theorem ratchet_strictly_shrinks_tcb :
    SubsetList (tcbForRung 3) (tcbForRung 2) ∧
    SubsetList (tcbForRung 2) (tcbForRung 1) ∧
    ¬ SubsetList (tcbForRung 2) (tcbForRung 3) ∧
    ¬ SubsetList (tcbForRung 1) (tcbForRung 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp [tcbForRung] at hx ⊢
    exact Or.inl hx
  · intro x hx
    simp [tcbForRung] at hx ⊢
    cases hx with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Or.inl h)
  · intro hSub
    have hMem : TcbItem.isolationHarness ∈ tcbForRung 3 :=
      hSub .isolationHarness (by simp [tcbForRung])
    simp [tcbForRung] at hMem
  · intro hSub
    have hMem : TcbItem.checkerCode ∈ tcbForRung 2 :=
      hSub .checkerCode (by simp [tcbForRung])
    simp [tcbForRung] at hMem

/-- Packaged hybrid component across Rungs 1–3 presenting a uniform total
behavioral interface `(eval : X → Y)` to any verified outer caller. -/
structure VerifiedInterface (X Y : Type) (pre : X → Prop) (R : X → Y → Prop) where
  eval  : X → Y
  sound : TotalContract pre R eval

/-- Rung 1 constructor: checker soundness & fallback soundness are TCB-assumed
(`hCheckerTcb`, `hFallbackTcb`). -/
def mkRung1 {X Y W : Type} {pre : X → Prop} {R : X → Y → Prop}
    (V : X → Y → W → Bool) (P : X → Option (Y × W)) (F : X → Y)
    (hCheckerTcb : CheckerSound R V)
    (hFallbackTcb : TotalContract pre R F) :
    VerifiedInterface X Y pre R where
  eval := fun x =>
    match P x with
    | none => F x
    | some (y, w) => if V x y w then y else F x
  sound := by
    intro x hPre
    dsimp
    cases hP : P x with
    | none => exact hFallbackTcb x hPre
    | some yw =>
      dsimp
      cases hChk : V x yw.1 yw.2 with
      | false =>
        dsimp
        exact hFallbackTcb x hPre
      | true =>
        dsimp
        exact hCheckerTcb x yw.1 yw.2 hChk

/-- Rung 2 constructor: checker and fallback carry machine-checked proofs
(`hCheckerVerified`, `hFallbackVerified`), matching Rung 1's external interface. -/
def mkRung2 {X Y W : Type} {pre : X → Prop} {R : X → Y → Prop}
    (V : X → Y → W → Bool) (P : X → Option (Y × W)) (F : X → Y)
    (hCheckerVerified : CheckerSound R V)
    (hFallbackVerified : TotalContract pre R F) :
    VerifiedInterface X Y pre R :=
  mkRung1 V P F hCheckerVerified hFallbackVerified

/-- Rung 3 constructor: fully verified direct producer (zero runtime checker
or fallback overhead). -/
def mkRung3 {X Y : Type} {pre : X → Prop} {R : X → Y → Prop}
    (impl : X → Y) (hImplVerified : TotalContract pre R impl) :
    VerifiedInterface X Y pre R where
  eval := impl
  sound := hImplVerified

/-- **Spec-Preserving Ratcheting Theorem:** Any outer system `Outer` verified
parametrically against `TotalContract pre R` preserves its outer specification
`OuterPost` identically across every rung transition (Rung 1 → Rung 2 → Rung 3)
with zero re-verification of `Outer`. -/
theorem outer_invariant_preserved_across_ratchet
    {X Y A Z : Type}
    {pre : X → Prop} {R : X → Y → Prop}
    {OuterPre : A → Prop} {OuterPost : A → Z → Prop}
    (outer : (X → Y) → A → Z)
    (hOuterVerified : ∀ (comp : X → Y), TotalContract pre R comp →
      ∀ a, OuterPre a → OuterPost a (outer comp a))
    (iface : VerifiedInterface X Y pre R) :
    ∀ a, OuterPre a → OuterPost a (outer iface.eval a) :=
  hOuterVerified iface.eval iface.sound

end RatchetLadder

end HybridFV

-- Axiom checks across all key exported theorems:
#print axioms HybridFV.optionWrap_sound
#print axioms HybridFV.none_always_satisfies_optionContract
#print axioms HybridFV.optionLift_satisfies_dichotomy_while_none_passes
#print axioms HybridFV.const_none_fails_some_witness
#print axioms HybridFV.optionSeq_eq_none_of_left_or_right
#print axioms HybridFV.optionPipeline_adversarial_none_collapse
#print axioms HybridFV.countSome_optionSeq_le_left
#print axioms HybridFV.countSome_total_full
#print axioms HybridFV.naive_impure_fallback_state_pollution
#print axioms HybridFV.spinMachine_never_halts
#print axioms HybridFV.isolatedVerifyOrFallback_sound_and_total
#print axioms HybridFV.raceProducers_sound
#print axioms HybridFV.raceOrFallback_sound_and_total
#print axioms HybridFV.raceProducers_isSome_iff
#print axioms HybridFV.effectMask_le_refl
#print axioms HybridFV.effectMask_le_trans
#print axioms HybridFV.totalContract_refines_optionContract
#print axioms HybridFV.ratchet_strictly_shrinks_tcb
#print axioms HybridFV.outer_invariant_preserved_across_ratchet
