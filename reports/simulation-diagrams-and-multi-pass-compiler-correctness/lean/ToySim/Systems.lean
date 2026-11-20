import ToySim.Basic

/-!
# Concrete systems used by the examples and counterexamples

Every system here has events and results in `Nat`.  For each system that is
used as the *source* side of a counterexample, its complete set of behaviours
is characterised, so that "the target has a behaviour the source does not
allow" can be checked exactly.
-/

namespace Toy.Sim

variable {E Res : Type}

/-! ## Generic tools (fully proved) -/

/-- If every step of a system is silent, every execution has the empty trace. -/
theorem Star.trace_nil_of_silent {L : LTS E Res}
    (hsil : ∀ s e s', L.step s e s' → e = none)
    {s s' : L.State} {t : List E} (h : Star L s t s') : t = [] := by
  induction h with
  | refl => rfl
  | step hstep _ ht ih =>
    subst ih
    rw [ht, hsil _ _ _ hstep]
    rfl

/-- A system with an initial state and no stuck state never goes wrong. -/
theorem neverGoesWrong_of_no_stuck {L : LTS E Res}
    (hns : ∀ s, ¬ Stuck L s) (hinit : ∃ s, L.init s) : NeverGoesWrong L := by
  intro t h
  rcases h with ⟨_, s, _, _, hstuck⟩ | ⟨_, hno⟩
  · exact hns s hstuck
  · obtain ⟨s, hs⟩ := hinit
    exact hno s hs

/-- If the source never goes wrong and the target has a behaviour that the
source lacks, the target does not refine the source. -/
theorem not_refinedBy_of_extra_behavior {L₁ L₂ : LTS E Res}
    (hsafe : NeverGoesWrong L₁) {b : Behavior E Res}
    (h₂ : HasBehavior L₂ b) (h₁ : ¬ HasBehavior L₁ b) : ¬ RefinedBy L₁ L₂ :=
  fun href => h₁ (refinedBy_neverGoesWrong_behaviors_subset href hsafe h₂)

/-- A backward step diagram simulates whole target executions when every
source state is safe. -/
theorem bsimStep_star_of_all_safe {L₁ L₂ : LTS E Res} {I : Type}
    {ord : I → I → Prop} {R : I → L₁.State → L₂.State → Prop}
    (hstep : BSimStep L₁ L₂ ord R) (hsafe : ∀ s, Safe L₁ s)
    {s₂ s₂' : L₂.State} {t : List E} (hrun : Star L₂ s₂ t s₂') :
    ∀ i s₁, R i s₁ s₂ → ∃ i' s₁', Star L₁ s₁ t s₁' ∧ R i' s₁' s₂' := by
  induction hrun with
  | refl s => exact fun i s₁ hR => ⟨i, s₁, Star.refl s₁, hR⟩
  | @step _ _ _ e _ _ h _ ht ih =>
    intro i s₁ hR
    obtain ⟨i', s₁', hmove, hR'⟩ := hstep i s₁ _ _ _ hR (hsafe s₁) h
    have hstar : Star L₁ s₁ (obs e) s₁' := by
      rcases hmove with hp | ⟨hs, _⟩
      · exact hp.star
      · exact hs
    obtain ⟨i'', s₁'', hstar', hR''⟩ := ih i' s₁' hR'
    exact ⟨i'', s₁'', by rw [ht]; exact hstar.trans hstar', hR''⟩

/-- If every source state is safe, the source has an initial state, and the
target has a terminating behaviour that the source lacks, then no backward
simulation from the source to the target exists (for any index type, order
and relation). -/
theorem no_backwardSim_of_extra_terminates {L₁ L₂ : LTS E Res}
    (hsafe : ∀ s, Safe L₁ s) (hinit : ∃ s, L₁.init s)
    {t : List E} {r : Res}
    (h₂ : HasBehavior L₂ (.terminates t r)) (h₁ : ¬ HasBehavior L₁ (.terminates t r)) :
    ¬ ∃ (I : Type) (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop),
        IsBackwardSim L₁ L₂ ord R := by
  rintro ⟨I, ord, R, hb⟩
  obtain ⟨s₀', s', h₀', hrun, hfin⟩ := h₂
  obtain ⟨s₀, h₀⟩ := hinit
  obtain ⟨i, s₁, hs₁, hR⟩ := hb.initMatch s₀ s₀' h₀ h₀'
  obtain ⟨i', s₁', hrun₁, hR'⟩ := bsimStep_star_of_all_safe hb.step hsafe hrun i s₁ hR
  obtain ⟨s₁'', hrun₂, hfin₁⟩ := hb.final i' s₁' s' r hR' (hsafe s₁') hfin
  exact h₁ ⟨s₁, s₁'', hs₁, by simpa using hrun₁.trans hrun₂, hfin₁⟩

namespace Ex

/-! ## One-state systems -/

/-- One state, no step, final with result `r`: terminates at once. -/
abbrev Done (r : Nat) : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun _ r' => r' = r

/-- One state with a silent self-loop, never final: diverges at once. -/
abbrev Loop : LTS Nat Nat where
  State := Unit
  step := fun _ e _ => e = none
  init := fun _ => True
  final := fun _ _ => False

/-- One state, no step, not final: goes wrong at once. -/
abbrev StuckNow : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun _ _ => False

/-- No initial state at all. -/
abbrev NoInit : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => False
  final := fun _ _ => False

/-- One state that emits the event `0` forever, never final. -/
abbrev Chatter : LTS Nat Nat where
  State := Unit
  step := fun _ e _ => e = some 0
  init := fun _ => True
  final := fun _ _ => False

/-- One state, no step, final with both results `0` and `1`. -/
abbrev TwoResults : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun _ r => r = 0 ∨ r = 1

theorem done_behavior (r : Nat) (b : Behavior Nat Nat) :
    HasBehavior (Done r) b ↔ b = .terminates [] r := by
  constructor
  · intro h
    cases b with
    | terminates t r' =>
      obtain ⟨_, s, _, hstar, hfin⟩ := h
      obtain ⟨rfl, _⟩ := Star.of_noStep (L := Done r) (fun _ _ h => h) hstar
      have hr : r' = r := hfin
      rw [hr]
    | diverges t =>
      obtain ⟨_, _, _, _, f, _, hf⟩ := h
      exact (hf 0).elim
    | goesWrong t =>
      rcases h with ⟨_, s, _, _, hstuck⟩ | ⟨_, hno⟩
      · exact (hstuck.2 r rfl).elim
      · exact (hno () trivial).elim
  · rintro rfl
    exact ⟨(), (), trivial, Star.refl _, rfl⟩

theorem loop_behavior (b : Behavior Nat Nat) :
    HasBehavior Loop b ↔ b = .diverges [] := by
  constructor
  · intro h
    cases b with
    | terminates t r =>
      obtain ⟨_, _, _, _, hfin⟩ := h
      exact hfin.elim
    | diverges t =>
      obtain ⟨_, _, _, hstar, _⟩ := h
      have ht := Star.trace_nil_of_silent (L := Loop) (fun _ _ _ h => h) hstar
      rw [ht]
    | goesWrong t =>
      rcases h with ⟨_, s, _, _, hstuck⟩ | ⟨_, hno⟩
      · exact (hstuck.1 none () rfl).elim
      · exact (hno () trivial).elim
  · rintro rfl
    exact ⟨(), (), trivial, Star.refl _, fun _ => (), rfl, fun _ => rfl⟩

theorem stuckNow_behavior (b : Behavior Nat Nat) :
    HasBehavior StuckNow b ↔ b = .goesWrong [] := by
  constructor
  · intro h
    cases b with
    | terminates t r =>
      obtain ⟨_, _, _, _, hfin⟩ := h
      exact hfin.elim
    | diverges t =>
      obtain ⟨_, _, _, _, f, _, hf⟩ := h
      exact (hf 0).elim
    | goesWrong t =>
      rcases h with ⟨_, s, _, hstar, _⟩ | ⟨ht, _⟩
      · obtain ⟨rfl, _⟩ := Star.of_noStep (L := StuckNow) (fun _ _ h => h) hstar
        rfl
      · rw [ht]
  · rintro rfl
    exact Or.inl ⟨(), (), trivial, Star.refl _, fun _ _ h => h, fun _ h => h⟩

theorem noInit_behavior (b : Behavior Nat Nat) :
    HasBehavior NoInit b ↔ b = .goesWrong [] := by
  constructor
  · intro h
    cases b with
    | terminates t r =>
      obtain ⟨_, _, h₀, _, _⟩ := h
      exact h₀.elim
    | diverges t =>
      obtain ⟨_, _, h₀, _, _⟩ := h
      exact h₀.elim
    | goesWrong t =>
      rcases h with ⟨_, _, h₀, _, _⟩ | ⟨ht, _⟩
      · exact h₀.elim
      · rw [ht]
  · rintro rfl
    exact Or.inr ⟨rfl, fun _ h => h⟩

/-- `Chatter` has no behaviour at all in this model: its only run emits
infinitely many events, and such behaviours are not modelled. -/
theorem chatter_no_behavior (b : Behavior Nat Nat) : ¬ HasBehavior Chatter b := by
  intro h
  cases b with
  | terminates t r =>
    obtain ⟨_, _, _, _, hfin⟩ := h
    exact hfin.elim
  | diverges t =>
    obtain ⟨_, _, _, _, f, _, hf⟩ := h
    exact absurd (hf 0) (by simp)
  | goesWrong t =>
    rcases h with ⟨_, s, _, _, hstuck⟩ | ⟨_, hno⟩
    · exact hstuck.1 (some 0) () rfl
    · exact hno () trivial

theorem done_neverGoesWrong (r : Nat) : NeverGoesWrong (Done r) := by
  intro t h
  have := (done_behavior r _).1 h
  cases this

theorem loop_neverGoesWrong : NeverGoesWrong Loop := by
  intro t h
  have := (loop_behavior _).1 h
  cases this

theorem done_all_safe (r : Nat) (s : (Done r).State) : Safe (Done r) s :=
  fun _ _ => Or.inl ⟨r, rfl⟩

theorem loop_all_safe (s : Loop.State) : Safe Loop s :=
  fun _ _ => Or.inr ⟨none, (), rfl⟩

/-! ## Two-state systems -/

/-- Two states: one step labelled `e` from `false` (initial) to `true`
(final with result `r`).  Its only behaviour is "emit `obs e`, return `r`". -/
abbrev OneStep (e : Option Nat) (r : Nat) : LTS Nat Nat where
  State := Bool
  step := fun s e' s' => s = false ∧ e' = e ∧ s' = true
  init := fun s => s = false
  final := fun s r' => s = true ∧ r' = r

theorem oneStep_star_true {e : Option Nat} {r : Nat} {t : List Nat} {s : Bool}
    (h : Star (OneStep e r) true t s) : t = [] ∧ s = true :=
  Star.of_noStep (L := OneStep e r) (fun _ _ h => Bool.noConfusion h.1) h

theorem oneStep_star_false {e : Option Nat} {r : Nat} {t : List Nat} {s : Bool}
    (h : Star (OneStep e r) false t s) :
    (t = [] ∧ s = false) ∨ (t = obs e ∧ s = true) := by
  rcases h.inv with h | ⟨e', s₁, t₁, hstep, hstar, rfl⟩
  · exact Or.inl h
  · obtain ⟨_, he, hs₁⟩ := hstep
    subst he hs₁
    obtain ⟨rfl, rfl⟩ := oneStep_star_true hstar
    exact Or.inr ⟨by simp, rfl⟩

theorem oneStep_behavior (e : Option Nat) (r : Nat) (b : Behavior Nat Nat) :
    HasBehavior (OneStep e r) b ↔ b = .terminates (obs e) r := by
  constructor
  · intro h
    cases b with
    | terminates t r' =>
      obtain ⟨s₀, s, h₀, hstar, hfin⟩ := h
      have h₀' : s₀ = false := h₀
      subst h₀'
      rcases oneStep_star_false hstar with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
      · exact Bool.noConfusion hfin.1
      · rw [hfin.2]
    | diverges t =>
      obtain ⟨s₀, s, h₀, hstar, f, hf0, hf⟩ := h
      have h1 : f 1 = true := (hf 0).2.2
      have h2 : f 1 = false := (hf 1).1
      rw [h1] at h2
      exact Bool.noConfusion h2
    | goesWrong t =>
      rcases h with ⟨s₀, s, h₀, hstar, hstuck⟩ | ⟨_, hno⟩
      · have h₀' : s₀ = false := h₀
        subst h₀'
        rcases oneStep_star_false hstar with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact (hstuck.1 e true ⟨rfl, rfl, rfl⟩).elim
        · exact (hstuck.2 r ⟨rfl, rfl⟩).elim
      · exact (hno false rfl).elim
  · rintro rfl
    exact ⟨false, true, rfl, Star.single (L := OneStep e r) ⟨rfl, rfl, rfl⟩, rfl, rfl⟩

theorem oneStep_no_stuck (e : Option Nat) (r : Nat) (s : (OneStep e r).State) :
    ¬ Stuck (OneStep e r) s := by
  intro h
  cases s with
  | false => exact h.1 e true ⟨rfl, rfl, rfl⟩
  | true => exact h.2 r ⟨rfl, rfl⟩

theorem oneStep_neverGoesWrong (e : Option Nat) (r : Nat) : NeverGoesWrong (OneStep e r) :=
  neverGoesWrong_of_no_stuck (oneStep_no_stuck e r) ⟨false, rfl⟩

theorem oneStep_all_safe (e : Option Nat) (r : Nat) (s : (OneStep e r).State) :
    Safe (OneStep e r) s :=
  safe_of_no_stuck (oneStep_no_stuck e r) s

/-- Two states: a silent step from `false` (initial) to `true`, which is
stuck and not final.  Goes wrong after one silent step. -/
abbrev Crash : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = false ∧ e = none ∧ s' = true
  init := fun s => s = false
  final := fun _ _ => False

/-- Two states: the initial state `false` emits the event `1` and moves to
`true`, which is stuck and not final.  Goes wrong after the trace `[1]`. -/
abbrev EmitThenStuck : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = false ∧ e = some 1 ∧ s' = true
  init := fun s => s = false
  final := fun _ _ => False

/-- Two states: a silent step from `false` (initial) to `true`, and a silent
self-loop on `true`; never final.  Diverges silently. -/
abbrev Spin : LTS Nat Nat where
  State := Bool
  step := fun _ e s' => e = none ∧ s' = true
  init := fun s => s = false
  final := fun _ _ => False

/-- Two initial states, no step: `false` is final with result `0`, `true` is
final with result `1`. -/
abbrev TwoInits : LTS Nat Nat where
  State := Bool
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun s r => (s = false ∧ r = 0) ∨ (s = true ∧ r = 1)

/-- The initial state `false` is final with result `0` *and* can step
silently to `true`, which is final with result `1`. -/
abbrev FinalSteps : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = false ∧ e = none ∧ s' = true
  init := fun s => s = false
  final := fun s r => (s = false ∧ r = 0) ∨ (s = true ∧ r = 1)

/-! ## A three-state branching system -/

/-- State names for three-state systems. -/
inductive Three where
  | root | left | right
  deriving DecidableEq

/-- From the initial state `root`, a step labelled `e₁` leads to `left`
(final with result `r₁`) and a step labelled `e₂` leads to `right` (final
with result `r₂`). -/
abbrev TwoBranch (e₁ e₂ : Option Nat) (r₁ r₂ : Nat) : LTS Nat Nat where
  State := Three
  step := fun s e s' => s = .root ∧ ((e = e₁ ∧ s' = .left) ∨ (e = e₂ ∧ s' = .right))
  init := fun s => s = .root
  final := fun s r => (s = .left ∧ r = r₁) ∨ (s = .right ∧ r = r₂)

/-- The second branch is a terminating behaviour of `TwoBranch`. -/
theorem twoBranch_right_behavior (e₁ e₂ : Option Nat) (r₁ r₂ : Nat) :
    HasBehavior (TwoBranch e₁ e₂ r₁ r₂) (.terminates (obs e₂) r₂) :=
  ⟨.root, .right, rfl,
    Star.single (L := TwoBranch e₁ e₂ r₁ r₂) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem twoBranch_initDeterminate (e₁ e₂ : Option Nat) (r₁ r₂ : Nat) :
    InitDeterminate (TwoBranch e₁ e₂ r₁ r₂) := by
  intro s s' hs hs'
  have h1 : s = .root := hs
  have h2 : s' = .root := hs'
  rw [h1, h2]

theorem twoBranch_finalNoStep (e₁ e₂ : Option Nat) (r₁ r₂ : Nat) :
    FinalNoStep (TwoBranch e₁ e₂ r₁ r₂) := by
  intro s r hfin e s' hstep
  have hroot : s = .root := hstep.1
  subst hroot
  rcases hfin with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h

theorem twoBranch_finalDeterminate (e₁ e₂ : Option Nat) (r₁ r₂ : Nat) :
    FinalDeterminate (TwoBranch e₁ e₂ r₁ r₂) := by
  intro s r r' h h'
  rcases h with ⟨hs, hr⟩ | ⟨hs, hr⟩ <;> rcases h' with ⟨hs', hr'⟩ | ⟨hs', hr'⟩
  · rw [hr, hr']
  · rw [hs] at hs'; cases hs'
  · rw [hs] at hs'; cases hs'
  · rw [hr, hr']

/-- The relation used to simulate `OneStep e r` by `TwoBranch e e₂ r r₂`:
before the step ↦ `root`, after the step ↦ `left`. -/
def branchRel : Unit → Bool → Three → Prop :=
  fun _ s s' => (s = false ∧ s' = .root) ∨ (s = true ∧ s' = .left)

/-- `OneStep e r` is forward-simulated by `TwoBranch e e₂ r r₂` (which has
an additional branch), without stuttering. -/
theorem oneStep_twoBranch_isForwardSim (e e₂ : Option Nat) (r r₂ : Nat) :
    IsForwardSim (OneStep e r) (TwoBranch e e₂ r r₂) (fun _ _ => False) branchRel where
  wf := ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  init := by
    intro s hs
    have hs' : s = false := hs
    exact ⟨(), .root, rfl, Or.inl ⟨hs', rfl⟩⟩
  final := by
    intro _ s s' r' hR hfin
    have hs : s = true := hfin.1
    have hr : r' = r := hfin.2
    rcases hR with ⟨h, _⟩ | ⟨_, h'⟩
    · rw [hs] at h; cases h
    · exact Or.inl ⟨h', hr⟩
  step := by
    intro _ s s' e' s₁ hR hstep
    obtain ⟨hs, he, hs₁⟩ := hstep
    rcases hR with ⟨_, h'⟩ | ⟨h, _⟩
    · subst h' he hs₁
      exact ⟨(), .left,
        Or.inl (Plus.single (L := TwoBranch e' e₂ r r₂) ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩),
        Or.inr ⟨rfl, rfl⟩⟩
    · rw [hs] at h; cases h

/-! ## A program that reads one input and returns it

Three systems with the same observable meaning: read an event `n` from the
environment, then return `n`.  `Src` takes a silent start-up step first;
`Tgt` takes a silent step after the read; `Mid` sits between them and is
internally nondeterministic. -/

inductive SrcSt where
  | start | ready | done (n : Nat)

inductive SrcStep : SrcSt → Option Nat → SrcSt → Prop where
  | boot : SrcStep .start none .ready
  | read (n : Nat) : SrcStep .ready (some n) (.done n)

/-- Source program: silent start-up, then read `n` and finish with `n`. -/
abbrev Src : LTS Nat Nat where
  State := SrcSt
  step := SrcStep
  init := fun s => s = .start
  final := fun s r => s = .done r

inductive MidSt where
  | ready | gotA (n : Nat) | gotB (n : Nat) | done (n : Nat)

inductive MidStep : MidSt → Option Nat → MidSt → Prop where
  | readA (n : Nat) : MidStep .ready (some n) (.gotA n)
  | readB (n : Nat) : MidStep .ready (some n) (.gotB n)
  | retA (n : Nat) : MidStep (.gotA n) none (.done n)
  | retB (n : Nat) : MidStep (.gotB n) none (.done n)

/-- Intermediate program: read `n` into one of two internal representations
(chosen nondeterministically), then silently finish with `n`. -/
abbrev Mid : LTS Nat Nat where
  State := MidSt
  step := MidStep
  init := fun s => s = .ready
  final := fun s r => s = .done r

inductive TgtSt where
  | ready | got (n : Nat) | done (n : Nat)

inductive TgtStep : TgtSt → Option Nat → TgtSt → Prop where
  | read (n : Nat) : TgtStep .ready (some n) (.got n)
  | ret (n : Nat) : TgtStep (.got n) none (.done n)

/-- Target program: read `n`, then silently finish with `n`. -/
abbrev Tgt : LTS Nat Nat where
  State := TgtSt
  step := TgtStep
  init := fun s => s = .ready
  final := fun s r => s = .done r

/-- "Every event matches every event": the environment may answer a read
with any value. -/
abbrev AnyInput : Nat → Nat → Prop := fun _ _ => True

/-- Forward relation from `Src` to `Tgt`; the index is `1` before the
start-up step (where the target stutters) and `0` afterwards. -/
inductive SrcTgtRel : Nat → SrcSt → TgtSt → Prop where
  | start : SrcTgtRel 1 .start .ready
  | ready : SrcTgtRel 0 .ready .ready
  | done (n : Nat) : SrcTgtRel 0 (.done n) (.done n)

/-- Forward relation from `Src` to `Mid` (through the `gotA` representation). -/
inductive SrcMidRel : Nat → SrcSt → MidSt → Prop where
  | start : SrcMidRel 1 .start .ready
  | ready : SrcMidRel 0 .ready .ready
  | done (n : Nat) : SrcMidRel 0 (.done n) (.done n)

/-- Forward relation from `Mid` to `Tgt`: both internal representations map
to the same target state. -/
inductive MidTgtRel : Unit → MidSt → TgtSt → Prop where
  | ready : MidTgtRel () .ready .ready
  | gotA (n : Nat) : MidTgtRel () (.gotA n) (.got n)
  | gotB (n : Nat) : MidTgtRel () (.gotB n) (.got n)
  | done (n : Nat) : MidTgtRel () (.done n) (.done n)

/-- Backward relation from `Src` to `Tgt`; the index is `1` at the target
state `got n`, where the source has already finished and stutters.  It
contains every pair of the forward relation `SrcTgtRel` (constructors
`start`, `ready`, `done`), as the flip lemma promises. -/
inductive SrcTgtBackRel : Nat → SrcSt → TgtSt → Prop where
  | start : SrcTgtBackRel 0 .start .ready
  | ready : SrcTgtBackRel 0 .ready .ready
  | got (n : Nat) : SrcTgtBackRel 1 (.done n) (.got n)
  | done (n : Nat) : SrcTgtBackRel 0 (.done n) (.done n)

theorem tgt_read_ret (n : Nat) : Plus Tgt .ready [n] (.done n) :=
  ⟨some n, .got n, [], TgtStep.read n, Star.single (L := Tgt) (TgtStep.ret n), rfl⟩

theorem src_boot_read (n : Nat) : Plus Src .start [n] (.done n) :=
  ⟨none, .ready, [n], SrcStep.boot, Star.single (L := Src) (SrcStep.read n), rfl⟩

theorem mid_readA_retA (n : Nat) : Plus Mid .ready [n] (.done n) :=
  ⟨some n, .gotA n, [], MidStep.readA n, Star.single (L := Mid) (MidStep.retA n), rfl⟩

theorem srcTgt_isForwardSim : IsForwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtRel where
  wf := Nat.lt_wfRel.wf
  init := by
    intro s hs
    have hs' : s = .start := hs
    subst hs'
    exact ⟨1, .ready, rfl, .start⟩
  final := by
    intro i s s' r hR hfin
    have hs : s = .done r := hfin
    subst hs
    cases hR
    rfl
  step := by
    intro i s s' e s₁ hR hstep
    cases hstep with
    | boot =>
      cases hR
      exact ⟨0, .ready, Or.inr ⟨Star.refl _, Nat.zero_lt_one⟩, .ready⟩
    | read n =>
      cases hR
      exact ⟨0, .done n, Or.inl (tgt_read_ret n), .done n⟩

theorem srcMid_isForwardSim : IsForwardSim Src Mid (fun i' i : Nat => i' < i) SrcMidRel where
  wf := Nat.lt_wfRel.wf
  init := by
    intro s hs
    have hs' : s = .start := hs
    subst hs'
    exact ⟨1, .ready, rfl, .start⟩
  final := by
    intro i s s' r hR hfin
    have hs : s = .done r := hfin
    subst hs
    cases hR
    rfl
  step := by
    intro i s s' e s₁ hR hstep
    cases hstep with
    | boot =>
      cases hR
      exact ⟨0, .ready, Or.inr ⟨Star.refl _, Nat.zero_lt_one⟩, .ready⟩
    | read n =>
      cases hR
      exact ⟨0, .done n, Or.inl (mid_readA_retA n), .done n⟩

theorem midTgt_isForwardSim : IsForwardSim Mid Tgt (fun _ _ : Unit => False) MidTgtRel where
  wf := ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  init := by
    intro s hs
    have hs' : s = .ready := hs
    subst hs'
    exact ⟨(), .ready, rfl, .ready⟩
  final := by
    intro i s s' r hR hfin
    have hs : s = .done r := hfin
    subst hs
    cases hR
    rfl
  step := by
    intro i s s' e s₁ hR hstep
    cases hstep with
    | readA n =>
      cases hR
      exact ⟨(), .got n, Or.inl (Plus.single (L := Tgt) (TgtStep.read n)), .gotA n⟩
    | readB n =>
      cases hR
      exact ⟨(), .got n, Or.inl (Plus.single (L := Tgt) (TgtStep.read n)), .gotB n⟩
    | retA n =>
      cases hR
      exact ⟨(), .done n, Or.inl (Plus.single (L := Tgt) (TgtStep.ret n)), .done n⟩
    | retB n =>
      cases hR
      exact ⟨(), .done n, Or.inl (Plus.single (L := Tgt) (TgtStep.ret n)), .done n⟩

theorem srcTgt_isBackwardSim :
    IsBackwardSim Src Tgt (fun i' i : Nat => i' < i) SrcTgtBackRel where
  wf := Nat.lt_wfRel.wf
  initExists := fun _ => ⟨.ready, rfl⟩
  initMatch := by
    intro s₁ s₂ _ h₂
    have h₂' : s₂ = .ready := h₂
    subst h₂'
    exact ⟨0, .start, rfl, .start⟩
  final := by
    intro i s₁ s₂ r hR _ hfin
    have hs : s₂ = .done r := hfin
    subst hs
    cases hR
    exact ⟨.done r, Star.refl _, rfl⟩
  progress := by
    intro i s₁ s₂ hR _
    cases hR with
    | start => exact Or.inr ⟨some 0, .got 0, TgtStep.read 0⟩
    | ready => exact Or.inr ⟨some 0, .got 0, TgtStep.read 0⟩
    | got n => exact Or.inr ⟨none, .done n, TgtStep.ret n⟩
    | done n => exact Or.inl ⟨n, rfl⟩
  step := by
    intro i s₁ s₂ e s₂' hR _ hstep
    cases hstep with
    | read n =>
      cases hR with
      | start => exact ⟨1, .done n, Or.inl (src_boot_read n), .got n⟩
      | ready => exact ⟨1, .done n, Or.inl (Plus.single (L := Src) (SrcStep.read n)), .got n⟩
    | ret n =>
      cases hR
      exact ⟨0, .done n, Or.inr ⟨Star.refl _, Nat.zero_lt_one⟩, .done n⟩

/-- The backward relation contains the forward relation. -/
theorem srcTgtRel_sub_srcTgtBackRel :
    ∀ i s₁ s₂, SrcTgtRel i s₁ s₂ → ∃ i', SrcTgtBackRel i' s₁ s₂ := by
  intro i s₁ s₂ hR
  cases hR with
  | start => exact ⟨0, .start⟩
  | ready => exact ⟨0, .ready⟩
  | done n => exact ⟨0, .done n⟩

theorem src_receptive : Receptive AnyInput Src := by
  intro s a s₁ b hstep _
  cases hstep
  exact ⟨.done b, SrcStep.read b⟩

theorem tgt_determinate : Determinate AnyInput Tgt where
  labels := by
    intro s e₁ s₁ e₂ s₂ h₁ h₂
    cases h₁ <;> cases h₂ <;> trivial
  functional := by
    intro s e s₁ s₂ h₁ h₂
    cases h₁ <;> cases h₂ <;> rfl
  init := by
    intro s s' hs hs'
    have h1 : s = .ready := hs
    have h2 : s' = .ready := hs'
    rw [h1, h2]
  finalNoStep := by
    intro s r hfin e s' hstep
    have hs : s = .done r := hfin
    subst hs
    cases hstep
  finalDet := by
    intro s r r' h h'
    have h1 : s = .done r := h
    have h2 : s = .done r' := h'
    rw [h1] at h2
    exact TgtSt.done.inj h2

/-- The intermediate program is not functional: the read has two successors. -/
theorem mid_not_stepFunctional : ¬ StepFunctional Mid := by
  intro h
  have := h .ready (some 0) (.gotA 0) (.gotB 0) (MidStep.readA 0) (MidStep.readB 0)
  cases this

theorem src_no_stuck (s : Src.State) : ¬ Stuck Src s := by
  intro h
  cases s with
  | start => exact h.1 none .ready SrcStep.boot
  | ready => exact h.1 (some 0) (.done 0) (SrcStep.read 0)
  | done n => exact h.2 n rfl

theorem src_neverGoesWrong : NeverGoesWrong Src :=
  neverGoesWrong_of_no_stuck src_no_stuck ⟨.start, rfl⟩

end Ex

end Toy.Sim
