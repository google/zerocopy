-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Morphism Degeneracy Taxonomy, Admissible Simulation Couplings, and Multi-Step Composition

This module mechanizes the admissibility and anti-degeneracy theory of behavior
morphisms (`π : L₁.Behavior → L₂.Behavior`) in Anneal's Layer 1A/1B refinement
framework (`Trusted/Refinement.lean` and `Trusted/StepResult.lean` at commit
`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`):

1. **Taxonomy of Degenerate Monotone Morphisms (Section 3):**
   Constructs concrete small-step operational counterexamples for all four
   classes of monotone morphisms that satisfy `Monotone π` while trivializing
   `Compiles L₁ L₂ π s t`, `Abstracts L_v L_src π_v v s`, or
   `Compiler.Verified`:
   - **(a) Top morphism (`π_top`):** maps every behavior to `Partial.ub`,
     allowing an unconditionally UB-free source program to compile to a target
     program that faults immediately (`.failed`).
   - **(b) Chaotic defined morphisms (`π_chaosPure`, `π_chaosVal`,
     `π_maskStuck`):** preserve definedness while erasing `.val` to
     `fun _ => True` (or remapping `.stuck`), allowing a compiler pass to
     corrupt return values, discard postconditions, diverge, or reach `.stuck`.
   - **(c) Step-zero and bounded-fuel query distortion (`π_stepZero`,
     `π_boundedFuel`):** pull back target queries `⟨init, steps⟩` to `steps = 0`
     or `min steps K`, mapping every source execution at `steps = 0` to
     `.running` and masking both non-termination (`loop: jmp loop`) and
     Undefined Behavior occurring after step `K`.
   - **(d) Observation and return-value erasure (`π_eraseTrace_cov`,
     `π_collapseVal_cov`, `π_spoof_contra`):** erase trace observations `tr` or
     collapse distinct return values via either covariant existential projection
     or non-injective contravariant pullback.
2. **Admissible Simulation Couplings and Target-Anchored Pipelines
   (Section 4):**
   Formulates `ExecSimCoupling` and its four minimal structural admissibility
   conditions (`AdmissibleExecCoupling`: `step_nonempty`, `step_coverage`,
   `trace_injective`, and `val_injective`), proves that they rule out all four
   degeneracy classes **(a)–(d)**, and characterizes the exact difference
   between unanchored `verify_through_passes` (which remains vulnerable to
   degenerate morphisms) and `spec_tgt`-anchored pipelines.
3. **Closure and Compositionality (Section 5):**
   Proves that `AdmissibleExecCoupling` is closed under identity
   (`ExecSimCoupling.id`) and relational-functional composition
   (`ExecSimCoupling.comp`), and composes with `Compiles.comp`,
   `Abstracts.comp`, and `verify_through_passes`.
4. **Concrete Positive Instantiations (Section 6):**
   Instantiates `AdmissibleExecCoupling` for a $1 \to 2$ multi-step lowering
   (`MirMultiLang → X86MultiLang`) and an upward borrow/functional abstraction
   (`FuncLang → MirMultiLang`), composing them end-to-end via
   `verify_through_passes`.
-/

namespace Anneal.MorphismAdmissibility

/-!
## 1. Layer 1A & Layer 1B Baseline (`Trusted.Refinement`, `Trusted.StepResult`)
-/

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever `B` is a `Preorder`. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive representation of $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element ($\mathsf{UB}$) of `Partial B` (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Refinement preorder on `Partial B`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Canonical domain of query-indexed partial behaviors. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling `Prog`, `Query`, `Out`, and `sem`. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- The behavior domain of a `Language`. -/
abbrev Language.Behavior (L : Language) : Type :=
  Anneal.MorphismAdmissibility.Behavior L.Query L.Out

/-- Query-indexed specification on `L` with precondition `pre` and postcondition
    `post`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification on `L`. -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `L`. -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`. -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Verification (abstraction) pass from `L_src` to verifier language `L_v`. -/
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- A compiler lowering programs from `L_src` to `L_tgt` with behavior mapping
    `π`. -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`. -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification obligation for source program `s` and specification
    `spec` under compiler `C`. -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- Distinguishes normal return from panic/unwind completion. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Outcome of a single transition step in a small-step interaction tree. -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Outcome recorded at the end of a finite execution prefix. -/
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

/-- A prefix outcome is safe when it is neither `.failed` nor `.stuck`. -/
def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed => False
  | .stuck => False

/-- Input query to a finite-prefix small-step execution. -/
structure ExecQuery (State : Type) where
  init : State
  steps : Nat

/-- Observable output of a finite-prefix small-step execution. -/
structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

/-- Small-step operational semantics. -/
structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of a finite execution prefix. -/
inductive ReachesPrefix
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      step p s (.choice branches) →
      branches s' →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix step p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      step p s (.terminated term) →
      ReachesPrefix step p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      step p s .failed →
      ReachesPrefix step p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, step p s r) →
      ReachesPrefix step p (n + 1) s [] .stuck

/-- Induced query-indexed partial behavior of program `p` in machine `M`. -/
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M.step p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M.step p q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a `Language`. -/
abbrev SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

theorem monotone_id {B : Type u} [Preorder B] : Monotone (fun b : B => b) :=
  fun _ _ h => h

theorem monotone_comp {A : Type u} {B : Type v} {C : Type w}
    [Preorder A] [Preorder B] [Preorder C]
    {g : B → C} {f : A → B}
    (hg : Monotone g) (hf : Monotone f) :
    Monotone (fun a => g (f a)) :=
  fun _ _ h => hg (hf h)

def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v}
    [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp hdef₂
  cases hp hdef₂ with
  | intro hdef₁ hle =>
    exact ⟨hdef₁, hf hle⟩

theorem ub_top {B : Type u} [Preorder B] (p : Partial B) :
    p ≤ Partial.ub :=
  fun h => False.elim h

theorem pass_trans
    {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    [Preorder B₁] [Preorder B₂] [Preorder B₃]
    {π₂ : B₁ → B₂} {π₁ : B₂ → B₃}
    (h_mono₁ : Monotone π₁)
    {b₁ : B₁} {b₂ : B₂} {b₃ : B₃}
    (h₂₃ : b₃ ≤ π₁ b₂)
    (h₁₂ : b₂ ≤ π₂ b₁) :
    b₃ ≤ π₁ (π₂ b₁) :=
  Preorder.le_trans h₂₃ (h_mono₁ h₁₂)

theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono₂ : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  pass_trans h_mono₂ h₂₃ h₁₂

theorem Abstracts.comp
    {L₂ L₁ L_src : Language}
    {π₂ : L₂.Behavior → L₁.Behavior} {π₁ : L₁.Behavior → L_src.Behavior}
    {v₂ : L₂.Prog} {v₁ : L₁.Prog} {s : L_src.Prog}
    (h₁ : Abstracts L₁ L_src π₁ v₁ s)
    (h₂ : Abstracts L₂ L₁ π₂ v₂ v₁)
    (h_mono₁ : Monotone π₁) :
    Abstracts L₂ L_src (fun b => π₁ (π₂ b)) v₂ s :=
  pass_trans h_mono₁ h₁ h₂

theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

theorem verify_through_passes
    {L_v L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {π_v : L_v.Behavior → L_src.Behavior} {spec : L_v.Behavior}
    {v : L_v.Prog} {s : L_src.Prog}
    (h_proof : L_v.sem v ≤ spec)
    (h_abs : Abstracts L_v L_src π_v v s)
    (h_mono_v : Monotone π_v)
    (h_comp : C.SoundOn s) :
    C.Verified s (π_v spec) :=
  Compiler.SoundOn.verify h_comp (Preorder.le_trans h_abs (h_mono_v h_proof))

/-!
## 2. Concrete Small-Step Counterexample Machine (`ToyMachine`)
-/

/-- Programs for our small-step counterexample testbed:
    - `good`: emits observation `10` at step 1 and terminates normally with `42`
      at step 2.
    - `lateUb`: emits observation `10` at step 1 and triggers `.failed` (UB) at
      step 2.
    - `immediateUb`: triggers `.failed` (UB) immediately at step 1.
    - `stuck`: has no outgoing transitions (`noStep`), reaching `.stuck` at
      step 1.
    - `wrongVal`: emits observation `10` at step 1 and terminates normally with
      `999` (instead of `42`) at step 2.
    - `silentReturn`: takes a silent `.choice` step (emitting `[]` instead of
      `[10]`) at step 1 and terminates normally with `42` at step 2.
    - `infiniteLoop`: takes a silent `.choice` self-loop at every step,
      remaining in `.running` with `trace = []` for all step budgets.
    - `loopAfter1`: emits observation `10` at step 1 and then enters a silent
      `.choice` self-loop from step 2 onward. -/
inductive ToyProg where
  | good
  | lateUb
  | immediateUb
  | stuck
  | wrongVal
  | silentReturn
  | infiniteLoop
  | loopAfter1

/-- Small-step transition relation for `ToyProg` over state `Nat` (`0` = entry,
    `1` = after first step), observation `Nat`, and return value `Nat`. -/
def toyStep (p : ToyProg) (s : Nat) (r : StepResult Nat Nat Nat) : Prop :=
  match p, s with
  | .good, 0 => r = .step 10 1
  | .good, _ + 1 => r = .terminated (.normal 42)
  | .lateUb, 0 => r = .step 10 1
  | .lateUb, _ + 1 => r = .failed
  | .immediateUb, _ => r = .failed
  | .stuck, _ => False
  | .wrongVal, 0 => r = .step 10 1
  | .wrongVal, _ + 1 => r = .terminated (.normal 999)
  | .silentReturn, 0 => r = .choice (fun s' => s' = 1)
  | .silentReturn, _ + 1 => r = .terminated (.normal 42)
  | .infiniteLoop, s => r = .choice (fun s' => s' = s)
  | .loopAfter1, 0 => r = .step 10 1
  | .loopAfter1, s + 1 => r = .choice (fun s' => s' = s + 1)

/-- `ToyMachine` starts at initial state `s = 0`. -/
def ToyMachine : SmallStepMachine ToyProg Nat Nat Nat where
  initState _ s := s = 0
  step := toyStep

/-- Operational language induced by `ToyMachine`. -/
abbrev ToyLang : Language :=
  ToyMachine.toLanguage

/-- Specification for `ToyProg.good`: unconditionally defined (`WellFormed`),
    every completed trace is `[10]`, and every normal return value is `42`. -/
def specGood : ToyLang.Behavior :=
  ToyLang.Spec (fun _ out =>
    (∀ v, out.outcome = .terminated (.normal v) → out.trace = [10] ∧ v = 42) ∧
    out.outcome ≠ .terminated .unwind)

theorem good_reaches_safe_and_spec (n : Nat) :
    ∀ tr out,
      ReachesPrefix ToyMachine.step .good n 0 tr out →
      out.isSafe ∧
        ((∀ v, out = .terminated (.normal v) → tr = [10] ∧ v = 42) ∧
          out ≠ .terminated .unwind) := by
  cases n with
  | zero =>
    intro tr out hr
    cases hr with
    | zero =>
      refine ⟨True.intro, ?_, ?_⟩
      · intro _ h; cases h
      · intro h; cases h
  | succ m =>
    intro tr out hr
    cases hr with
    | step _ _ s' obs tr' _ h1 hr2 =>
      dsimp [ToyMachine, toyStep] at h1
      injection h1 with hobs hs'
      subst hobs hs'
      cases m with
      | zero =>
        cases hr2 with
        | zero =>
          refine ⟨True.intro, ?_, ?_⟩
          · intro _ h; cases h
          · intro h; cases h
      | succ k =>
        cases hr2 with
        | step _ _ _ _ _ _ h2 _ =>
          dsimp [ToyMachine, toyStep] at h2; cases h2
        | choice _ _ _ _ _ _ h2 _ _ =>
          dsimp [ToyMachine, toyStep] at h2; cases h2
        | emptyChoice _ _ _ h2 _ =>
          dsimp [ToyMachine, toyStep] at h2; cases h2
        | terminated _ _ term h2 =>
          dsimp [ToyMachine, toyStep] at h2
          injection h2 with hterm
          subst hterm
          refine ⟨True.intro, ?_, ?_⟩
          · intro v hv
            injection hv with hv'
            injection hv' with hv''
            subst hv''
            exact ⟨rfl, rfl⟩
          · intro h; cases h
        | failed _ _ h2 =>
          dsimp [ToyMachine, toyStep] at h2; cases h2
        | noStep _ _ hno =>
          exact False.elim (hno ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ h1 _ _ =>
      dsimp [ToyMachine, toyStep] at h1; cases h1
    | emptyChoice _ _ _ h1 _ =>
      dsimp [ToyMachine, toyStep] at h1; cases h1
    | terminated _ _ _ h1 =>
      dsimp [ToyMachine, toyStep] at h1; cases h1
    | failed _ _ h1 =>
      dsimp [ToyMachine, toyStep] at h1; cases h1
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, rfl⟩)

/-- `ToyProg.good` satisfies `specGood`. -/
theorem progGood_satisfies_specGood :
    ToyLang.sem .good ≤ specGood := by
  intro q _
  cases q with
  | mk init steps =>
    refine ⟨?_, ?_⟩
    · intro hinit tr out hr
      dsimp [ToyMachine] at hinit
      subst hinit
      exact (good_reaches_safe_and_spec steps tr out hr).1
    · intro out hout
      have hinit : init = 0 := hout.1
      have hr := hout.2
      subst hinit
      exact (good_reaches_safe_and_spec steps out.trace out.outcome hr).2

/-- `ToyProg.good` is unconditionally well-formed (`ToyLang.WellFormed`). -/
theorem progGood_wellFormed :
    ToyLang.sem .good ≤ ToyLang.WellFormed := by
  intro q _
  cases q with
  | mk init steps =>
    refine ⟨?_, fun _ _ => True.intro⟩
    intro hinit tr out hr
    dsimp [ToyMachine] at hinit
    subst hinit
    exact (good_reaches_safe_and_spec steps tr out hr).1

/-- `ToyProg.immediateUb` violates `ToyLang.WellFormed` at step 1. -/
theorem progImmediateUb_not_wellFormed :
    ¬ (ToyLang.sem .immediateUb ≤ ToyLang.WellFormed) := by
  intro hwf
  have hdef := (hwf ⟨0, 1⟩ True.intro).1
  have hr : ReachesPrefix ToyMachine.step .immediateUb 1 0 [] .failed :=
    ReachesPrefix.failed 0 0 rfl
  exact hdef rfl [] .failed hr

/-- `ToyProg.stuck` violates `ToyLang.WellFormed` at step 1 because `noStep`
    transitions to `.stuck` (`isSafe = False`). -/
theorem progStuck_not_wellFormed :
    ¬ (ToyLang.sem .stuck ≤ ToyLang.WellFormed) := by
  intro hwf
  have hdef := (hwf ⟨0, 1⟩ True.intro).1
  have hr : ReachesPrefix ToyMachine.step .stuck 1 0 [] .stuck :=
    ReachesPrefix.noStep 0 0 (fun ⟨_, h⟩ => h)
  exact hdef rfl [] .stuck hr

/-- `ToyProg.lateUb` violates `ToyLang.WellFormed` at step 2. -/
theorem progLateUb_not_wellFormed :
    ¬ (ToyLang.sem .lateUb ≤ ToyLang.WellFormed) := by
  intro hwf
  have hdef := (hwf ⟨0, 2⟩ True.intro).1
  have hr1 : ReachesPrefix ToyMachine.step .lateUb 1 1 [] .failed :=
    ReachesPrefix.failed 0 1 rfl
  have hr2 : ReachesPrefix ToyMachine.step .lateUb 2 0 [10] .failed :=
    ReachesPrefix.step 1 0 1 10 [] .failed rfl hr1
  exact hdef rfl [10] .failed hr2

/-- Every prefix of `ToyProg.infiniteLoop` from state `s` produces `trace = []`
    and `outcome = .running`. -/
theorem infiniteLoop_reaches_running (n : Nat) :
    ∀ s tr out,
      ReachesPrefix ToyMachine.step .infiniteLoop n s tr out →
      tr = [] ∧ out = .running := by
  induction n with
  | zero =>
    intro s tr out hr
    cases hr with
    | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro s tr out hr
    cases hr with
    | step _ _ _ _ _ _ h1 _ =>
      dsimp [ToyMachine, toyStep] at h1; cases h1
    | choice _ _ s' branches _ _ h1 hbr hr2 =>
      dsimp [ToyMachine, toyStep] at h1
      injection h1 with hbr_eq
      subst hbr_eq
      subst hbr
      exact ih s' tr out hr2
    | emptyChoice _ _ branches h1 hemp =>
      dsimp [ToyMachine, toyStep] at h1
      injection h1 with hbr_eq
      subst hbr_eq
      exact False.elim (hemp ⟨s, rfl⟩)
    | terminated _ _ _ h1 =>
      dsimp [ToyMachine, toyStep] at h1; cases h1
    | failed _ _ h1 =>
      dsimp [ToyMachine, toyStep] at h1; cases h1
    | noStep _ _ hno =>
      exact False.elim (hno ⟨_, rfl⟩)

/-- `ToyProg.infiniteLoop` is unconditionally well-formed (`ToyLang.WellFormed`). -/
theorem progInfiniteLoop_wellFormed :
    ToyLang.sem .infiniteLoop ≤ ToyLang.WellFormed := by
  intro q _
  refine ⟨?_, fun _ _ => True.intro⟩
  intro _ tr out hr
  have hout := (infiniteLoop_reaches_running q.steps q.init tr out hr).2
  rw [hout]
  exact True.intro

/-- `ToyProg.wrongVal` is unconditionally well-formed, but violates `specGood`
    at `steps = 2` because it returns `999 ≠ 42`. -/
theorem progWrongVal_wellFormed :
    ToyLang.sem .wrongVal ≤ ToyLang.WellFormed := by
  intro q _
  cases q with
  | mk init steps =>
    refine ⟨?_, fun _ _ => True.intro⟩
    intro hinit tr out hr
    dsimp [ToyMachine] at hinit
    subst hinit
    cases steps with
    | zero =>
      cases hr with
      | zero => exact True.intro
    | succ m =>
      cases hr with
      | step _ _ s' obs tr' _ h1 hr2 =>
        dsimp [ToyMachine, toyStep] at h1
        injection h1 with _ hs'
        subst hs'
        cases m with
        | zero =>
          cases hr2 with
          | zero => exact True.intro
        | succ k =>
          cases hr2 with
          | step _ _ _ _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
          | choice _ _ _ _ _ _ h2 _ _ => dsimp [ToyMachine, toyStep] at h2; cases h2
          | emptyChoice _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
          | terminated _ _ _ _ => exact True.intro
          | failed _ _ h2 => dsimp [ToyMachine, toyStep] at h2; cases h2
          | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
      | choice _ _ _ _ _ _ h1 _ _ => dsimp [ToyMachine, toyStep] at h1; cases h1
      | emptyChoice _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
      | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
      | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)

theorem progWrongVal_not_specGood :
    ¬ (ToyLang.sem .wrongVal ≤ specGood) := by
  intro hspec
  cases hspec ⟨0, 2⟩ True.intro with
  | intro hdef hval =>
    have hr1 : ReachesPrefix ToyMachine.step .wrongVal 1 1 [] (.terminated (.normal 999)) :=
      ReachesPrefix.terminated 0 1 (.normal 999) rfl
    have hr2 : ReachesPrefix ToyMachine.step .wrongVal 2 0 [10] (.terminated (.normal 999)) :=
      ReachesPrefix.step 1 0 1 10 [] (.terminated (.normal 999)) rfl hr1
    have hout := hval ⟨[10], .terminated (.normal 999)⟩ ⟨rfl, hr2⟩
    have h42 := (hout.1 999 rfl).2
    cases h42

/-- `ToyProg.silentReturn` is unconditionally well-formed, but violates
    `specGood` at `steps = 2` because its trace is `[] ≠ [10]`. -/
theorem progSilentReturn_not_specGood :
    ¬ (ToyLang.sem .silentReturn ≤ specGood) := by
  intro hspec
  cases hspec ⟨0, 2⟩ True.intro with
  | intro hdef hval =>
    have hr1 : ReachesPrefix ToyMachine.step .silentReturn 1 1 [] (.terminated (.normal 42)) :=
      ReachesPrefix.terminated 0 1 (.normal 42) rfl
    have hr2 : ReachesPrefix ToyMachine.step .silentReturn 2 0 [] (.terminated (.normal 42)) :=
      ReachesPrefix.choice 1 0 1 (fun s' => s' = 1) [] (.terminated (.normal 42)) rfl rfl hr1
    have hout := hval ⟨[], .terminated (.normal 42)⟩ ⟨rfl, hr2⟩
    have htr := (hout.1 42 rfl).1
    cases htr

/-!
## 3. Taxonomy of Degenerate Monotone Morphisms

### 3.1 Class (a): Top Morphism (`π_top`)
-/

/-- The top behavior morphism mapping every source behavior and target query to
    `Partial.ub` (`defined := False`). -/
def π_top (L₁ L₂ : Language) : L₁.Behavior → L₂.Behavior :=
  fun _ _ => Partial.ub

/-- `π_top` is monotone on any pair of languages `L₁` and `L₂`. -/
theorem monotone_π_top (L₁ L₂ : Language) :
    Monotone (π_top L₁ L₂) :=
  fun _ _ _ _ h => False.elim h

/-- Under `π_top`, every source program `s` compiles to every target program
    `t`—even when `s` is unconditionally UB-free and `t` faults immediately. -/
theorem compiles_π_top_trivial (L₁ L₂ : Language) (s : L₁.Prog) (t : L₂.Prog) :
    Compiles L₁ L₂ (π_top L₁ L₂) s t :=
  fun q => ub_top (L₂.sem t q)

/-- Under `π_top`, every verifier model `v` abstracts every source program `s`. -/
theorem abstracts_π_top_trivial (L_v L_src : Language) (v : L_v.Prog)
    (s : L_src.Prog) :
    Abstracts L_v L_src (π_top L_v L_src) v s :=
  fun q => ub_top (L_src.sem s q)

/-- Counterexample (a): A compiler with `π := π_top` that compiles `.good` to
    `.immediateUb` satisfies `Compiler.SoundOn .good` and
    `Compiler.Verified .good specGood`, masking unconditional target UB. -/
theorem counterexample_class_a_masks_target_ub :
    let C : Compiler ToyLang ToyLang := {
      compile := fun _ => .immediateUb
      π := π_top ToyLang ToyLang
    }
    ToyLang.sem .good ≤ ToyLang.WellFormed ∧
    ¬ (ToyLang.sem (C.compile .good) ≤ ToyLang.WellFormed) ∧
    C.SoundOn .good ∧
    C.Verified .good specGood := by
  intro C
  have hSound : C.SoundOn .good :=
    ⟨monotone_π_top ToyLang ToyLang,
     compiles_π_top_trivial ToyLang ToyLang .good .immediateUb⟩
  exact ⟨progGood_wellFormed,
         progImmediateUb_not_wellFormed,
         hSound,
         Compiler.SoundOn.verify hSound progGood_satisfies_specGood⟩

/-!
### 3.2 Class (b): Chaotic Defined Morphisms (`π_chaosPure`, `π_chaosVal`, `π_maskStuck`)
-/

/-- Variant (b1): Constant chaotic defined morphism mapping every behavior to
    `L₂.WellFormed` (`fun _ => Partial.pure (fun _ => True)`). -/
def π_chaosPure (L₁ L₂ : Language) : L₁.Behavior → L₂.Behavior :=
  fun _ _ => Partial.pure (fun _ => True)

theorem monotone_π_chaosPure (L₁ L₂ : Language) :
    Monotone (π_chaosPure L₁ L₂) :=
  fun _ _ _ _ _ => ⟨True.intro, fun _ h => h⟩

/-- Variant (b2): Definedness-preserving chaotic morphism that preserves
    `(b (mapQ q)).defined` while erasing `.val` to `fun _ => True`. -/
def π_chaosVal {L₁ L₂ : Language} (mapQ : L₂.Query → L₁.Query)
    (b : L₁.Behavior) : L₂.Behavior :=
  fun q => Partial.map (fun _ _ => True) (b (mapQ q))

theorem monotone_π_chaosVal {L₁ L₂ : Language} (mapQ : L₂.Query → L₁.Query) :
    Monotone (π_chaosVal (L₁ := L₁) (L₂ := L₂) mapQ) := by
  intro b₁ b₂ hle q
  exact Partial.monotone_map
    (f := fun (_ : L₁.Out → Prop) (_ : L₂.Out) => True)
    (fun _ _ _ _ _ => True.intro)
    (hle (mapQ q))

/-- Counterexample (b): `π_chaosVal id` preserves `.defined` (so `.immediateUb`
    is still rejected when compiling `.good`), yet erases all functional
    postconditions and trace obligations—allowing `.good` (returns `42` with
    trace `[10]`) to compile to `.wrongVal` (returns `999`) or `.infiniteLoop`
    (never terminates) while satisfying `Compiler.Verified .good specGood`. -/
theorem counterexample_class_b_erases_postconditions :
    let C_wrong : Compiler ToyLang ToyLang := {
      compile := fun _ => .wrongVal
      π := π_chaosVal id
    }
    ¬ Compiles ToyLang ToyLang (π_chaosVal id) .good .immediateUb ∧
    Compiles ToyLang ToyLang (π_chaosVal id) .good .wrongVal ∧
    Compiles ToyLang ToyLang (π_chaosVal id) .good .infiniteLoop ∧
    C_wrong.SoundOn .good ∧
    C_wrong.Verified .good specGood ∧
    ¬ (ToyLang.sem (C_wrong.compile .good) ≤ specGood) := by
  intro C_wrong
  have hNotUb : ¬ Compiles ToyLang ToyLang (π_chaosVal id) .good .immediateUb := by
    intro hcomp
    have hdefGood : (ToyLang.sem .good ⟨0, 1⟩).defined :=
      (progGood_wellFormed ⟨0, 1⟩ True.intro).1
    cases hcomp ⟨0, 1⟩ hdefGood with
    | intro hdefUb _ =>
      exact hdefUb rfl [] .failed (ReachesPrefix.failed 0 0 rfl)
  have hCompWrong : Compiles ToyLang ToyLang (π_chaosVal id) .good .wrongVal := by
    intro q _
    exact ⟨(progWrongVal_wellFormed q True.intro).1, fun _ _ => True.intro⟩
  have hCompLoop : Compiles ToyLang ToyLang (π_chaosVal id) .good .infiniteLoop := by
    intro q _
    exact ⟨(progInfiniteLoop_wellFormed q True.intro).1, fun _ _ => True.intro⟩
  have hSound : C_wrong.SoundOn .good :=
    ⟨monotone_π_chaosVal id, hCompWrong⟩
  exact ⟨hNotUb, hCompWrong, hCompLoop, hSound,
         Compiler.SoundOn.verify hSound progGood_satisfies_specGood,
         progWrongVal_not_specGood⟩

/-- Variant (b3): In a language whose raw transition semantics places `.stuck`
    inside defined outcomes (`defined := True`, `val := ReachesPrefix`),
    `π_chaosVal id` even allows `.good` to compile to `.stuck`! -/
def RawToyLang : Language where
  Prog := ToyProg
  Query := ExecQuery Nat
  Out := ExecOut Nat Nat
  sem p q := Partial.pure (fun out =>
    ToyMachine.initState p q.init ∧
    ReachesPrefix ToyMachine.step p q.steps q.init out.trace out.outcome)

theorem counterexample_class_b_allows_stuck_when_defined :
    Compiles ToyLang RawToyLang (π_chaosVal id) .good .stuck := by
  intro _ _
  exact ⟨True.intro, fun _ _ => True.intro⟩

/-!
### 3.3 Class (c): Step-Zero and Bounded-Fuel Query Distortion (`π_stepZero`, `π_boundedFuel`)
-/

/-- Standard contravariant query/outcome pullback morphism used by compiler
    passes (`fun q => Partial.map (fun P out => P (mapOut out)) (b (mapQ q))`). -/
def pullbackMorphism {L₁ L₂ : Language}
    (mapQ : L₂.Query → L₁.Query) (mapOut : L₂.Out → L₁.Out)
    (b : L₁.Behavior) : L₂.Behavior :=
  fun q => Partial.map (fun P out => P (mapOut out)) (b (mapQ q))

/-- Every `pullbackMorphism mapQ mapOut` is monotone. -/
theorem monotone_pullbackMorphism {L₁ L₂ : Language}
    (mapQ : L₂.Query → L₁.Query) (mapOut : L₂.Out → L₁.Out) :
    Monotone (pullbackMorphism (L₁ := L₁) (L₂ := L₂) mapQ mapOut) := by
  intro b₁ b₂ hle q
  refine Partial.monotone_map ?_ (hle (mapQ q))
  intro P₁ P₂ hP out hout
  exact hP (mapOut out) hout

/-- At `steps = 0`, `BehaviorOf M p ⟨init, 0⟩` is unconditionally defined for
    *every* program `p` (even one that faults at step 1), and its only reachable
    outcome is `⟨[], .running⟩`. -/
theorem behaviorOf_steps_zero_defined
    (M : SmallStepMachine Prog State Obs Val) (p : Prog) (init : State) :
    (BehaviorOf M p ⟨init, 0⟩).defined := by
  intro _ tr out hr
  cases hr with
  | zero => exact True.intro

/-- Step-zero query projection mapping every target query `⟨init, steps⟩` to
    `⟨mapInit init, 0⟩`. -/
def mapQueryZero {State₁ State₂ : Type} (mapInit : State₂ → State₁)
    (q : ExecQuery State₂) : ExecQuery State₁ where
  init := mapInit q.init
  steps := 0

/-- Step-zero pullback morphism (`steps ↦ 0`, `out ↦ out`). -/
def π_stepZero : ToyLang.Behavior → ToyLang.Behavior :=
  pullbackMorphism (L₁ := ToyLang) (L₂ := ToyLang) (mapQueryZero id) id

theorem monotone_π_stepZero : Monotone π_stepZero :=
  monotone_pullbackMorphism (L₁ := ToyLang) (L₂ := ToyLang) (mapQueryZero id) id

/-- Counterexample (c1): Under `π_stepZero`, `.good` (which terminates at step 2
    with `42`) and even `.immediateUb` (which faults at step 1) compile to
    `.infiniteLoop` (`loop: jmp loop`), and `π_stepZero (ToyLang.sem .immediateUb)`
    is defined at every step budget `q.steps`! -/
theorem counterexample_class_c_stepZero_diverges_and_masks_ub :
    (ToyLang.sem .immediateUb ≤ ToyLang.WellFormed → False) ∧
    (π_stepZero (ToyLang.sem .immediateUb) ≤ ToyLang.WellFormed) ∧
    Compiles ToyLang ToyLang π_stepZero .good .infiniteLoop ∧
    Compiles ToyLang ToyLang π_stepZero .immediateUb .infiniteLoop := by
  have hWfMasked : π_stepZero (ToyLang.sem .immediateUb) ≤ ToyLang.WellFormed := by
    intro q _
    exact ⟨behaviorOf_steps_zero_defined ToyMachine .immediateUb q.init,
           fun _ _ => True.intro⟩
  have hCompGood : Compiles ToyLang ToyLang π_stepZero .good .infiniteLoop := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨(progInfiniteLoop_wellFormed ⟨init, steps⟩ True.intro).1, ?_⟩
      intro out hout
      have hinit : init = 0 := hout.1
      have hr := infiniteLoop_reaches_running steps init out.trace out.outcome hout.2
      cases out with
      | mk trace outcome =>
        dsimp at hr
        subst hinit
        rw [hr.1, hr.2]
        exact ⟨rfl, ReachesPrefix.zero 0⟩
  have hCompUb : Compiles ToyLang ToyLang π_stepZero .immediateUb .infiniteLoop := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨(progInfiniteLoop_wellFormed ⟨init, steps⟩ True.intro).1, ?_⟩
      intro out hout
      have hinit : init = 0 := hout.1
      have hr := infiniteLoop_reaches_running steps init out.trace out.outcome hout.2
      cases out with
      | mk trace outcome =>
        dsimp at hr
        subst hinit
        rw [hr.1, hr.2]
        exact ⟨rfl, ReachesPrefix.zero 0⟩
  exact ⟨progImmediateUb_not_wellFormed, hWfMasked, hCompGood, hCompUb⟩

/-- Structural step-budget cap ($\min(\mathsf{steps}, K)$) defined by recursion
    so `capSteps 0 K = 0` and `capSteps (m + 1) 1 = 1` reduce cleanly. -/
def capSteps : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => capSteps n k + 1

theorem capSteps_one_succ (m : Nat) : capSteps (m + 1) 1 = 1 := by
  cases m <;> rfl

/-- Bounded-fuel query projection capping target step budgets at `K`
    (`steps ↦ capSteps steps K`). -/
def mapQueryBounded (K : Nat) {State₁ State₂ : Type} (mapInit : State₂ → State₁)
    (q : ExecQuery State₂) : ExecQuery State₁ where
  init := mapInit q.init
  steps := capSteps q.steps K

/-- Bounded-fuel pullback morphism (`steps ↦ capSteps steps K`, `out ↦ out`). -/
def π_boundedFuel (K : Nat) : ToyLang.Behavior → ToyLang.Behavior :=
  pullbackMorphism (L₁ := ToyLang) (L₂ := ToyLang) (mapQueryBounded K id) id

theorem monotone_π_boundedFuel (K : Nat) : Monotone (π_boundedFuel K) :=
  monotone_pullbackMorphism (L₁ := ToyLang) (L₂ := ToyLang) (mapQueryBounded K id) id

theorem capSteps_one_cases (n : Nat) : capSteps n 1 = 0 ∨ capSteps n 1 = 1 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ m => exact Or.inr (capSteps_one_succ m)

/-- Counterexample (c2): Under `π_boundedFuel 1`, `ToyProg.lateUb` (which triggers
    UB at step 2) is mapped to a behavior that is `WellFormed` at *all* step
    budgets `q.steps`, and `ToyProg.good` (which returns `42` at step 2) compiles
    to `ToyProg.loopAfter1` (which loops forever after step 1)! -/
theorem counterexample_class_c_boundedFuel_masks_late_ub_and_divergence :
    ¬ (ToyLang.sem .lateUb ≤ ToyLang.WellFormed) ∧
    (π_boundedFuel 1 (ToyLang.sem .lateUb) ≤ ToyLang.WellFormed) ∧
    Compiles ToyLang ToyLang (π_boundedFuel 1) .good .loopAfter1 := by
  have hLateMasked : π_boundedFuel 1 (ToyLang.sem .lateUb) ≤ ToyLang.WellFormed := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨?_, fun _ _ => True.intro⟩
      intro hinit tr out hr
      dsimp [ToyMachine, mapQueryBounded] at hinit hr
      subst hinit
      cases capSteps_one_cases steps with
      | inl h0 =>
        rw [h0] at hr
        cases hr with
        | zero => exact True.intro
      | inr h1 =>
        rw [h1] at hr
        cases hr with
        | step _ _ s' _ _ _ hstep hr2 =>
          dsimp [ToyMachine, toyStep] at hstep
          injection hstep with _ hs'
          subst hs'
          cases hr2 with
          | zero => exact True.intro
        | choice _ _ _ _ _ _ hstep _ _ => dsimp [ToyMachine, toyStep] at hstep; cases hstep
        | emptyChoice _ _ _ hstep _ => dsimp [ToyMachine, toyStep] at hstep; cases hstep
        | terminated _ _ _ hstep => dsimp [ToyMachine, toyStep] at hstep; cases hstep
        | failed _ _ hstep => dsimp [ToyMachine, toyStep] at hstep; cases hstep
        | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  have hLoopAfter1 : ∀ n tr out,
      ReachesPrefix ToyMachine.step .loopAfter1 (n + 1) 1 tr out →
      tr = [] ∧ out = .running := by
    intro n
    induction n with
    | zero =>
      intro tr out hr
      cases hr with
      | step _ _ _ _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
      | choice _ _ s' _ _ _ h1 hbr hr2 =>
        dsimp [ToyMachine, toyStep] at h1
        injection h1 with hbr_eq
        subst hbr_eq
        subst hbr
        cases hr2 with
        | zero => exact ⟨rfl, rfl⟩
      | emptyChoice _ _ _ h1 hemp =>
        dsimp [ToyMachine, toyStep] at h1
        injection h1 with hbr_eq
        subst hbr_eq
        exact False.elim (hemp ⟨1, rfl⟩)
      | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
      | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
    | succ k ih =>
      intro tr out hr
      cases hr with
      | step _ _ _ _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
      | choice _ _ s' _ _ _ h1 hbr hr2 =>
        dsimp [ToyMachine, toyStep] at h1
        injection h1 with hbr_eq
        subst hbr_eq
        subst hbr
        exact ih tr out hr2
      | emptyChoice _ _ _ h1 hemp =>
        dsimp [ToyMachine, toyStep] at h1
        injection h1 with hbr_eq
        subst hbr_eq
        exact False.elim (hemp ⟨1, rfl⟩)
      | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
      | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
      | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  have hCompLoop1 : Compiles ToyLang ToyLang (π_boundedFuel 1) .good .loopAfter1 := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨?_, ?_⟩
      · intro hinit tr out hr
        dsimp [ToyMachine] at hinit
        subst hinit
        cases steps with
        | zero =>
          cases hr with
          | zero => exact True.intro
        | succ m =>
          cases hr with
          | step _ _ s' _ tr' _ h1 hr2 =>
            dsimp [ToyMachine, toyStep] at h1
            injection h1 with _ hs'
            subst hs'
            cases m with
            | zero =>
              cases hr2 with
              | zero => exact True.intro
            | succ k =>
              have hrun := (hLoopAfter1 k tr' out hr2).2
              rw [hrun]
              exact True.intro
          | choice _ _ _ _ _ _ h1 _ _ => dsimp [ToyMachine, toyStep] at h1; cases h1
          | emptyChoice _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
          | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
      · intro out hout
        have hinit : init = 0 := hout.1
        have hr := hout.2
        subst hinit
        cases steps with
        | zero =>
          cases out with
          | mk trace outcome =>
            cases hr with
            | zero => exact ⟨rfl, ReachesPrefix.zero 0⟩
        | succ m =>
          have hmin : capSteps (m + 1) 1 = 1 := capSteps_one_succ m
          cases out with
          | mk trace outcome =>
            change 0 = 0 ∧ ReachesPrefix ToyMachine.step .good (capSteps (m + 1) 1) 0 trace outcome
            rw [hmin]
            dsimp at hr
            cases hr with
            | step _ _ s' _ tr' _ h1 hr2 =>
              dsimp [ToyMachine, toyStep] at h1
              injection h1 with hobs hs'
              subst hobs hs'
              cases m with
              | zero =>
                cases hr2 with
                | zero =>
                  exact ⟨rfl, ReachesPrefix.step 0 0 1 10 [] .running rfl (ReachesPrefix.zero 1)⟩
              | succ k =>
                have hpair := hLoopAfter1 k tr' outcome hr2
                rw [hpair.1, hpair.2]
                exact ⟨rfl, ReachesPrefix.step 0 0 1 10 [] .running rfl (ReachesPrefix.zero 1)⟩
            | choice _ _ _ _ _ _ h1 _ _ => dsimp [ToyMachine, toyStep] at h1; cases h1
            | emptyChoice _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
            | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
            | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
            | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  exact ⟨progLateUb_not_wellFormed, hLateMasked, hCompLoop1⟩

/-!
### 3.4 Class (d): Observation and Return-Value Erasure (`covariantMorphism`, `pullbackMorphism`)
-/

/-- Covariant existential outcome projection:
    `out₂` is permitted whenever *some* source outcome `out₁ ∈ P` has the same
    projected image `proj out₁ = proj out₂`. -/
def covariantMorphism {L : Language} {Proj : Type} (proj : L.Out → Proj)
    (b : L.Behavior) : L.Behavior :=
  fun q => Partial.map (fun P out₂ => ∃ out₁, P out₁ ∧ proj out₁ = proj out₂) (b q)

theorem monotone_covariantMorphism {L : Language} {Proj : Type}
    (proj : L.Out → Proj) :
    Monotone (covariantMorphism proj) := by
  intro b₁ b₂ hle q
  refine Partial.monotone_map ?_ (hle q)
  intro P₁ P₂ hP out₂ ⟨out₁, hout₁, heq⟩
  exact ⟨out₁, hP out₁ hout₁, heq⟩

/-- Projection that erases the observation trace `out.trace` (keeping only
    `out.outcome`). -/
def eraseTraceProj (out : ExecOut Nat Nat) : PrefixOutcome Nat :=
  out.outcome

/-- Projection that collapses all normal return values to `()` (keeping
    `out.trace`). -/
def collapseValProj (out : ExecOut Nat Nat) : List Nat × PrefixOutcome Unit :=
  (out.trace,
   match out.outcome with
   | .running => .running
   | .terminated (.normal _) => .terminated (.normal ())
   | .terminated .unwind => .terminated .unwind
   | .failed => .failed
   | .stuck => .stuck)

/-- Non-injective contravariant outcome map that spoofs trace `[10]` and return
    value `42` on every normal termination. -/
def spoofOutContra (out : ExecOut Nat Nat) : ExecOut Nat Nat :=
  match out.outcome with
  | .running => { trace := out.trace, outcome := .running }
  | .terminated (.normal _) => { trace := [10], outcome := .terminated (.normal 42) }
  | .terminated .unwind => { trace := out.trace, outcome := .terminated .unwind }
  | .failed => { trace := out.trace, outcome := .failed }
  | .stuck => { trace := out.trace, outcome := .stuck }

/-- Counterexample (d):
    1. Under `covariantMorphism eraseTraceProj`, `.good` (emits `[10]`) compiles
       to `.silentReturn` (deletes volatile I/O, emitting `[]`).
    2. Under `covariantMorphism collapseValProj`, `.good` (returns `42`)
       compiles to `.wrongVal` (returns `999`).
    3. Even under a purely contravariant `pullbackMorphism id spoofOutContra`
       (with exact query identity `mapQ = id`), non-injectivity of
       `spoofOutContra` allows `.good` to compile to `.wrongVal`! -/
theorem counterexample_class_d_erases_observations_and_values :
    Compiles ToyLang ToyLang (covariantMorphism eraseTraceProj) .good .silentReturn ∧
    Compiles ToyLang ToyLang (covariantMorphism collapseValProj) .good .wrongVal ∧
    Compiles ToyLang ToyLang (pullbackMorphism id spoofOutContra) .good .wrongVal := by
  have hSilentWf : ToyLang.sem .silentReturn ≤ ToyLang.WellFormed := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨?_, fun _ _ => True.intro⟩
      intro hinit tr out hr
      dsimp [ToyMachine] at hinit
      subst hinit
      cases steps with
      | zero =>
        cases hr with
        | zero => exact True.intro
      | succ m =>
        cases hr with
        | step _ _ _ _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
        | choice _ _ s' _ _ _ h1 hbr hr2 =>
          dsimp [ToyMachine, toyStep] at h1
          injection h1 with hbr_eq
          subst hbr_eq
          subst hbr
          cases m with
          | zero =>
            cases hr2 with
            | zero => exact True.intro
          | succ k =>
            cases hr2 with
            | step _ _ _ _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
            | choice _ _ _ _ _ _ h2 _ _ => dsimp [ToyMachine, toyStep] at h2; cases h2
            | emptyChoice _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
            | terminated _ _ _ _ => exact True.intro
            | failed _ _ h2 => dsimp [ToyMachine, toyStep] at h2; cases h2
            | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
        | emptyChoice _ _ _ h1 hemp =>
          dsimp [ToyMachine, toyStep] at h1
          injection h1 with hbr_eq
          subst hbr_eq
          exact False.elim (hemp ⟨1, rfl⟩)
        | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
        | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
        | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  have hEraseTrace : Compiles ToyLang ToyLang (covariantMorphism eraseTraceProj)
      .good .silentReturn := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨(hSilentWf ⟨init, steps⟩ True.intro).1, ?_⟩
      intro out hout
      have hinit : init = 0 := hout.1
      have hr := hout.2
      subst hinit
      cases steps with
      | zero =>
        cases out with
        | mk trace outcome =>
          cases hr with
          | zero =>
            exact ⟨⟨[], .running⟩, ⟨rfl, ReachesPrefix.zero 0⟩, rfl⟩
      | succ m =>
        cases out with
        | mk trace outcome =>
          dsimp at hr
          cases hr with
          | step _ _ _ _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
          | choice _ _ s' _ _ _ h1 hbr hr2 =>
            dsimp [ToyMachine, toyStep] at h1
            injection h1 with hbr_eq
            subst hbr_eq
            subst hbr
            cases m with
            | zero =>
              cases hr2 with
              | zero =>
                exact ⟨⟨[10], .running⟩,
                       ⟨rfl, ReachesPrefix.step 0 0 1 10 [] .running rfl (ReachesPrefix.zero 1)⟩,
                       rfl⟩
            | succ k =>
              cases hr2 with
              | step _ _ _ _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | choice _ _ _ _ _ _ h2 _ _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | emptyChoice _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | terminated _ _ term h2 =>
                dsimp [ToyMachine, toyStep] at h2
                injection h2 with hterm
                subst hterm
                exact ⟨⟨[10], .terminated (.normal 42)⟩,
                       ⟨rfl, ReachesPrefix.step (k + 1) 0 1 10 [] (.terminated (.normal 42)) rfl
                         (ReachesPrefix.terminated k 1 (.normal 42) rfl)⟩,
                       rfl⟩
              | failed _ _ h2 => dsimp [ToyMachine, toyStep] at h2; cases h2
              | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
          | emptyChoice _ _ _ h1 hemp =>
            dsimp [ToyMachine, toyStep] at h1
            injection h1 with hbr_eq
            subst hbr_eq
            exact False.elim (hemp ⟨1, rfl⟩)
          | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  have hCollapseVal : Compiles ToyLang ToyLang (covariantMorphism collapseValProj)
      .good .wrongVal := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨(progWrongVal_wellFormed ⟨init, steps⟩ True.intro).1, ?_⟩
      intro out hout
      have hinit : init = 0 := hout.1
      have hr := hout.2
      subst hinit
      cases steps with
      | zero =>
        cases out with
        | mk trace outcome =>
          cases hr with
          | zero =>
            exact ⟨⟨[], .running⟩, ⟨rfl, ReachesPrefix.zero 0⟩, rfl⟩
      | succ m =>
        cases out with
        | mk trace outcome =>
          dsimp at hr
          cases hr with
          | step _ _ s' _ tr' _ h1 hr2 =>
            dsimp [ToyMachine, toyStep] at h1
            injection h1 with hobs hs'
            subst hobs hs'
            cases m with
            | zero =>
              cases hr2 with
              | zero =>
                exact ⟨⟨[10], .running⟩,
                       ⟨rfl, ReachesPrefix.step 0 0 1 10 [] .running rfl (ReachesPrefix.zero 1)⟩,
                       rfl⟩
            | succ k =>
              cases hr2 with
              | step _ _ _ _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | choice _ _ _ _ _ _ h2 _ _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | emptyChoice _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | terminated _ _ term h2 =>
                dsimp [ToyMachine, toyStep] at h2
                injection h2 with hterm
                subst hterm
                exact ⟨⟨[10], .terminated (.normal 42)⟩,
                       ⟨rfl, ReachesPrefix.step (k + 1) 0 1 10 [] (.terminated (.normal 42)) rfl
                         (ReachesPrefix.terminated k 1 (.normal 42) rfl)⟩,
                       rfl⟩
              | failed _ _ h2 => dsimp [ToyMachine, toyStep] at h2; cases h2
              | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
          | choice _ _ _ _ _ _ h1 _ _ => dsimp [ToyMachine, toyStep] at h1; cases h1
          | emptyChoice _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
          | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  have hSpoofContra : Compiles ToyLang ToyLang (pullbackMorphism id spoofOutContra)
      .good .wrongVal := by
    intro q _
    cases q with
    | mk init steps =>
      refine ⟨(progWrongVal_wellFormed ⟨init, steps⟩ True.intro).1, ?_⟩
      intro out hout
      have hinit : init = 0 := hout.1
      have hr := hout.2
      subst hinit
      cases steps with
      | zero =>
        cases out with
        | mk trace outcome =>
          cases hr with
          | zero => exact ⟨rfl, ReachesPrefix.zero 0⟩
      | succ m =>
        cases out with
        | mk trace outcome =>
          dsimp at hr
          cases hr with
          | step _ _ s' _ tr' _ h1 hr2 =>
            dsimp [ToyMachine, toyStep] at h1
            injection h1 with hobs hs'
            subst hobs hs'
            cases m with
            | zero =>
              cases hr2 with
              | zero =>
                exact ⟨rfl, ReachesPrefix.step 0 0 1 10 [] .running rfl (ReachesPrefix.zero 1)⟩
            | succ k =>
              cases hr2 with
              | step _ _ _ _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | choice _ _ _ _ _ _ h2 _ _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | emptyChoice _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | terminated _ _ term h2 =>
                dsimp [ToyMachine, toyStep] at h2
                injection h2 with hterm
                subst hterm
                exact ⟨rfl, ReachesPrefix.step (k + 1) 0 1 10 [] (.terminated (.normal 42)) rfl
                  (ReachesPrefix.terminated k 1 (.normal 42) rfl)⟩
              | failed _ _ h2 => dsimp [ToyMachine, toyStep] at h2; cases h2
              | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
          | choice _ _ _ _ _ _ h1 _ _ => dsimp [ToyMachine, toyStep] at h1; cases h1
          | emptyChoice _ _ _ h1 _ => dsimp [ToyMachine, toyStep] at h1; cases h1
          | terminated _ _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | failed _ _ h1 => dsimp [ToyMachine, toyStep] at h1; cases h1
          | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  exact ⟨hEraseTrace, hCollapseVal, hSpoofContra⟩

/-!
## 4. Minimal Structural Admissibility Conditions & `ExecSimCoupling`

### 4.1 Canonical `ExecSimCoupling` and Its Induced Behavior Morphism
-/

/-- Functorial action on `TerminationKind`. -/
def TerminationKind.map {Val₁ Val₂ : Type} (f : Val₂ → Val₁) :
    TerminationKind Val₂ → TerminationKind Val₁
  | .normal v => .normal (f v)
  | .unwind => .unwind

/-- Functorial action on `PrefixOutcome` preserving outcome constructor tags
    (`.running`, `.terminated`, `.failed`, `.stuck`). -/
def PrefixOutcome.map {Val₁ Val₂ : Type} (f : Val₂ → Val₁) :
    PrefixOutcome Val₂ → PrefixOutcome Val₁
  | .running => .running
  | .terminated t => .terminated (t.map f)
  | .failed => .failed
  | .stuck => .stuck

/-- Mapping a `PrefixOutcome` via `PrefixOutcome.map` preserves and reflects
    `PrefixOutcome.isSafe`. -/
theorem PrefixOutcome.map_isSafe {Val₁ Val₂ : Type} (f : Val₂ → Val₁)
    (out : PrefixOutcome Val₂) :
    (out.map f).isSafe ↔ out.isSafe := by
  cases out <;> exact ⟨fun h => h, fun h => h⟩

/-- Simulation coupling between a source/abstract execution domain
    `(State₁, Obs₁, Val₁)` and a target/concrete execution domain
    `(State₂, Obs₂, Val₂)`:
    - `decompileInit`: lifts a target initial state to a source initial state.
    - `stepCoupling n₂ n₁`: relates a target step budget `n₂` to the source step
      budgets `n₁` whose safety and outcomes govern `n₂` (supporting both
      $1 \to 1$ lockstep `n₁ = n₂` and $1 \to k$ multi-step expansion where `n₂`
      couples to $\lfloor n₂ / k \rfloor$ and $\lceil n₂ / k \rceil$).
    - `decompileTrace`: lifts a target observation trace to a source observation
      trace.
    - `decompileVal`: lifts a target return value to a source return value. -/
structure ExecSimCoupling (State₁ Obs₁ Val₁ State₂ Obs₂ Val₂ : Type) where
  decompileInit : State₂ → State₁
  stepCoupling : Nat → Nat → Prop
  decompileTrace : List Obs₂ → List Obs₁
  decompileVal : Val₂ → Val₁

/-- Canonical outcome lifting induced by an `ExecSimCoupling`. -/
def ExecSimCoupling.decompileOut
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (out : ExecOut Obs₂ Val₂) : ExecOut Obs₁ Val₁ where
  trace := C.decompileTrace out.trace
  outcome := out.outcome.map C.decompileVal

/-- Canonical behavior morphism induced by an `ExecSimCoupling`:
    - `defined`: requires the source behavior `b` to be defined at every source
      step budget `n₁` coupled to `q₂.steps`. If any coupled source step budget
      exhibits UB (`defined = False`), the target is unconstrained at `q₂`.
    - `val`: permits a target output `out₂` iff `C.decompileOut out₂` is
      permitted by `b` at some coupled source step budget `n₁`. -/
def ExecSimCoupling.toMorphism
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (b : Behavior (ExecQuery State₁) (ExecOut Obs₁ Val₁)) :
    Behavior (ExecQuery State₂) (ExecOut Obs₂ Val₂) :=
  fun q₂ => {
    defined :=
      ∀ n₁, C.stepCoupling q₂.steps n₁ →
        (b ⟨C.decompileInit q₂.init, n₁⟩).defined
    val := fun h out₂ =>
      ∃ n₁, ∃ hn : C.stepCoupling q₂.steps n₁,
        (b ⟨C.decompileInit q₂.init, n₁⟩).val (h n₁ hn) (C.decompileOut out₂)
  }

/-- Every `ExecSimCoupling.toMorphism C` is constructively monotone (requiring
    zero axioms and no `Classical.choice`). -/
theorem ExecSimCoupling.monotone_toMorphism
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂) :
    Monotone C.toMorphism := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun n₁ hn => (hle ⟨C.decompileInit q₂.init, n₁⟩ (hdef₂ n₁ hn)).1, ?_⟩
  intro out₂ ⟨n₁, hn, hval₁⟩
  refine ⟨n₁, hn, ?_⟩
  cases hle ⟨C.decompileInit q₂.init, n₁⟩ (hdef₂ n₁ hn) with
  | intro hdef₁' hsub =>
    exact hsub (C.decompileOut out₂) hval₁

/-!
### 4.2 Minimal Structural Admissibility Conditions (`AdmissibleExecCoupling`)
-/

/-- Minimal structural admissibility conditions on an `ExecSimCoupling` ruling
    out all four degeneracy classes **(a)–(d)**:
    1. `step_nonempty`: every target step budget `n₂` is coupled to at least one
       source step budget `n₁` (so `.defined` on specs is never vacuous).
    2. `step_coverage`: for every source step budget `n₁`, there exists a target
       checkpoint step budget `n₂` at which `n₁` is the *unique* coupled source
       step budget (ruling out Class (c) step-zero and bounded-fuel caps while
       permitting $1 \to k$ instruction expansion via $n₂ = k \cdot n₁$).
    3. `trace_injective`: `decompileTrace` is injective (ruling out Class (d)
       trace erasure and spoofing).
    4. `val_injective`: `decompileVal` is injective (ruling out Class (d)
       return-value collapse and spoofing). -/
structure AdmissibleExecCoupling
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂) : Prop where
  step_nonempty :
    ∀ n₂ : Nat, ∃ n₁ : Nat, C.stepCoupling n₂ n₁
  step_coverage :
    ∀ n₁ : Nat, ∃ n₂ : Nat,
      C.stepCoupling n₂ n₁ ∧
      ∀ n₁' : Nat, C.stepCoupling n₂ n₁' → n₁' = n₁
  trace_injective :
    ∀ ⦃tr₁ tr₂ : List Obs₂⦄,
      C.decompileTrace tr₁ = C.decompileTrace tr₂ → tr₁ = tr₂
  val_injective :
    ∀ ⦃v₁ v₂ : Val₂⦄,
      C.decompileVal v₁ = C.decompileVal v₂ → v₁ = v₂

/-- Behavioral admissibility contract for an arbitrary behavior mapping
    `π : M₁.toLanguage.Behavior → M₂.toLanguage.Behavior`: `π` is pointwise
    refinement-equivalent to `C.toMorphism` for an `AdmissibleExecCoupling C`. -/
def AdmissibleCompilerMorphism
    (M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁)
    (M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂)
    (π : M₁.toLanguage.Behavior → M₂.toLanguage.Behavior) : Prop :=
  ∃ C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂,
    AdmissibleExecCoupling C ∧
    ∀ b : M₁.toLanguage.Behavior,
      π b ≤ C.toMorphism b ∧ C.toMorphism b ≤ π b

/-!
### 4.3 How `AdmissibleExecCoupling` Rules Out Classes (a)–(d)
-/

/-- Specification-transport bridge theorem (ruling out Classes (a) and (b)):
    Under `step_nonempty`, `C.toMorphism` maps any step-independent source
    specification `SpecOn (preInit ∘ init) (postOut ∘ init)` to the
    corresponding target specification `SpecOn (preInit ∘ C.decompileInit ∘ init)
    (postOut ∘ C.decompileInit ∘ init ∘ C.decompileOut)`. -/
theorem ExecSimCoupling.toMorphism_specOn_le
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (preInit : State₁ → Prop)
    (postOut : State₁ → ExecOut Obs₁ Val₁ → Prop) :
    C.toMorphism
      (M₁.toLanguage.SpecOn
        (fun q₁ => preInit q₁.init)
        (fun q₁ out₁ => postOut q₁.init out₁)) ≤
    M₂.toLanguage.SpecOn
      (fun q₂ => preInit (C.decompileInit q₂.init))
      (fun q₂ out₂ => postOut (C.decompileInit q₂.init) (C.decompileOut out₂)) := by
  intro q₂ hpre₂
  refine ⟨fun _ _ => hpre₂, ?_⟩
  intro out₂ ⟨_, _, hpost⟩
  exact hpost

/-- Corollary (ruling out Class (a)): `C.toMorphism` preserves `WellFormedOn` on
    initial-state preconditions (`C.toMorphism (WellFormedOn pre₁) ≤
    WellFormedOn pre₂`). -/
theorem ExecSimCoupling.toMorphism_wellFormedOn_le
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (preInit : State₁ → Prop) :
    C.toMorphism (M₁.toLanguage.WellFormedOn (fun q₁ => preInit q₁.init)) ≤
      M₂.toLanguage.WellFormedOn (fun q₂ => preInit (C.decompileInit q₂.init)) :=
  C.toMorphism_specOn_le preInit (fun _ _ => True)

/-- Corollary (ruling out Class (a)): `C.toMorphism` preserves unconditional
    `WellFormed` (`C.toMorphism M₁.toLanguage.WellFormed ≤
    M₂.toLanguage.WellFormed`). -/
theorem ExecSimCoupling.toMorphism_wellFormed_le
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂) :
    C.toMorphism M₁.toLanguage.WellFormed ≤ M₂.toLanguage.WellFormed :=
  C.toMorphism_wellFormedOn_le (fun _ => True)

/-- Anti-degeneracy theorem for Class (a): If `s` is `WellFormed` in `M₁`, then
    under *any* `C : ExecSimCoupling`, no target program `t` that violates
    `M₂.toLanguage.WellFormed` (such as `.immediateUb` or `.stuck`) can satisfy
    `Compiles M₁.toLanguage M₂.toLanguage C.toMorphism s t`. -/
theorem admissible_rules_out_class_a_target_ub_and_stuck
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    (C : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    {s : Prog₁} {t : Prog₂}
    (hs_wf : M₁.toLanguage.sem s ≤ M₁.toLanguage.WellFormed)
    (ht_not_wf : ¬ (M₂.toLanguage.sem t ≤ M₂.toLanguage.WellFormed)) :
    ¬ Compiles M₁.toLanguage M₂.toLanguage C.toMorphism s t := by
  intro hcomp
  have h1 : M₂.toLanguage.sem t ≤ C.toMorphism M₁.toLanguage.WellFormed :=
    Preorder.le_trans hcomp (C.monotone_toMorphism hs_wf)
  have h2 : M₂.toLanguage.sem t ≤ M₂.toLanguage.WellFormed :=
    Preorder.le_trans h1 (C.toMorphism_wellFormed_le)
  exact ht_not_wf h2

/-- `π_top ToyLang ToyLang` cannot satisfy `AdmissibleCompilerMorphism`. -/
theorem π_top_not_admissible :
    ¬ AdmissibleCompilerMorphism ToyMachine ToyMachine (π_top ToyLang ToyLang) := by
  intro ⟨C, _, hEq⟩
  have hle : π_top ToyLang ToyLang ToyLang.WellFormed ≤
      C.toMorphism ToyLang.WellFormed :=
    (hEq ToyLang.WellFormed).1
  have hwf : π_top ToyLang ToyLang ToyLang.WellFormed ≤ ToyLang.WellFormed :=
    Preorder.le_trans hle C.toMorphism_wellFormed_le
  exact (hwf ⟨0, 0⟩ True.intro).1

/-- `π_chaosVal id` cannot satisfy `AdmissibleCompilerMorphism` on `ToyMachine`. -/
theorem π_chaosVal_not_admissible :
    ¬ AdmissibleCompilerMorphism ToyMachine ToyMachine (π_chaosVal id) := by
  intro ⟨C, hAdm, hEq⟩
  let emptySpec : ToyLang.Behavior := ToyLang.Spec (fun _ _ => False)
  have hle : π_chaosVal id emptySpec ≤ C.toMorphism emptySpec :=
    (hEq emptySpec).1
  cases hle ⟨0, 0⟩ (fun _ _ => True.intro) with
  | intro _ hval =>
    have hfalse : (C.toMorphism emptySpec ⟨0, 0⟩).val (fun _ _ => True.intro)
        ⟨[], .running⟩ :=
      hval ⟨[], .running⟩ True.intro
    cases hfalse with
    | intro _ hrest =>
      cases hrest with
      | intro _ hbot => exact hbot

/-- Anti-degeneracy theorem for Class (c): Neither step-zero coupling
    (`n₁ = 0`) nor bounded-fuel coupling (`n₁ = capSteps n₂ K`) satisfies
    `step_coverage`. -/
theorem stepZero_not_step_coverage :
    ¬ (∀ n₁ : Nat, ∃ _ : Nat,
        (0 = n₁) ∧ ∀ n₁' : Nat, 0 = n₁' → n₁' = n₁) := by
  intro hcov
  cases hcov 1 with
  | intro _ h => cases h.1

theorem capSteps_le_right (n K : Nat) : capSteps n K ≤ K := by
  induction n generalizing K with
  | zero => exact Nat.zero_le K
  | succ m ih =>
    cases K with
    | zero => exact Nat.le_refl 0
    | succ k => exact Nat.succ_le_succ (ih k)

theorem boundedFuel_not_step_coverage (K : Nat) :
    ¬ (∀ n₁ : Nat, ∃ n₂ : Nat,
        capSteps n₂ K = n₁ ∧
        ∀ n₁' : Nat, capSteps n₂ K = n₁' → n₁' = n₁) := by
  intro hcov
  cases hcov (K + 1) with
  | intro n₂ h =>
    have hle : capSteps n₂ K ≤ K := capSteps_le_right n₂ K
    rw [h.1] at hle
    exact Nat.not_succ_le_self K hle

/-- Anti-degeneracy theorem for Class (c): Under *any* `AdmissibleExecCoupling C`
    with `C.decompileInit 0 = 0`:
    1. `C.toMorphism (ToyLang.sem .lateUb)` is NOT `WellFormed` (exposing the
       step-2 UB that `π_boundedFuel 1` hid), and
    2. `.good` does NOT compile to `.infiniteLoop` (ruling out divergence
       introduction). -/
theorem admissible_rules_out_class_c_late_ub_and_divergence
    (C : ExecSimCoupling Nat Nat Nat Nat Nat Nat)
    (hAdm : AdmissibleExecCoupling C)
    (hInit0 : C.decompileInit 0 = 0) :
    ¬ (C.toMorphism (ToyLang.sem .lateUb) ≤ ToyLang.WellFormed) ∧
    ¬ Compiles ToyLang ToyLang C.toMorphism .good .infiniteLoop := by
  cases hAdm.step_coverage 2 with
  | intro n₂ hn₂ =>
    have hCoupled2 : C.stepCoupling n₂ 2 := hn₂.1
    have hUnique2 : ∀ n₁', C.stepCoupling n₂ n₁' → n₁' = 2 := hn₂.2
    constructor
    · intro hwf
      have hdef := (hwf ⟨0, n₂⟩ True.intro).1 2 hCoupled2
      rw [hInit0] at hdef
      have hr1 : ReachesPrefix ToyMachine.step .lateUb 1 1 [] .failed :=
        ReachesPrefix.failed 0 1 rfl
      have hr2 : ReachesPrefix ToyMachine.step .lateUb 2 0 [10] .failed :=
        ReachesPrefix.step 1 0 1 10 [] .failed rfl hr1
      exact hdef rfl [10] .failed hr2
    · intro hcomp
      have hdefGood : (C.toMorphism (ToyLang.sem .good) ⟨0, n₂⟩).defined := by
        intro n₁ _
        exact (progGood_wellFormed ⟨C.decompileInit 0, n₁⟩ True.intro).1
      cases hcomp ⟨0, n₂⟩ hdefGood with
      | intro _ hval =>
        have hLoopReaches :
            ∀ n s, ReachesPrefix ToyMachine.step .infiniteLoop n s [] .running := by
          intro n
          induction n with
          | zero => intro s; exact ReachesPrefix.zero s
          | succ k ih =>
            intro s
            exact ReachesPrefix.choice k s s (fun s' => s' = s) [] .running rfl rfl (ih s)
        have houtLoop : (ToyLang.sem .infiniteLoop ⟨0, n₂⟩).val
            ((progInfiniteLoop_wellFormed ⟨0, n₂⟩ True.intro).1) ⟨[], .running⟩ :=
          ⟨rfl, hLoopReaches n₂ 0⟩
        cases hval ⟨[], .running⟩ houtLoop with
        | intro n₁ hrest =>
          cases hrest with
          | intro hn₁ hgood =>
            have heq2 : n₁ = 2 := hUnique2 n₁ hn₁
            have hrGood : ReachesPrefix ToyMachine.step .good n₁ (C.decompileInit 0)
                (C.decompileTrace []) .running := hgood.2
            rw [heq2, hInit0] at hrGood
            generalize C.decompileTrace [] = tr0 at hrGood
            cases hrGood with
            | step _ _ s' _ tr' _ h1 hr2 =>
              dsimp [ToyMachine, toyStep] at h1
              injection h1 with _ hs'
              subst hs'
              cases hr2 with
              | step _ _ _ _ _ _ h2 _ => dsimp [ToyMachine, toyStep] at h2; cases h2
              | choice _ _ _ _ _ _ h2 _ _ => dsimp [ToyMachine, toyStep] at h2; cases h2
            | choice _ _ _ _ _ _ h1 _ _ => dsimp [ToyMachine, toyStep] at h1; cases h1

/-- Anti-degeneracy theorem for Class (d): Under *any* `AdmissibleExecCoupling C`
    with `C.decompileTrace [10] = [10]` and `C.decompileVal 42 = 42`, `.good`
    can NEITHER compile to `.silentReturn` (trace erasure) NOR compile to
    `.wrongVal` (return-value corruption). -/
theorem admissible_rules_out_class_d_trace_and_val_erasure
    (C : ExecSimCoupling Nat Nat Nat Nat Nat Nat)
    (hAdm : AdmissibleExecCoupling C)
    (hTr10 : C.decompileTrace [10] = [10])
    (hVal42 : C.decompileVal 42 = 42) :
    ¬ Compiles ToyLang ToyLang C.toMorphism .good .silentReturn ∧
    ¬ Compiles ToyLang ToyLang C.toMorphism .good .wrongVal := by
  have hSpecBridge :
      C.toMorphism specGood ≤
      ToyLang.SpecOn
        (fun _ => True)
        (fun _ out₂ =>
          (∀ v, (out₂.outcome.map C.decompileVal) = .terminated (.normal v) →
            C.decompileTrace out₂.trace = [10] ∧ v = 42) ∧
          (out₂.outcome.map C.decompileVal) ≠ .terminated .unwind) :=
    C.toMorphism_specOn_le (fun _ => True) (fun _ out₁ =>
      (∀ v, out₁.outcome = .terminated (.normal v) → out₁.trace = [10] ∧ v = 42) ∧
      out₁.outcome ≠ .terminated .unwind)
  constructor
  · intro hcomp
    have hTargetSpec :=
      Preorder.le_trans hcomp
        (Preorder.le_trans (C.monotone_toMorphism progGood_satisfies_specGood) hSpecBridge)
    cases hTargetSpec ⟨0, 2⟩ True.intro with
    | intro hdef hval =>
      have hr1 : ReachesPrefix ToyMachine.step .silentReturn 1 1 [] (.terminated (.normal 42)) :=
        ReachesPrefix.terminated 0 1 (.normal 42) rfl
      have hr2 : ReachesPrefix ToyMachine.step .silentReturn 2 0 [] (.terminated (.normal 42)) :=
        ReachesPrefix.choice 1 0 1 (fun s' => s' = 1) [] (.terminated (.normal 42)) rfl rfl hr1
      have hpost := (hval ⟨[], .terminated (.normal 42)⟩ ⟨rfl, hr2⟩).1 (C.decompileVal 42) rfl
      have hTrEq : C.decompileTrace [] = C.decompileTrace [10] := by
        rw [hpost.1, hTr10]
      have hNilEq : ([] : List Nat) = [10] := hAdm.trace_injective hTrEq
      cases hNilEq
  · intro hcomp
    have hTargetSpec :=
      Preorder.le_trans hcomp
        (Preorder.le_trans (C.monotone_toMorphism progGood_satisfies_specGood) hSpecBridge)
    cases hTargetSpec ⟨0, 2⟩ True.intro with
    | intro hdef hval =>
      have hr1 : ReachesPrefix ToyMachine.step .wrongVal 1 1 [] (.terminated (.normal 999)) :=
        ReachesPrefix.terminated 0 1 (.normal 999) rfl
      have hr2 : ReachesPrefix ToyMachine.step .wrongVal 2 0 [10] (.terminated (.normal 999)) :=
        ReachesPrefix.step 1 0 1 10 [] (.terminated (.normal 999)) rfl hr1
      have hpost := (hval ⟨[10], .terminated (.normal 999)⟩ ⟨rfl, hr2⟩).1 (C.decompileVal 999) rfl
      have hValEq : C.decompileVal 999 = C.decompileVal 42 := by
        rw [hpost.2, hVal42]
      have h999 : (999 : Nat) = 42 := hAdm.val_injective hValEq
      cases h999

/-!
### 4.4 `verify_through_passes`: Unanchored Vulnerability vs. Target-Anchored Pipelines
-/

/-- Vulnerability of unanchored `verify_through_passes`: Because
    `verify_through_passes` concludes `C.Verified s (π_v spec)` (whose target
    obligation is `L_tgt.sem (C.compile s) ≤ C.π (π_v spec)`), if `π_v` is not
    constrained by admissibility or target anchoring, choosing `π_v := π_top`
    allows `verify_through_passes` to "verify" `s = .immediateUb` and
    `C.compile s = .immediateUb` from the valid proof
    `ToyLang.sem .good ≤ specGood`! -/
theorem verify_through_passes_unanchored_vulnerable :
    let C_id : Compiler ToyLang ToyLang := { compile := id, π := id }
    C_id.Verified .immediateUb (π_top ToyLang ToyLang specGood) ∧
    ¬ (ToyLang.sem .immediateUb ≤ ToyLang.WellFormed) := by
  intro C_id
  have hVer :=
    verify_through_passes
      (C := C_id)
      (π_v := π_top ToyLang ToyLang)
      progGood_satisfies_specGood
      (abstracts_π_top_trivial ToyLang ToyLang .good .immediateUb)
      (monotone_π_top ToyLang ToyLang)
      ⟨monotone_id, Preorder.le_refl _⟩
  exact ⟨hVer, progImmediateUb_not_wellFormed⟩

/-- Target-anchored cross-pass verification theorem: When the end of a pass
    chain is anchored to a trusted target specification `spec_tgt : L_tgt.Behavior`
    via `h_anchor : C.π (π_v spec_v) ≤ spec_tgt`, the compiled target program
    `C.compile s` genuinely satisfies `L_tgt.sem (C.compile s) ≤ spec_tgt`. -/
theorem verify_through_passes_anchored
    {L_v L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {π_v : L_v.Behavior → L_src.Behavior}
    {spec_v : L_v.Behavior} {spec_tgt : L_tgt.Behavior}
    {v : L_v.Prog} {s : L_src.Prog}
    (h_proof : L_v.sem v ≤ spec_v)
    (h_abs : Abstracts L_v L_src π_v v s)
    (h_mono_v : Monotone π_v)
    (h_comp : C.SoundOn s)
    (h_anchor : C.π (π_v spec_v) ≤ spec_tgt) :
    C.Verified s (π_v spec_v) ∧ L_tgt.sem (C.compile s) ≤ spec_tgt := by
  have hVer := verify_through_passes h_proof h_abs h_mono_v h_comp
  exact ⟨hVer, Preorder.le_trans hVer.2.2 h_anchor⟩

/-- Step-sensitive termination specification on `ToyLang` requiring that at
    step budget `q.steps = 2`, execution has terminated normally with `42`. -/
def specTerminatesAt2 : ToyLang.Behavior :=
  ToyLang.Spec (fun q out =>
    q.steps = 2 → out.outcome = .terminated (.normal 42))

/-- Target anchoring against `specGood` (and `specTerminatesAt2` for step
    distortion) rejects Classes **(a), (b), (d)**, and step-sensitive **(c)**. -/
theorem target_anchor_rejects_degenerate_classes :
    ¬ (π_top ToyLang ToyLang specGood ≤ specGood) ∧
    ¬ (π_chaosVal id specGood ≤ specGood) ∧
    ¬ (π_stepZero specTerminatesAt2 ≤ specTerminatesAt2) ∧
    ¬ (covariantMorphism collapseValProj specGood ≤ specGood) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hTop
    exact (hTop ⟨0, 0⟩ True.intro).1
  · intro hChaos
    cases hChaos ⟨0, 2⟩ True.intro with
    | intro _ hval =>
      have hbad := hval ⟨[10], .terminated (.normal 999)⟩ True.intro
      have h999 := (hbad.1 999 rfl).2
      cases h999
  · intro hZero
    cases hZero ⟨0, 2⟩ True.intro with
    | intro _ hval =>
      have hrun : (π_stepZero specTerminatesAt2 ⟨0, 2⟩).val True.intro
          ⟨[], .running⟩ := by
        intro h02
        cases h02
      have hterm := hval ⟨[], .running⟩ hrun rfl
      cases hterm
  · intro hCollapse
    cases hCollapse ⟨0, 2⟩ True.intro with
    | intro _ hval =>
      have hbad : (covariantMorphism collapseValProj specGood ⟨0, 2⟩).val True.intro
          ⟨[10], .terminated (.normal 999)⟩ := by
        refine ⟨⟨[10], .terminated (.normal 42)⟩, ?_, rfl⟩
        refine ⟨?_, fun h => by cases h⟩
        intro v hv
        injection hv with hv'
        injection hv' with hv''
        subst hv''
        exact ⟨rfl, rfl⟩
      have hpost := hval ⟨[10], .terminated (.normal 999)⟩ hbad
      have h999 := (hpost.1 999 rfl).2
      cases h999

/-- Crucial subtlety: for step-independent partial-correctness specifications
    (such as `WellFormed`, `EnsuresEqArg`, `EnsuresRetLibInv`, and `specGood`,
    whose `pre` and `post` depend only on `q.init` and `out`, not `q.steps`),
    `π_stepZero spec = spec` and `π_boundedFuel K spec = spec` hold
    definitionally (`rfl`)! Consequently, target anchoring against a
    step-independent specification is *blind* to Class (c) query distortion,
    demonstrating why `AdmissibleExecCoupling.step_coverage` is strictly
    required. -/
theorem stepIndependent_target_anchor_blind_to_class_c :
    π_stepZero specGood = specGood ∧
    π_stepZero ToyLang.WellFormed = ToyLang.WellFormed ∧
    π_boundedFuel 1 specGood = specGood ∧
    let C_zero : Compiler ToyLang ToyLang := {
      compile := fun _ => .infiniteLoop
      π := π_stepZero
    }
    C_zero.SoundOn .good ∧
    C_zero.Verified .good specGood ∧
    C_zero.π specGood ≤ specGood := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro C_zero
  have hSound : C_zero.SoundOn .good :=
    ⟨monotone_π_stepZero,
     counterexample_class_c_stepZero_diverges_and_masks_ub.2.2.1⟩
  exact ⟨hSound,
         Compiler.SoundOn.verify hSound progGood_satisfies_specGood,
         Preorder.le_refl specGood⟩

/-!
## 5. Closure and Compositionality of `AdmissibleExecCoupling`
-/

/-- Identity simulation coupling on `(State, Obs, Val)`. -/
def ExecSimCoupling.id (State Obs Val : Type) :
    ExecSimCoupling State Obs Val State Obs Val where
  decompileInit := fun s => s
  stepCoupling n₂ n₁ := n₁ = n₂
  decompileTrace := fun tr => tr
  decompileVal := fun v => v

/-- `ExecSimCoupling.id` satisfies `AdmissibleExecCoupling`. -/
theorem AdmissibleExecCoupling.id (State Obs Val : Type) :
    AdmissibleExecCoupling (ExecSimCoupling.id State Obs Val) where
  step_nonempty n₂ := ⟨n₂, rfl⟩
  step_coverage n₁ := ⟨n₁, rfl, fun _ h => h⟩
  trace_injective _ _ h := h
  val_injective _ _ h := h

theorem PrefixOutcome.map_id {Val : Type} (out : PrefixOutcome Val) :
    out.map (fun v => v) = out := by
  cases out with
  | running => rfl
  | terminated t =>
    cases t <;> rfl
  | failed => rfl
  | stuck => rfl

theorem ExecSimCoupling.decompileOut_id {State Obs Val : Type}
    (out : ExecOut Obs Val) :
    (ExecSimCoupling.id State Obs Val).decompileOut out = out := by
  cases out with
  | mk trace outcome =>
    dsimp [ExecSimCoupling.decompileOut, ExecSimCoupling.id]
    rw [PrefixOutcome.map_id]

/-- `(ExecSimCoupling.id State Obs Val).toMorphism b` is mutual-refinement
    equivalent to `b`. -/
theorem ExecSimCoupling.id_toMorphism_equiv {State Obs Val : Type}
    (b : Behavior (ExecQuery State) (ExecOut Obs Val)) :
    (ExecSimCoupling.id State Obs Val).toMorphism b ≤ b ∧
    b ≤ (ExecSimCoupling.id State Obs Val).toMorphism b := by
  constructor
  · intro q hdef
    refine ⟨fun n₁ hn => hn ▸ hdef, ?_⟩
    intro out ⟨n₁, hn, hval⟩
    subst hn
    rw [ExecSimCoupling.decompileOut_id] at hval
    exact hval
  · intro q hdef
    refine ⟨hdef q.steps rfl, ?_⟩
    intro out hval
    refine ⟨q.steps, rfl, ?_⟩
    rw [ExecSimCoupling.decompileOut_id]
    exact hval

/-- `AdmissibleCompilerMorphism` holds for the identity morphism `id`. -/
theorem AdmissibleCompilerMorphism.id
    (M : SmallStepMachine Prog State Obs Val) :
    AdmissibleCompilerMorphism M M (fun b => b) := by
  refine ⟨ExecSimCoupling.id State Obs Val, AdmissibleExecCoupling.id State Obs Val, ?_⟩
  intro b
  have h := ExecSimCoupling.id_toMorphism_equiv b
  exact ⟨h.2, h.1⟩

/-- Composition of two simulation couplings `C₁₂` (from `1` to `2`) and `C₂₃`
    (from `2` to `3`). -/
def ExecSimCoupling.comp
    (C₁₂ : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (C₂₃ : ExecSimCoupling State₂ Obs₂ Val₂ State₃ Obs₃ Val₃) :
    ExecSimCoupling State₁ Obs₁ Val₁ State₃ Obs₃ Val₃ where
  decompileInit s₃ := C₁₂.decompileInit (C₂₃.decompileInit s₃)
  stepCoupling n₃ n₁ := ∃ n₂, C₂₃.stepCoupling n₃ n₂ ∧ C₁₂.stepCoupling n₂ n₁
  decompileTrace tr₃ := C₁₂.decompileTrace (C₂₃.decompileTrace tr₃)
  decompileVal v₃ := C₁₂.decompileVal (C₂₃.decompileVal v₃)

/-- `AdmissibleExecCoupling` is closed under composition (`ExecSimCoupling.comp`). -/
theorem AdmissibleExecCoupling.comp
    {C₁₂ : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂}
    {C₂₃ : ExecSimCoupling State₂ Obs₂ Val₂ State₃ Obs₃ Val₃}
    (h₁₂ : AdmissibleExecCoupling C₁₂)
    (h₂₃ : AdmissibleExecCoupling C₂₃) :
    AdmissibleExecCoupling (C₁₂.comp C₂₃) where
  step_nonempty n₃ := by
    cases h₂₃.step_nonempty n₃ with
    | intro n₂ hn₂ =>
      cases h₁₂.step_nonempty n₂ with
      | intro n₁ hn₁ =>
        exact ⟨n₁, n₂, hn₂, hn₁⟩
  step_coverage n₁ := by
    cases h₁₂.step_coverage n₁ with
    | intro n₂ hn₂ =>
      cases h₂₃.step_coverage n₂ with
      | intro n₃ hn₃ =>
        refine ⟨n₃, ⟨n₂, hn₃.1, hn₂.1⟩, ?_⟩
        intro n₁' ⟨n₂', hn₃', hn₂'⟩
        have heq₂ : n₂' = n₂ := hn₃.2 n₂' hn₃'
        subst heq₂
        exact hn₂.2 n₁' hn₂'
  trace_injective _ _ h :=
    h₂₃.trace_injective (h₁₂.trace_injective h)
  val_injective _ _ h :=
    h₂₃.val_injective (h₁₂.val_injective h)

theorem PrefixOutcome.map_comp {Val₁ Val₂ Val₃ : Type}
    (f : Val₂ → Val₁) (g : Val₃ → Val₂) (out : PrefixOutcome Val₃) :
    (out.map g).map f = out.map (fun v => f (g v)) := by
  cases out with
  | running => rfl
  | terminated t =>
    cases t <;> rfl
  | failed => rfl
  | stuck => rfl

theorem ExecSimCoupling.decompileOut_comp
    (C₁₂ : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (C₂₃ : ExecSimCoupling State₂ Obs₂ Val₂ State₃ Obs₃ Val₃)
    (out₃ : ExecOut Obs₃ Val₃) :
    C₁₂.decompileOut (C₂₃.decompileOut out₃) =
      (C₁₂.comp C₂₃).decompileOut out₃ := by
  cases out₃ with
  | mk trace outcome =>
    dsimp [ExecSimCoupling.decompileOut, ExecSimCoupling.comp]
    rw [PrefixOutcome.map_comp]

/-- Functorial equivalence of composed `toMorphism`:
    `C₂₃.toMorphism (C₁₂.toMorphism b)` and `(C₁₂.comp C₂₃).toMorphism b`
    mutually refine each other at every behavior `b`. -/
theorem ExecSimCoupling.comp_toMorphism_equiv
    (C₁₂ : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (C₂₃ : ExecSimCoupling State₂ Obs₂ Val₂ State₃ Obs₃ Val₃)
    (b : Behavior (ExecQuery State₁) (ExecOut Obs₁ Val₁)) :
    C₂₃.toMorphism (C₁₂.toMorphism b) ≤ (C₁₂.comp C₂₃).toMorphism b ∧
    (C₁₂.comp C₂₃).toMorphism b ≤ C₂₃.toMorphism (C₁₂.toMorphism b) := by
  constructor
  · intro q₃ hdef
    refine ⟨fun n₂ hn₂ n₁ hn₁ => hdef n₁ ⟨n₂, hn₂, hn₁⟩, ?_⟩
    intro out₃ ⟨n₂, hn₂, n₁, hn₁, hval⟩
    refine ⟨n₁, ⟨n₂, hn₂, hn₁⟩, ?_⟩
    rw [← ExecSimCoupling.decompileOut_comp]
    exact hval
  · intro q₃ hdef
    refine ⟨fun n₁ ⟨n₂, hn₂, hn₁⟩ => hdef n₂ hn₂ n₁ hn₁, ?_⟩
    intro out₃ ⟨n₁, ⟨n₂, hn₂, hn₁⟩, hval⟩
    refine ⟨n₂, hn₂, n₁, hn₁, ?_⟩
    rw [ExecSimCoupling.decompileOut_comp]
    exact hval

/-- `AdmissibleCompilerMorphism` is closed under composition (`π₂ ∘ π₁`). -/
theorem AdmissibleCompilerMorphism.comp
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    {M₃ : SmallStepMachine Prog₃ State₃ Obs₃ Val₃}
    {π₁ : M₁.toLanguage.Behavior → M₂.toLanguage.Behavior}
    {π₂ : M₂.toLanguage.Behavior → M₃.toLanguage.Behavior}
    (h₁ : AdmissibleCompilerMorphism M₁ M₂ π₁)
    (h₂ : AdmissibleCompilerMorphism M₂ M₃ π₂)
    (h_mono₂ : Monotone π₂) :
    AdmissibleCompilerMorphism M₁ M₃ (fun b => π₂ (π₁ b)) := by
  cases h₁ with
  | intro C₁₂ hC₁₂ =>
    cases h₂ with
    | intro C₂₃ hC₂₃ =>
      refine ⟨C₁₂.comp C₂₃, AdmissibleExecCoupling.comp hC₁₂.1 hC₂₃.1, ?_⟩
      intro b
      have hcomp := ExecSimCoupling.comp_toMorphism_equiv C₁₂ C₂₃ b
      constructor
      · have hStep1 : π₂ (π₁ b) ≤ π₂ (C₁₂.toMorphism b) :=
          h_mono₂ (hC₁₂.2 b).1
        have hStep2 : π₂ (C₁₂.toMorphism b) ≤ C₂₃.toMorphism (C₁₂.toMorphism b) :=
          (hC₂₃.2 (C₁₂.toMorphism b)).1
        exact Preorder.le_trans hStep1 (Preorder.le_trans hStep2 hcomp.1)
      · have hStep1 : (C₁₂.comp C₂₃).toMorphism b ≤ C₂₃.toMorphism (C₁₂.toMorphism b) :=
          hcomp.2
        have hStep2 : C₂₃.toMorphism (C₁₂.toMorphism b) ≤ π₂ (C₁₂.toMorphism b) :=
          (hC₂₃.2 (C₁₂.toMorphism b)).2
        have hStep3 : π₂ (C₁₂.toMorphism b) ≤ π₂ (π₁ b) :=
          h_mono₂ (hC₁₂.2 b).2
        exact Preorder.le_trans hStep1 (Preorder.le_trans hStep2 hStep3)

/-- Composing two `Compiles` passes governed by `ExecSimCoupling` yields
    `Compiles` under the composed coupling `C₁₂.comp C₂₃`. -/
theorem Compiles.comp_coupling
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    {M₃ : SmallStepMachine Prog₃ State₃ Obs₃ Val₃}
    (C₁₂ : ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂)
    (C₂₃ : ExecSimCoupling State₂ Obs₂ Val₂ State₃ Obs₃ Val₃)
    {p₁ : Prog₁} {p₂ : Prog₂} {p₃ : Prog₃}
    (h₁₂ : Compiles M₁.toLanguage M₂.toLanguage C₁₂.toMorphism p₁ p₂)
    (h₂₃ : Compiles M₂.toLanguage M₃.toLanguage C₂₃.toMorphism p₂ p₃) :
    Compiles M₁.toLanguage M₃.toLanguage (C₁₂.comp C₂₃).toMorphism p₁ p₃ :=
  Preorder.le_trans
    (Compiles.comp h₁₂ h₂₃ C₂₃.monotone_toMorphism)
    (ExecSimCoupling.comp_toMorphism_equiv C₁₂ C₂₃ (M₁.toLanguage.sem p₁)).1

/-- Composing two `Abstracts` passes governed by `ExecSimCoupling` yields
    `Abstracts` under the composed coupling `C₂₁.comp C₁_src`. -/
theorem Abstracts.comp_coupling
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M_src : SmallStepMachine Prog_src State_src Obs_src Val_src}
    (C₂₁ : ExecSimCoupling State₂ Obs₂ Val₂ State₁ Obs₁ Val₁)
    (C₁_src : ExecSimCoupling State₁ Obs₁ Val₁ State_src Obs_src Val_src)
    {v₂ : Prog₂} {v₁ : Prog₁} {s : Prog_src}
    (h₁ : Abstracts M₁.toLanguage M_src.toLanguage C₁_src.toMorphism v₁ s)
    (h₂ : Abstracts M₂.toLanguage M₁.toLanguage C₂₁.toMorphism v₂ v₁) :
    Abstracts M₂.toLanguage M_src.toLanguage (C₂₁.comp C₁_src).toMorphism v₂ s :=
  Preorder.le_trans
    (Abstracts.comp h₁ h₂ C₁_src.monotone_toMorphism)
    (ExecSimCoupling.comp_toMorphism_equiv C₂₁ C₁_src (M₂.toLanguage.sem v₂)).1

/-!
## Section 6: Concrete Positive Instantiations (Multi-Step Lowering and Upward Abstraction)

We now prove concrete positive instances demonstrating that
`AdmissibleExecCoupling` is neither vacuous nor restricted to 1-to-1 lockstep
compilers:
1. **$1 \to 2$ Multi-Step Lowering (`MirMultiLang → X86MultiLang`):**
   Each MIR instruction lowers to 2 x86 micro-instructions (fetch/compute into
   `rax` via a silent `.choice` step, followed by commit/return). We prove:
   - `admissible_stepScale2Coupling : AdmissibleExecCoupling stepScale2Coupling`,
   - Universal compilation `compileMirToX86_compiles` for all `p : MirMultiProg`,
   - Why a single-valued functional step pullback (`n₁ = div2 n₂` alone or
     `n₁ = ceil2 n₂` alone) is *insufficient* (`not_compiles_floor_only_failNow`
     and `not_compiles_ceil_only_incAndRet`), justifying the relational step
     window `n₁ = div2 n₂ ∨ n₁ = ceil2 n₂` in `ExecSimCoupling`.
2. **Upward Borrow-Erasure Abstraction (`FuncLang → MirMultiLang`) Composed
   End-to-End with Multi-Step Lowering (`MirMultiLang → X86MultiLang`):**
   A functional specification machine `FuncLang` abstracts imperative borrow
   steps in `MirMultiLang` (`Abstracts FuncLang MirMultiLang`), and composes
   via `AdmissibleExecCoupling.comp` and `verify_through_passes_anchored` to
   verify the compiled x86-64 program against an anchored target specification.
-/

/-- Floor division by 2 (`n / 2`), representing completed 2-micro-step source
    instructions after `n` target micro-steps. -/
def div2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => (div2 n) + 1

/-- Ceiling division by 2 (`(n + 1) / 2`), representing started 2-micro-step
    source instructions at `n` target micro-steps. -/
def ceil2 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => (ceil2 n) + 1

/-- Exact step doubling (`2 * m`). -/
def double : Nat → Nat
  | 0 => 0
  | m + 1 => (double m) + 2

theorem div2_double (m : Nat) : div2 (double m) = m := by
  induction m with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

theorem ceil2_double (m : Nat) : ceil2 (double m) = m := by
  induction m with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

/-- Elementary 2-step induction principle on `Nat` (constructive, zero imports). -/
theorem nat_pair_ind (P : Nat → Prop) (h0 : P 0) (h1 : P 1)
    (hstep : ∀ n, P n → P (n + 2)) (n : Nat) : P n ∧ P (n + 1) := by
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ k ih => exact ⟨ih.2, hstep k ih.1⟩

/-- Every positive target step budget `k + 1` has a positive ceiling `ceil2 (k + 1) = m + 1`. -/
theorem ceil2_succ_exists (k : Nat) : ∃ m : Nat, ceil2 (k + 1) = m + 1 :=
  (nat_pair_ind (fun n => ∃ m : Nat, ceil2 (n + 1) = m + 1)
    ⟨0, rfl⟩
    ⟨0, rfl⟩
    (fun _ ⟨m, hm⟩ => ⟨m + 1, congrArg Nat.succ hm⟩)
    k).1

/-- Source MIR program family for $1 \to 2$ multi-step lowering:
    - `.incAndRet`: increments argument `x` while emitting observation `1` (step 1),
      then returns `x + 1` (step 2).
    - `.failNow`: triggers immediate UB (`.failed`) on step 1. -/
inductive MirMultiProg where
  | incAndRet
  | failNow

/-- State of `MirMultiMachine`: program counter `pc` and local slot `arg`. -/
structure MirMultiState where
  pc : Nat
  arg : Nat

def mirMultiStep (p : MirMultiProg) (s : MirMultiState)
    (r : StepResult MirMultiState Nat Nat) : Prop :=
  match p, s with
  | .incAndRet, ⟨0, x⟩ => r = .step 1 ⟨1, x + 1⟩
  | .incAndRet, ⟨_ + 1, x⟩ => r = .terminated (.normal x)
  | .failNow, _ => r = .failed

def MirMultiMachine : SmallStepMachine MirMultiProg MirMultiState Nat Nat where
  initState _ s := s.pc = 0
  step := mirMultiStep

abbrev MirMultiLang : Language := MirMultiMachine.toLanguage

/-- Target x86-64 program family where each MIR instruction is lowered to a
    2-micro-step sequence (`phase = false` followed by `phase = true`):
    - For `.incAndRet`:
      - `(pc = 0, phase = false)`: load `arg` and compute `rax := arg + 1`
        via silent internal transition `.choice`.
      - `(pc = 0, phase = true)`: store `rax` back to `arg`, emit observation `1`,
        and advance to `(pc = 1, phase = false)`.
      - `(pc = 1, phase = false)`: move return value from `arg` into `rax`
        via silent internal transition `.choice`.
      - `(pc = 1, phase = true)`: execute `ret`, terminating with `.normal rax`.
    - For `.failNow`:
      - `(pc = 0, phase = false)` faults immediately with `.failed`. -/
inductive X86MultiProg where
  | incAndRet
  | failNow

structure X86MultiState where
  pc : Nat
  phase : Bool
  arg : Nat
  rax : Nat

def x86MultiStep (p : X86MultiProg) (s : X86MultiState)
    (r : StepResult X86MultiState Nat Nat) : Prop :=
  match p, s with
  | .incAndRet, ⟨0, false, x, _⟩ =>
    r = .choice (fun s' => s' = ⟨0, true, x, x + 1⟩)
  | .incAndRet, ⟨0, true, _, rVal⟩ =>
    r = .step 1 ⟨1, false, rVal, rVal⟩
  | .incAndRet, ⟨_ + 1, false, x, _⟩ =>
    r = .choice (fun s' => s' = ⟨1, true, x, x⟩)
  | .incAndRet, ⟨_ + 1, true, _, rVal⟩ =>
    r = .terminated (.normal rVal)
  | .failNow, _ =>
    r = .failed

def X86MultiMachine : SmallStepMachine X86MultiProg X86MultiState Nat Nat where
  initState _ s := s.pc = 0 ∧ s.phase = false ∧ s.rax = 0
  step := x86MultiStep

abbrev X86MultiLang : Language := X86MultiMachine.toLanguage

/-- State decompilation from `X86MultiState` to `MirMultiState`. -/
def decompileMirState (s : X86MultiState) : MirMultiState :=
  ⟨s.pc, s.arg⟩

/-- $1 \to 2$ multi-step execution coupling (`MirMultiLang → X86MultiLang`):
    each MIR step expands into 2 x86 micro-steps, so target step `n₂` couples
    to `{div2 n₂, ceil2 n₂}`. At exact instruction boundaries `n₂ = double n₁`,
    `div2 n₂ = ceil2 n₂ = n₁` uniquely pins source step `n₁`. -/
def mirToX86Coupling :
    ExecSimCoupling MirMultiState Nat Nat X86MultiState Nat Nat where
  decompileInit := decompileMirState
  stepCoupling := fun n₂ n₁ => n₁ = div2 n₂ ∨ n₁ = ceil2 n₂
  decompileTrace := fun tr => tr
  decompileVal := fun v => v

/-- `mirToX86Coupling` satisfies all four conditions of `AdmissibleExecCoupling`. -/
theorem admissible_mirToX86Coupling :
    AdmissibleExecCoupling mirToX86Coupling where
  step_nonempty := fun n₂ => ⟨div2 n₂, Or.inl rfl⟩
  step_coverage := fun n₁ => by
    refine ⟨double n₁, Or.inl (div2_double n₁).symm, ?_⟩
    intro n₁' h'
    cases h' with
    | inl hdiv =>
      rw [hdiv, div2_double]
    | inr hceil =>
      rw [hceil, ceil2_double]
  trace_injective := fun _ _ h => h
  val_injective := fun _ _ h => h

theorem decompileOut_mirToX86 (out : ExecOut Nat Nat) :
    mirToX86Coupling.decompileOut out = out := by
  cases out with
  | mk trace outcome =>
    dsimp [ExecSimCoupling.decompileOut, mirToX86Coupling]
    rw [PrefixOutcome.map_id]

def compileMirToX86 : MirMultiProg → X86MultiProg
  | .incAndRet => .incAndRet
  | .failNow => .failNow

/-- `X86MultiProg.incAndRet` never reaches `.failed` or `.stuck` from any state
    at any step budget `n`. -/
theorem x86IncAndRet_always_safe (n : Nat) :
    ∀ (s : X86MultiState) (tr : List Nat) (out : PrefixOutcome Nat),
      ReachesPrefix x86MultiStep .incAndRet n s tr out → out.isSafe := by
  induction n with
  | zero =>
    intro _ _ _ hr
    cases hr with
    | zero => exact True.intro
  | succ k ih =>
    intro s tr out hr
    cases s with
    | mk pc phase arg rax =>
      cases pc with
      | zero =>
        cases phase with
        | false =>
          cases hr with
          | step _ _ _ _ _ _ hstep _ => dsimp [x86MultiStep] at hstep; cases hstep
          | choice _ _ s' _ _ _ hstep hs' hr' =>
            dsimp [x86MultiStep] at hstep
            injection hstep with hpred
            rw [hpred] at hs'
            subst hs'
            exact ih (X86MultiState.mk 0 true arg (arg + 1)) tr out hr'
          | emptyChoice _ _ _ hstep hempty =>
            dsimp [x86MultiStep] at hstep
            injection hstep with hpred
            rw [hpred] at hempty
            exact False.elim (hempty ⟨X86MultiState.mk 0 true arg (arg + 1), rfl⟩)
          | terminated _ _ _ _ => exact True.intro
          | failed _ _ hstep => dsimp [x86MultiStep] at hstep; cases hstep
          | noStep _ _ hno =>
            exact False.elim (hno ⟨StepResult.choice (fun s' => s' = X86MultiState.mk 0 true arg (arg + 1)), rfl⟩)
        | true =>
          cases hr with
          | step _ _ s' _ tr' _ hstep hr' =>
            dsimp [x86MultiStep] at hstep
            injection hstep with _ hs'
            subst hs'
            exact ih (X86MultiState.mk 1 false rax rax) tr' out hr'
          | choice _ _ _ _ _ _ hstep _ _ => dsimp [x86MultiStep] at hstep; cases hstep
          | emptyChoice _ _ _ hstep _ => dsimp [x86MultiStep] at hstep; cases hstep
          | terminated _ _ _ _ => exact True.intro
          | failed _ _ hstep => dsimp [x86MultiStep] at hstep; cases hstep
          | noStep _ _ hno =>
            exact False.elim (hno ⟨StepResult.step 1 (X86MultiState.mk 1 false rax rax), rfl⟩)
      | succ pc1 =>
        cases phase with
        | false =>
          cases hr with
          | step _ _ _ _ _ _ hstep _ => dsimp [x86MultiStep] at hstep; cases hstep
          | choice _ _ s' _ _ _ hstep hs' hr' =>
            dsimp [x86MultiStep] at hstep
            injection hstep with hpred
            rw [hpred] at hs'
            subst hs'
            exact ih (X86MultiState.mk 1 true arg arg) tr out hr'
          | emptyChoice _ _ _ hstep hempty =>
            dsimp [x86MultiStep] at hstep
            injection hstep with hpred
            rw [hpred] at hempty
            exact False.elim (hempty ⟨X86MultiState.mk 1 true arg arg, rfl⟩)
          | terminated _ _ _ _ => exact True.intro
          | failed _ _ hstep => dsimp [x86MultiStep] at hstep; cases hstep
          | noStep _ _ hno =>
            exact False.elim (hno ⟨StepResult.choice (fun s' => s' = X86MultiState.mk 1 true arg arg), rfl⟩)
        | true =>
          cases hr with
          | step _ _ _ _ _ _ hstep _ => dsimp [x86MultiStep] at hstep; cases hstep
          | choice _ _ _ _ _ _ hstep _ _ => dsimp [x86MultiStep] at hstep; cases hstep
          | emptyChoice _ _ _ hstep _ => dsimp [x86MultiStep] at hstep; cases hstep
          | terminated _ _ _ _ => exact True.intro
          | failed _ _ hstep => dsimp [x86MultiStep] at hstep; cases hstep
          | noStep _ _ hno =>
            exact False.elim (hno ⟨StepResult.terminated (.normal rax), rfl⟩)

/-- Backward simulation of `X86MultiMachine` on `.incAndRet`: every target
    execution prefix of length `n` from `⟨0, false, x, 0⟩` matches the source
    `MirMultiMachine` execution prefix of length `div2 n` from `⟨0, x⟩`. -/
theorem x86IncAndRet_simulates_at_div2 (n x : Nat) (tr : List Nat)
    (out : PrefixOutcome Nat)
    (hr : ReachesPrefix x86MultiStep .incAndRet n (X86MultiState.mk 0 false x 0) tr out) :
    ReachesPrefix mirMultiStep .incAndRet (div2 n) (MirMultiState.mk 0 x) tr out := by
  cases n with
  | zero =>
    cases hr with
    | zero => exact ReachesPrefix.zero (MirMultiState.mk 0 x)
  | succ n1 =>
    cases hr with
    | step _ _ _ _ _ _ h1 _ => dsimp [x86MultiStep] at h1; cases h1
    | choice _ _ s1 _ _ _ h1 hs1 hr1 =>
      dsimp [x86MultiStep] at h1
      injection h1 with hpred1
      rw [hpred1] at hs1
      subst hs1
      cases n1 with
      | zero =>
        cases hr1 with
        | zero => exact ReachesPrefix.zero (MirMultiState.mk 0 x)
      | succ n2 =>
        cases hr1 with
        | step _ _ s2 obs1 tr1 _ h2 hr2 =>
          dsimp [x86MultiStep] at h2
          injection h2 with hobs1 hs2
          subst hobs1 hs2
          cases n2 with
          | zero =>
            cases hr2 with
            | zero =>
              exact ReachesPrefix.step 0 (MirMultiState.mk 0 x) (MirMultiState.mk 1 (x + 1))
                1 [] .running rfl (ReachesPrefix.zero (MirMultiState.mk 1 (x + 1)))
          | succ n3 =>
            cases hr2 with
            | step _ _ _ _ _ _ h3 _ => dsimp [x86MultiStep] at h3; cases h3
            | choice _ _ s3 _ _ _ h3 hs3 hr3 =>
              dsimp [x86MultiStep] at h3
              injection h3 with hpred3
              rw [hpred3] at hs3
              subst hs3
              cases n3 with
              | zero =>
                cases hr3 with
                | zero =>
                  exact ReachesPrefix.step 0 (MirMultiState.mk 0 x) (MirMultiState.mk 1 (x + 1))
                    1 [] .running rfl (ReachesPrefix.zero (MirMultiState.mk 1 (x + 1)))
              | succ n4 =>
                cases hr3 with
                | step _ _ _ _ _ _ h4 _ => dsimp [x86MultiStep] at h4; cases h4
                | choice _ _ _ _ _ _ h4 _ _ => dsimp [x86MultiStep] at h4; cases h4
                | emptyChoice _ _ _ h4 _ => dsimp [x86MultiStep] at h4; cases h4
                | terminated _ _ res h4 =>
                  dsimp [x86MultiStep] at h4
                  injection h4 with hres
                  subst hres
                  exact ReachesPrefix.step ((div2 n4) + 1) (MirMultiState.mk 0 x)
                    (MirMultiState.mk 1 (x + 1)) 1 []
                    (.terminated (.normal (x + 1))) rfl
                    (ReachesPrefix.terminated (div2 n4) (MirMultiState.mk 1 (x + 1))
                      (.normal (x + 1)) rfl)
                | failed _ _ h4 => dsimp [x86MultiStep] at h4; cases h4
                | noStep _ _ hno =>
                  exact False.elim (hno ⟨StepResult.terminated (.normal (x + 1)), rfl⟩)
            | emptyChoice _ _ _ h3 hempty =>
              dsimp [x86MultiStep] at h3
              injection h3 with hpred3
              rw [hpred3] at hempty
              exact False.elim (hempty ⟨X86MultiState.mk 1 true (x + 1) (x + 1), rfl⟩)
            | terminated _ _ _ h3 => dsimp [x86MultiStep] at h3; cases h3
            | failed _ _ h3 => dsimp [x86MultiStep] at h3; cases h3
            | noStep _ _ hno =>
              exact False.elim (hno ⟨StepResult.choice (fun s' => s' = X86MultiState.mk 1 true (x + 1) (x + 1)), rfl⟩)
        | choice _ _ _ _ _ _ h2 _ _ => dsimp [x86MultiStep] at h2; cases h2
        | emptyChoice _ _ _ h2 _ => dsimp [x86MultiStep] at h2; cases h2
        | terminated _ _ _ h2 => dsimp [x86MultiStep] at h2; cases h2
        | failed _ _ h2 => dsimp [x86MultiStep] at h2; cases h2
        | noStep _ _ hno =>
          exact False.elim (hno ⟨StepResult.step 1 (X86MultiState.mk 1 false (x + 1) (x + 1)), rfl⟩)
    | emptyChoice _ _ _ h1 hempty =>
      dsimp [x86MultiStep] at h1
      injection h1 with hpred1
      rw [hpred1] at hempty
      exact False.elim (hempty ⟨X86MultiState.mk 0 true x (x + 1), rfl⟩)
    | terminated _ _ _ h1 => dsimp [x86MultiStep] at h1; cases h1
    | failed _ _ h1 => dsimp [x86MultiStep] at h1; cases h1
    | noStep _ _ hno =>
      exact False.elim (hno ⟨StepResult.choice (fun s' => s' = X86MultiState.mk 0 true x (x + 1)), rfl⟩)

/-- Universal multi-step compilation theorem (`MirMultiLang → X86MultiLang`):
    every `p : MirMultiProg` compiles to `compileMirToX86 p` under the
    admissible $1 \to 2$ step-scaling coupling `mirToX86Coupling`. -/
theorem compileMirToX86_compiles (p : MirMultiProg) :
    Compiles MirMultiLang X86MultiLang mirToX86Coupling.toMorphism
      p (compileMirToX86 p) := by
  cases p with
  | incAndRet =>
    intro q _
    refine ⟨?_, ?_⟩
    · intro _ tr out hr
      exact x86IncAndRet_always_safe q.steps q.init tr out hr
    · intro out ⟨hinit, hr⟩
      cases q with
      | mk s n₂ =>
        cases s with
        | mk pc phase arg rax =>
          have hpc : pc = 0 := hinit.1
          have hph : phase = false := hinit.2.1
          have hrax : rax = 0 := hinit.2.2
          subst hpc hph hrax
          refine ⟨div2 n₂, Or.inl rfl, rfl, ?_⟩
          rw [decompileOut_mirToX86]
          exact x86IncAndRet_simulates_at_div2 n₂ arg out.trace out.outcome hr
  | failNow =>
    intro q hdef
    cases q with
    | mk s n₂ =>
      cases n₂ with
      | zero =>
        refine ⟨?_, ?_⟩
        · intro _ _ _ hr
          cases hr with
          | zero => exact True.intro
        · intro out ⟨hinit, hr⟩
          cases out with
          | mk tr outc =>
            cases hr with
            | zero =>
              refine ⟨0, Or.inl rfl, hinit.1, ?_⟩
              rw [decompileOut_mirToX86]
              exact ReachesPrefix.zero (decompileMirState s)
      | succ k =>
        cases ceil2_succ_exists k with
        | intro m hm =>
          have hdefCeil := hdef (ceil2 (k + 1)) (Or.inr rfl)
          rw [hm] at hdefCeil
          refine ⟨?_, ?_⟩
          · intro hinit _ _ _
            have hfailMir : ReachesPrefix mirMultiStep .failNow (m + 1)
                (decompileMirState s) [] .failed :=
              ReachesPrefix.failed m (decompileMirState s) rfl
            exact False.elim (hdefCeil hinit.1 [] .failed hfailMir)
          · intro _ ⟨hinit, _⟩
            have hfailMir : ReachesPrefix mirMultiStep .failNow (m + 1)
                (decompileMirState s) [] .failed :=
              ReachesPrefix.failed m (decompileMirState s) rfl
            exact False.elim (hdefCeil hinit.1 [] .failed hfailMir)

/-- Why a single-valued floor pullback `n₁ = div2 n₂` alone fails: at `n₂ = 1`,
    `div2 1 = 0` maps the first target step of `.failNow` to source step `0`
    (which is trivially defined), so `.failNow` fails to compile to `.failNow`. -/
theorem not_compiles_floor_only_failNow :
    ¬ Compiles MirMultiLang X86MultiLang
        (pullbackMorphism
          (fun q : ExecQuery X86MultiState => ⟨decompileMirState q.init, div2 q.steps⟩) id)
        .failNow .failNow := by
  intro hcomp
  let s₀ : X86MultiState := X86MultiState.mk 0 false 0 0
  have hdef0 : (MirMultiLang.sem .failNow ⟨decompileMirState s₀, div2 1⟩).defined := by
    intro _ _ _ hr
    cases hr with
    | zero => exact True.intro
  cases hcomp ⟨s₀, 1⟩ hdef0 with
  | intro hdefX86 _ =>
    have hfailX86 : ReachesPrefix x86MultiStep .failNow 1 s₀ [] .failed :=
      ReachesPrefix.failed 0 s₀ rfl
    exact hdefX86 ⟨rfl, rfl, rfl⟩ [] .failed hfailX86

/-- Why a single-valued ceiling pullback `n₁ = ceil2 n₂` alone fails: at `n₂ = 1`,
    `ceil2 1 = 1` demands that the first micro-step of `.incAndRet` (which is still
    in `phase = false` with `trace = []`) match a completed 1-step MIR prefix
    (which has `trace = [1]`). -/
theorem not_compiles_ceil_only_incAndRet :
    ¬ Compiles MirMultiLang X86MultiLang
        (pullbackMorphism
          (fun q : ExecQuery X86MultiState => ⟨decompileMirState q.init, ceil2 q.steps⟩) id)
        .incAndRet .incAndRet := by
  intro hcomp
  let s₀ : X86MultiState := X86MultiState.mk 0 false 0 0
  have hdefMir1 : (MirMultiLang.sem .incAndRet ⟨decompileMirState s₀, 1⟩).defined := by
    intro _ _ _ hr
    cases hr with
    | step _ _ s' _ _ _ h1 hr2 =>
      dsimp [mirMultiStep, decompileMirState, s₀] at h1
      injection h1 with _ hs'
      subst hs'
      cases hr2 with
      | zero => exact True.intro
    | choice _ _ _ _ _ _ h1 _ _ => dsimp [mirMultiStep, decompileMirState, s₀] at h1; cases h1
    | emptyChoice _ _ _ h1 _ => dsimp [mirMultiStep, decompileMirState, s₀] at h1; cases h1
    | terminated _ _ _ _ => exact True.intro
    | failed _ _ h1 => dsimp [mirMultiStep, decompileMirState, s₀] at h1; cases h1
    | noStep _ _ hno =>
      exact False.elim (hno ⟨StepResult.step 1 (MirMultiState.mk 1 1), rfl⟩)
  cases hcomp ⟨s₀, 1⟩ hdefMir1 with
  | intro _ hval =>
    have hrX86 : ReachesPrefix x86MultiStep .incAndRet 1 s₀ [] .running :=
      ReachesPrefix.choice 0 s₀ (X86MultiState.mk 0 true 0 1)
        (fun s' => s' = X86MultiState.mk 0 true 0 1) [] .running rfl rfl
        (ReachesPrefix.zero (X86MultiState.mk 0 true 0 1))
    have hMirOut := hval ⟨[], .running⟩ ⟨⟨rfl, rfl, rfl⟩, hrX86⟩
    have hrMir : ReachesPrefix mirMultiStep .incAndRet 1 (MirMultiState.mk 0 0) [] .running := hMirOut.2
    cases hrMir with
    | choice _ _ _ _ _ _ h1 _ _ => dsimp [mirMultiStep] at h1; cases h1

/-!
### Subsection 6.2: Upward Borrow-Erasure Abstraction (`FuncLang → MirMultiLang`) and End-to-End Composition

We now define a high-level functional model `FuncLang` whose states are pure
mathematical pairs `(done : Bool, acc : Nat)` without program counters or
mutable local slots, prove `Abstracts FuncLang MirMultiLang` for `.incAndRet`,
and compose the upward abstraction (`FuncLang → MirMultiLang`) with the
multi-step lowering (`MirMultiLang → X86MultiLang`) via
`AdmissibleExecCoupling.comp` and `verify_through_passes_anchored`.
-/

inductive FuncProg where
  | incSpec

structure FuncState where
  done : Bool
  acc : Nat

def funcStep (p : FuncProg) (s : FuncState)
    (r : StepResult FuncState Nat Nat) : Prop :=
  match p, s with
  | .incSpec, ⟨false, x⟩ => r = .step 1 ⟨true, x + 1⟩
  | .incSpec, ⟨true, x⟩ => r = .terminated (.normal x)

def FuncMachine : SmallStepMachine FuncProg FuncState Nat Nat where
  initState _ s := s.done = false
  step := funcStep

abbrev FuncLang : Language := FuncMachine.toLanguage

def decompileFuncState (s : MirMultiState) : FuncState :=
  ⟨s.pc != 0, s.arg⟩

/-- Upward abstraction coupling `funcToMirCoupling` (`FuncLang → MirMultiLang`). -/
def funcToMirCoupling :
    ExecSimCoupling FuncState Nat Nat MirMultiState Nat Nat where
  decompileInit := decompileFuncState
  stepCoupling := fun n₂ n₁ => n₁ = n₂
  decompileTrace := fun tr => tr
  decompileVal := fun v => v

theorem admissible_funcToMirCoupling :
    AdmissibleExecCoupling funcToMirCoupling where
  step_nonempty := fun n₂ => ⟨n₂, rfl⟩
  step_coverage := fun n₁ => ⟨n₁, rfl, fun _ h => h⟩
  trace_injective := fun _ _ h => h
  val_injective := fun _ _ h => h

theorem decompileOut_funcToMir (out : ExecOut Nat Nat) :
    funcToMirCoupling.decompileOut out = out := by
  cases out with
  | mk trace outcome =>
    dsimp [ExecSimCoupling.decompileOut, funcToMirCoupling]
    rw [PrefixOutcome.map_id]

/-- Backward simulation from `MirMultiMachine` on `.incAndRet` to `FuncMachine`
    on `.incSpec`. -/
theorem mirIncAndRet_simulates_func (n x : Nat) (tr : List Nat)
    (out : PrefixOutcome Nat)
    (hr : ReachesPrefix mirMultiStep .incAndRet n (MirMultiState.mk 0 x) tr out) :
    ReachesPrefix funcStep .incSpec n (FuncState.mk false x) tr out := by
  cases n with
  | zero =>
    cases hr with
    | zero => exact ReachesPrefix.zero (FuncState.mk false x)
  | succ k =>
    cases hr with
    | step _ _ s1 obs tr' _ h1 hr1 =>
      dsimp [mirMultiStep] at h1
      injection h1 with hobs hs1
      subst hobs hs1
      cases k with
      | zero =>
        cases hr1 with
        | zero =>
          exact ReachesPrefix.step 0 (FuncState.mk false x) (FuncState.mk true (x + 1))
            1 [] .running rfl (ReachesPrefix.zero (FuncState.mk true (x + 1)))
      | succ m =>
        cases hr1 with
        | step _ _ _ _ _ _ h2 _ => dsimp [mirMultiStep] at h2; cases h2
        | choice _ _ _ _ _ _ h2 _ _ => dsimp [mirMultiStep] at h2; cases h2
        | emptyChoice _ _ _ h2 _ => dsimp [mirMultiStep] at h2; cases h2
        | terminated _ _ res h2 =>
          dsimp [mirMultiStep] at h2
          injection h2 with hres
          subst hres
          exact ReachesPrefix.step (m + 1) (FuncState.mk false x) (FuncState.mk true (x + 1))
            1 [] (.terminated (.normal (x + 1))) rfl
            (ReachesPrefix.terminated m (FuncState.mk true (x + 1)) (.normal (x + 1)) rfl)
        | failed _ _ h2 => dsimp [mirMultiStep] at h2; cases h2
        | noStep _ _ hno =>
          exact False.elim (hno ⟨StepResult.terminated (.normal (x + 1)), rfl⟩)
    | choice _ _ _ _ _ _ h1 _ _ => dsimp [mirMultiStep] at h1; cases h1
    | emptyChoice _ _ _ h1 _ => dsimp [mirMultiStep] at h1; cases h1
    | terminated _ _ _ h1 => dsimp [mirMultiStep] at h1; cases h1
    | failed _ _ h1 => dsimp [mirMultiStep] at h1; cases h1
    | noStep _ _ hno =>
      exact False.elim (hno ⟨StepResult.step 1 (MirMultiState.mk 1 (x + 1)), rfl⟩)

theorem funcIncSpec_always_safe (n x : Nat) (tr : List Nat) (out : PrefixOutcome Nat)
    (hr : ReachesPrefix funcStep .incSpec n (FuncState.mk false x) tr out) :
    out.isSafe ∧
      ((∀ v, out = .terminated (.normal v) → tr = [1] ∧ v = x + 1) ∧
        out ≠ .terminated .unwind) := by
  cases n with
  | zero =>
    cases hr with
    | zero =>
      refine ⟨True.intro, ?_, ?_⟩
      · intro _ h; cases h
      · intro h; cases h
  | succ k =>
    cases hr with
    | step _ _ s1 obs _ _ h1 hr1 =>
      dsimp [funcStep] at h1
      injection h1 with hobs hs1
      subst hobs hs1
      cases k with
      | zero =>
        cases hr1 with
        | zero =>
          refine ⟨True.intro, ?_, ?_⟩
          · intro _ h; cases h
          · intro h; cases h
      | succ m =>
        cases hr1 with
        | step _ _ _ _ _ _ h2 _ => dsimp [funcStep] at h2; cases h2
        | choice _ _ _ _ _ _ h2 _ _ => dsimp [funcStep] at h2; cases h2
        | emptyChoice _ _ _ h2 _ => dsimp [funcStep] at h2; cases h2
        | terminated _ _ res h2 =>
          dsimp [funcStep] at h2
          injection h2 with hres
          subst hres
          refine ⟨True.intro, ?_, ?_⟩
          · intro v hv
            injection hv with hres'
            injection hres' with hv'
            exact ⟨rfl, hv'.symm⟩
          · intro h; cases h
        | failed _ _ h2 => dsimp [funcStep] at h2; cases h2
        | noStep _ _ hno =>
          exact False.elim (hno ⟨StepResult.terminated (.normal (x + 1)), rfl⟩)
    | choice _ _ _ _ _ _ h1 _ _ => dsimp [funcStep] at h1; cases h1
    | emptyChoice _ _ _ h1 _ => dsimp [funcStep] at h1; cases h1
    | terminated _ _ _ h1 => dsimp [funcStep] at h1; cases h1
    | failed _ _ h1 => dsimp [funcStep] at h1; cases h1
    | noStep _ _ hno =>
      exact False.elim (hno ⟨StepResult.step 1 (FuncState.mk true (x + 1)), rfl⟩)

/-- `FuncProg.incSpec` upward-abstracts `MirMultiProg.incAndRet` under
    `funcToMirCoupling`. -/
theorem funcIncSpec_abstracts_mirIncAndRet :
    Abstracts FuncLang MirMultiLang funcToMirCoupling.toMorphism
      .incSpec .incAndRet := by
  intro q _
  cases q with
  | mk s n =>
    cases s with
    | mk pc arg =>
      refine ⟨?_, ?_⟩
      · intro hinit tr out hr
        dsimp [MirMultiMachine] at hinit
        subst hinit
        exact (funcIncSpec_always_safe n arg tr out
          (mirIncAndRet_simulates_func n arg tr out hr)).1
      · intro out ⟨hinit, hr⟩
        dsimp [MirMultiMachine] at hinit
        subst hinit
        refine ⟨n, rfl, rfl, ?_⟩
        rw [decompileOut_funcToMir]
        exact mirIncAndRet_simulates_func n arg out.trace out.outcome hr

def funcSpecIncOne : FuncLang.Behavior :=
  FuncLang.Spec (fun q out =>
    (∀ v, out.outcome = .terminated (.normal v) → out.trace = [1] ∧ v = q.init.acc + 1) ∧
    out.outcome ≠ .terminated .unwind)

def x86SpecIncOne : X86MultiLang.Behavior :=
  X86MultiLang.Spec (fun q out =>
    (∀ v, out.outcome = .terminated (.normal v) → out.trace = [1] ∧ v = q.init.arg + 1) ∧
    out.outcome ≠ .terminated .unwind)

theorem funcIncSpec_satisfies_funcSpecIncOne :
    FuncLang.sem .incSpec ≤ funcSpecIncOne := by
  intro q _
  cases q with
  | mk s n =>
    cases s with
    | mk done acc =>
      refine ⟨?_, ?_⟩
      · intro hinit tr out hr
        dsimp [FuncMachine] at hinit
        subst hinit
        exact (funcIncSpec_always_safe n acc tr out hr).1
      · intro out ⟨hinit, hr⟩
        dsimp [FuncMachine] at hinit
        subst hinit
        exact (funcIncSpec_always_safe n acc out.trace out.outcome hr).2

/-- End-to-end composed coupling (`funcToMirCoupling.comp mirToX86Coupling`) is
    admissible (`AdmissibleExecCoupling`), and the target anchor
    `mirToX86Coupling.toMorphism (funcToMirCoupling.toMorphism funcSpecIncOne) ≤ x86SpecIncOne`
    discharges the full two-stage verification pipeline (`FuncLang → MirMultiLang → X86MultiLang`)
    via `verify_through_passes_anchored`. -/
theorem endToEnd_func_mir_x86_verified :
    AdmissibleExecCoupling (funcToMirCoupling.comp mirToX86Coupling) ∧
    X86MultiLang.sem (compileMirToX86 .incAndRet) ≤ x86SpecIncOne := by
  refine ⟨AdmissibleExecCoupling.comp admissible_funcToMirCoupling admissible_mirToX86Coupling, ?_⟩
  let C_mir_x86 : Compiler MirMultiLang X86MultiLang :=
    { compile := compileMirToX86
      π := mirToX86Coupling.toMorphism }
  have hAnchor :
      C_mir_x86.π (funcToMirCoupling.toMorphism funcSpecIncOne) ≤ x86SpecIncOne := by
    intro q _
    refine ⟨fun _ _ _ _ => True.intro, ?_⟩
    intro out ⟨_, _, _, _, hPost⟩
    rw [decompileOut_mirToX86, decompileOut_funcToMir] at hPost
    exact hPost
  exact (verify_through_passes_anchored
    (C := C_mir_x86)
    (π_v := funcToMirCoupling.toMorphism)
    funcIncSpec_satisfies_funcSpecIncOne
    funcIncSpec_abstracts_mirIncAndRet
    funcToMirCoupling.monotone_toMorphism
    ⟨mirToX86Coupling.monotone_toMorphism, compileMirToX86_compiles .incAndRet⟩
    hAnchor).2

/-!
### Subsection 6.3: `BehaviorCodec` — Bi-Directional Query/Outcome Retraction-Section Codec

In `.agent-worktrees/mir-to-x86/theory/Anneal/Compiler/NaiveCodegen.lean`
(lines 40–145), `π_stage0` is constructed from data-level `compileState`/
`decompileInitState` and `compileVal`/`decompileVal` functions satisfying the
round-trip equations `decompileVal (compileVal v) = v` and
`compileState (decompileInitState s) = s` on valid initial states.

Abstracting this pattern to arbitrary languages `L₁, L₂ : Language` yields
`BehaviorCodec L₁ L₂`:
1. A query retraction pair `(encodeQuery, decodeQuery)` with
   `decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁`. This makes
   `decodeQuery` surjective onto `L₁.Query` (ruling out Class (c) `steps := 0`
   and bounded-fuel truncation while allowing `L₂.Query` to carry extra concrete
   target state such as scratch registers), and
2. An outcome section-retraction pair `(decodeOut, encodeOut)` with
   `encode_decode_out : ∀ o₂, encodeOut (decodeOut o₂) = o₂`. This makes
   `decodeOut` injective on `L₂.Out` (ruling out Class (d) trace/value/outcome
   collapse), while `pullbackMorphism decodeQuery decodeOut` preserves
   `.defined` bi-directionally (ruling out Class (a)) and preserves outcome
   predicates without erasure (ruling out Class (b)).

When specialized to small-step machines (`SmallStepCodec`), every codec embeds
canonically into `AdmissibleExecCoupling` (`SmallStepCodec.admissible_toExecSimCoupling`).
-/

/-- A bi-directional query/outcome codec between `L₁` and `L₂` inducing a
    non-degenerate pullback morphism `toMorphism : L₁.Behavior → L₂.Behavior`. -/
structure BehaviorCodec (L₁ L₂ : Language) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁ : L₁.Query, decodeQuery (encodeQuery q₁) = q₁
  decodeOut : L₂.Out → L₁.Out
  encodeOut : L₁.Out → L₂.Out
  encode_decode_out : ∀ o₂ : L₂.Out, encodeOut (decodeOut o₂) = o₂

/-- Surjectivity of `decodeQuery` onto `L₁.Query` (rules out Class (c) query
    truncation). -/
theorem BehaviorCodec.decodeQuery_surjective {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) (q₁ : L₁.Query) :
    ∃ q₂ : L₂.Query, c.decodeQuery q₂ = q₁ :=
  ⟨c.encodeQuery q₁, c.decode_encode_query q₁⟩

/-- Injectivity of `decodeOut` on `L₂.Out` (rules out Class (d) outcome/trace/
    value conflation). -/
theorem BehaviorCodec.decodeOut_injective {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) {o₂ o₂' : L₂.Out}
    (h : c.decodeOut o₂ = c.decodeOut o₂') :
    o₂ = o₂' := by
  have h' := congrArg c.encodeOut h
  rw [c.encode_decode_out, c.encode_decode_out] at h'
  exact h'

/-- Induced behavior morphism `L₁.Behavior → L₂.Behavior` obtained by pulling
    back queries along `c.decodeQuery` and outcomes along `c.decodeOut`. -/
def BehaviorCodec.toMorphism {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) : L₁.Behavior → L₂.Behavior :=
  pullbackMorphism c.decodeQuery c.decodeOut

/-- `c.toMorphism` is automatically `Monotone`. -/
theorem BehaviorCodec.monotone_toMorphism {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) : Monotone c.toMorphism :=
  monotone_pullbackMorphism c.decodeQuery c.decodeOut

/-- `c.toMorphism` preserves `.defined` bi-directionally at every target query
    `q₂` (ruling out Class (a)). -/
theorem BehaviorCodec.toMorphism_defined_iff {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₂ : L₂.Query) :
    (c.toMorphism b q₂).defined ↔ (b (c.decodeQuery q₂)).defined :=
  Iff.rfl

/-- Evaluating `c.toMorphism b` at `c.encodeQuery q₁` recovers `(b q₁).defined`
    bi-directionally. -/
theorem BehaviorCodec.toMorphism_encodeQuery_defined_iff {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₁ : L₁.Query) :
    (c.toMorphism b (c.encodeQuery q₁)).defined ↔ (b q₁).defined := by
  dsimp [BehaviorCodec.toMorphism, pullbackMorphism, Partial.map]
  rw [c.decode_encode_query]

/-- Evaluating `c.toMorphism b` at `c.encodeQuery q₁` equals pulling back only
    the outcome of `b q₁` along `c.decodeOut`. -/
theorem BehaviorCodec.toMorphism_encodeQuery {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₁ : L₁.Query) :
    c.toMorphism b (c.encodeQuery q₁) =
      Partial.map (fun P o₂ => P (c.decodeOut o₂)) (b q₁) := by
  dsimp [BehaviorCodec.toMorphism, pullbackMorphism]
  rw [c.decode_encode_query]

/-- Evaluating `c.toMorphism b` at `c.encodeQuery q₁` recovers `(b q₁).val` on
    `c.decodeOut o₂` bi-directionally. -/
theorem BehaviorCodec.toMorphism_encodeQuery_val_iff {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₁ : L₁.Query)
    (h : (c.toMorphism b (c.encodeQuery q₁)).defined)
    (h₁ : (b q₁).defined) (o₂ : L₂.Out) :
    (c.toMorphism b (c.encodeQuery q₁)).val h o₂ ↔
      (b q₁).val h₁ (c.decodeOut o₂) := by
  revert h
  dsimp [BehaviorCodec.toMorphism, pullbackMorphism, Partial.map]
  rw [c.decode_encode_query]
  intro _
  exact Iff.rfl

/-- Identity `BehaviorCodec`. -/
def BehaviorCodec.id (L : Language) : BehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  decode_encode_query _ := rfl
  decodeOut o := o
  encodeOut o := o
  encode_decode_out _ := rfl

theorem BehaviorCodec.id_toMorphism (L : Language) (b : L.Behavior) :
    (BehaviorCodec.id L).toMorphism b = b :=
  rfl

/-- Composition of `BehaviorCodec`s across three languages `L₁ → L₂ → L₃`. -/
def BehaviorCodec.comp {L₁ L₂ L₃ : Language}
    (c₁₂ : BehaviorCodec L₁ L₂) (c₂₃ : BehaviorCodec L₂ L₃) :
    BehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂₃.encodeQuery (c₁₂.encodeQuery q₁)
  decodeQuery q₃ := c₁₂.decodeQuery (c₂₃.decodeQuery q₃)
  decode_encode_query q₁ := by
    rw [c₂₃.decode_encode_query, c₁₂.decode_encode_query]
  decodeOut o₃ := c₁₂.decodeOut (c₂₃.decodeOut o₃)
  encodeOut o₁ := c₂₃.encodeOut (c₁₂.encodeOut o₁)
  encode_decode_out o₃ := by
    rw [c₁₂.encode_decode_out, c₂₃.encode_decode_out]

/-- Strict definitional functoriality of `BehaviorCodec.toMorphism` under
    composition (`rfl`). -/
theorem BehaviorCodec.comp_toMorphism {L₁ L₂ L₃ : Language}
    (c₁₂ : BehaviorCodec L₁ L₂) (c₂₃ : BehaviorCodec L₂ L₃) (b : L₁.Behavior) :
    (c₁₂.comp c₂₃).toMorphism b = c₂₃.toMorphism (c₁₂.toMorphism b) :=
  rfl

/-- Bi-directional outcome preservation theorem: when `s` is defined and
    deterministic at `q₁` with unique outcome `o₁`, and `t` is total at
    `c.encodeQuery q₁`, `Compiles L₁ L₂ c.toMorphism s t` forces `t` to be
    defined at `c.encodeQuery q₁` and forces every target outcome `o₂` to satisfy
    `c.decodeOut o₂ = o₁` and `o₂ = c.encodeOut o₁`—bi-directionally preserving
    both termination and non-termination. -/
theorem BehaviorCodec.compiles_bidirectional_outcome {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) {s : L₁.Prog} {t : L₂.Prog}
    (hComp : Compiles L₁ L₂ c.toMorphism s t)
    (q₁ : L₁.Query) (o₁ : L₁.Out)
    (hDef₁ : (L₁.sem s q₁).defined)
    (hUnique₁ : ∀ o₁', (L₁.sem s q₁).val hDef₁ o₁' ↔ o₁' = o₁)
    (hTotal₂ : ∀ hDef₂ : (L₂.sem t (c.encodeQuery q₁)).defined,
      ∃ o₂, (L₂.sem t (c.encodeQuery q₁)).val hDef₂ o₂) :
    ∃ (hDef₂ : (L₂.sem t (c.encodeQuery q₁)).defined),
      (∃ o₂, (L₂.sem t (c.encodeQuery q₁)).val hDef₂ o₂ ∧
        c.decodeOut o₂ = o₁ ∧ o₂ = c.encodeOut o₁) ∧
      (∀ o₂, (L₂.sem t (c.encodeQuery q₁)).val hDef₂ o₂ →
        c.decodeOut o₂ = o₁ ∧ o₂ = c.encodeOut o₁) := by
  have hDefPull : (c.toMorphism (L₁.sem s) (c.encodeQuery q₁)).defined :=
    (c.toMorphism_encodeQuery_defined_iff (L₁.sem s) q₁).mpr hDef₁
  cases hComp (c.encodeQuery q₁) hDefPull with
  | intro hDef₂ hVal₂ =>
    refine ⟨hDef₂, ?_, ?_⟩
    · cases hTotal₂ hDef₂ with
      | intro o₂ ho₂ =>
        have hPullVal := hVal₂ o₂ ho₂
        have hSrcVal : (L₁.sem s q₁).val hDef₁ (c.decodeOut o₂) :=
          (c.toMorphism_encodeQuery_val_iff (L₁.sem s) q₁ hDefPull hDef₁ o₂).mp hPullVal
        have hDecEq : c.decodeOut o₂ = o₁ := (hUnique₁ (c.decodeOut o₂)).mp hSrcVal
        have hOutEq : o₂ = c.encodeOut o₁ := by
          rw [← hDecEq, c.encode_decode_out]
        exact ⟨o₂, ho₂, hDecEq, hOutEq⟩
    · intro o₂ ho₂
      have hPullVal := hVal₂ o₂ ho₂
      have hSrcVal : (L₁.sem s q₁).val hDef₁ (c.decodeOut o₂) :=
        (c.toMorphism_encodeQuery_val_iff (L₁.sem s) q₁ hDefPull hDef₁ o₂).mp hPullVal
      have hDecEq : c.decodeOut o₂ = o₁ := (hUnique₁ (c.decodeOut o₂)).mp hSrcVal
      have hOutEq : o₂ = c.encodeOut o₁ := by
        rw [← hDecEq, c.encode_decode_out]
      exact ⟨hDecEq, hOutEq⟩

/-- Small-step data codec modeling `NaiveCodegen.lean`'s `π_stage0` via
    state retraction and trace/value sections, bridging `BehaviorCodec` and
    `AdmissibleExecCoupling`. -/
structure SmallStepCodec (State₁ Obs₁ Val₁ State₂ Obs₂ Val₂ : Type) where
  encodeInit : State₁ → State₂
  decodeInit : State₂ → State₁
  decode_encode_init : ∀ s₁, decodeInit (encodeInit s₁) = s₁
  decodeTrace : List Obs₂ → List Obs₁
  encodeTrace : List Obs₁ → List Obs₂
  encode_decode_trace : ∀ tr₂, encodeTrace (decodeTrace tr₂) = tr₂
  decodeVal : Val₂ → Val₁
  encodeVal : Val₁ → Val₂
  encode_decode_val : ∀ v₂, encodeVal (decodeVal v₂) = v₂

/-- Every `SmallStepCodec` induces a `BehaviorCodec` between the induced
    languages of any two `SmallStepMachine`s over those state/observation/value
    types. -/
def SmallStepCodec.toBehaviorCodec
    {M₁ : SmallStepMachine Prog₁ State₁ Obs₁ Val₁}
    {M₂ : SmallStepMachine Prog₂ State₂ Obs₂ Val₂}
    (c : SmallStepCodec State₁ Obs₁ Val₁ State₂ Obs₂ Val₂) :
    BehaviorCodec M₁.toLanguage M₂.toLanguage where
  encodeQuery q₁ := ⟨c.encodeInit q₁.init, q₁.steps⟩
  decodeQuery q₂ := ⟨c.decodeInit q₂.init, q₂.steps⟩
  decode_encode_query q₁ := by
    cases q₁ with
    | mk init steps =>
      dsimp
      rw [c.decode_encode_init]
  decodeOut o₂ := ⟨c.decodeTrace o₂.trace, o₂.outcome.map c.decodeVal⟩
  encodeOut o₁ := ⟨c.encodeTrace o₁.trace, o₁.outcome.map c.encodeVal⟩
  encode_decode_out o₂ := by
    cases o₂ with
    | mk tr outc =>
      dsimp
      rw [c.encode_decode_trace, PrefixOutcome.map_comp]
      have hmap : outc.map (fun v => c.encodeVal (c.decodeVal v)) = outc := by
        cases outc with
        | running => rfl
        | terminated t =>
          cases t with
          | normal v =>
            dsimp [PrefixOutcome.map, TerminationKind.map]
            rw [c.encode_decode_val]
          | unwind => rfl
        | failed => rfl
        | stuck => rfl
      rw [hmap]

/-- Every `SmallStepCodec` embeds canonically into `ExecSimCoupling` and
    automatically satisfies `AdmissibleExecCoupling`. -/
def SmallStepCodec.toExecSimCoupling
    (c : SmallStepCodec State₁ Obs₁ Val₁ State₂ Obs₂ Val₂) :
    ExecSimCoupling State₁ Obs₁ Val₁ State₂ Obs₂ Val₂ where
  decompileInit := c.decodeInit
  stepCoupling n₂ n₁ := n₁ = n₂
  decompileTrace := c.decodeTrace
  decompileVal := c.decodeVal

theorem SmallStepCodec.admissible_toExecSimCoupling
    (c : SmallStepCodec State₁ Obs₁ Val₁ State₂ Obs₂ Val₂) :
    AdmissibleExecCoupling c.toExecSimCoupling where
  step_nonempty n₂ := ⟨n₂, rfl⟩
  step_coverage n₁ := ⟨n₁, rfl, fun _ h => h⟩
  trace_injective _ _ h := by
    have h' := congrArg c.encodeTrace h
    dsimp [SmallStepCodec.toExecSimCoupling] at h'
    rw [c.encode_decode_trace, c.encode_decode_trace] at h'
    exact h'
  val_injective _ _ h := by
    have h' := congrArg c.encodeVal h
    dsimp [SmallStepCodec.toExecSimCoupling] at h'
    rw [c.encode_decode_val, c.encode_decode_val] at h'
    exact h'

/-!
## Section 7: Kernel Axiom Audit (`#print axioms`)

Every theorem in this mechanization is constructively proved in the Lean 4
kernel (`v4.34.1`) with zero `sorryAx`, zero `Lean.ofReduceBool`, and zero
`Classical.choice`.
-/

#print axioms counterexample_class_a_masks_target_ub
#print axioms counterexample_class_b_erases_postconditions
#print axioms counterexample_class_c_stepZero_diverges_and_masks_ub
#print axioms counterexample_class_c_boundedFuel_masks_late_ub_and_divergence
#print axioms counterexample_class_d_erases_observations_and_values
#print axioms verify_through_passes_unanchored_vulnerable
#print axioms verify_through_passes_anchored
#print axioms target_anchor_rejects_degenerate_classes
#print axioms stepIndependent_target_anchor_blind_to_class_c
#print axioms admissible_rules_out_class_a_target_ub_and_stuck
#print axioms π_top_not_admissible
#print axioms π_chaosVal_not_admissible
#print axioms admissible_rules_out_class_c_late_ub_and_divergence
#print axioms admissible_rules_out_class_d_trace_and_val_erasure
#print axioms AdmissibleExecCoupling.id
#print axioms AdmissibleExecCoupling.comp
#print axioms AdmissibleCompilerMorphism.id
#print axioms AdmissibleCompilerMorphism.comp
#print axioms compileMirToX86_compiles
#print axioms not_compiles_floor_only_failNow
#print axioms not_compiles_ceil_only_incAndRet
#print axioms funcIncSpec_abstracts_mirIncAndRet
#print axioms endToEnd_func_mir_x86_verified
#print axioms BehaviorCodec.decodeQuery_surjective
#print axioms BehaviorCodec.decodeOut_injective
#print axioms BehaviorCodec.monotone_toMorphism
#print axioms BehaviorCodec.id_toMorphism
#print axioms BehaviorCodec.comp_toMorphism
#print axioms BehaviorCodec.compiles_bidirectional_outcome
#print axioms SmallStepCodec.admissible_toExecSimCoupling

end Anneal.MorphismAdmissibility
