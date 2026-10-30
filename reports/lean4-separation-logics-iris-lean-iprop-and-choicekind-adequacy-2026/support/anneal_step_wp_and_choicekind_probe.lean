-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Empirical Lean v4.34.1 Probe: Step-Indexed Separation Logic & `ChoiceKind`

This standalone, zero-dependency, zero-`sorry` Lean `v4.34.1` module mechanizes
the bridge between a step-indexed separation-logic weakest precondition (`wpAt`
and `wpDualAt`) and Anneal's Layer 1A (`Trusted.Refinement`) and Layer 1B
(`Trusted.StepResult`) semantics, together with the complete analysis and
two-stage resolution of `ChoiceKind.angelic`:

1. **Exact Layer 1A and Layer 1B Definitions:** Reproduces `Preorder`,
   `Partial`, `Behavior`, `Language`, `SpecOn`, `Spec`, `WellFormedOn`,
   `WellFormed`, `Compiles`, `Abstracts`, `Compiler`, `Compiler.Verified`,
   `SmallStepMachine`, `StepResult`, `PrefixOutcome`, `ReachesPrefix`, and
   `BehaviorOf`.
2. **Step-Indexed Separation Logic (`SProp Res`):** Defines a step-indexed
   bunched-implication (BI) assertion carrier over an abstract separation
   algebra `SepAlgebra Res` with separating conjunction (`∗`), magic wand
   (`-∗`), persistence (`□`), later (`▷`), and frame-preserving basic updates
   (`|==>`), together with the BI frame rule (`bupd_frame_r`).
3. **Small-Step Weakest Precondition (`wpAt`) and All-Prefix Adequacy:** Defines
   `wpAt` over `SmallStepMachine` with state and trace-history interpretation
   `stateInterp`, proves `wpAt_mono` and `wpAt_frame_r`, and proves
   `wp_adequacy_reachesPrefix`, `wp_adequacy_specOn`,
   `wp_adequacy_wellFormedOn`, `wp_adequacy_wellFormed`, and
   `wp_adequacy_compiler_verified`.
4. **Complete Audit and Resolution of `ChoiceKind.angelic` (Options A, B, C):**
   - **Option B Semantic Trap (`angelic_choice_phantom_in_reachesPrefix` and
     `optionB_angelic_trap_is_ub`):** Proves that `ReachesPrefix.choice` and
     `BehaviorOf.defined` treat `ChoiceKind.angelic` universally rather than
     existentially, so any `.angelic` choice node with even one failing branch
     collapses `(BehaviorOf M p q).defined` to `False`.
   - **Option A (`StepResultA` and `reachesPrefixA_iff_reachesPrefix`):**
     Removes the unused `ChoiceKind` parameter from `StepResult.choice` and
     proves exact equivalence with demonic-only `ReachesPrefix`.
   - **Option C (`GameHolds`, `GameBehaviorOf`, `ReachesWithStrategy`,
     `StrategyBehaviorOf`, `wpDualAt`, and `wpDual_adequacy_specOn`):**
     Mechanizes both the fuel-indexed two-player game semantics (`GameHolds` /
     `GameBehaviorOf`) and the Skolemized angelic-strategy trace relation
     (`ReachesWithStrategy` / `StrategyBehaviorOf`), and proves adequacy of
     `wpDualAt` (`wpDualAt_sound_for_safePrefixWithPost`,
     `wpDualAt_sound_for_gameHolds`, and `wpDual_adequacy_specOn`).
5. **Concrete Canary Instantiations:** Verifies an infinite reactive counter
   loop (`counterLoop_wellFormed`) and a 2-cell heap swap-and-add machine
   (`twoCell_spec`).
-/

namespace AnnealStepWPAdequacyProbe

/-!
## 1. Layer 1A (`Trusted.Refinement`) and Layer 1B (`Trusted.StepResult`)
-/

class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  AnnealStepWPAdequacyProbe.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

inductive ChoiceKind where
  | demonic
  | angelic

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive FailureKind where
  | ub
  | contractViolation

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State)
      (branches : State → Prop) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State)
      (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

/-!
## 2. Step-Indexed Separation Logic Carrier (`SProp Res`)
-/

/-- A separation algebra (partial commutative monoid with explicit disjointness
    relation) representing physical and ghost resources. -/
class SepAlgebra (Res : Type) where
  unit : Res
  disjoint : Res → Res → Prop
  op : Res → Res → Res
  disjoint_symm : ∀ {r₁ r₂}, disjoint r₁ r₂ → disjoint r₂ r₁
  disjoint_unit_l : ∀ r, disjoint unit r
  disjoint_unit_r : ∀ r, disjoint r unit
  op_comm : ∀ {r₁ r₂}, disjoint r₁ r₂ → op r₁ r₂ = op r₂ r₁
  op_unit_l : ∀ r, op unit r = r
  op_unit_r : ∀ r, op r unit = r
  disjoint_assoc_l : ∀ {r₁ r₂ r₃},
    disjoint r₁ r₂ → disjoint (op r₁ r₂) r₃ → disjoint r₂ r₃
  disjoint_assoc_r : ∀ {r₁ r₂ r₃},
    disjoint r₁ r₂ → disjoint (op r₁ r₂) r₃ → disjoint r₁ (op r₂ r₃)
  op_assoc : ∀ {r₁ r₂ r₃},
    disjoint r₁ r₂ → disjoint (op r₁ r₂) r₃ →
    op (op r₁ r₂) r₃ = op r₁ (op r₂ r₃)

namespace SProp

set_option linter.unusedSectionVars false

/-- Step-indexed resource predicates over `Res`. -/
abbrev SProp (Res : Type) := Nat → Res → Prop

variable {Res : Type} [SepAlgebra Res]

/-- Semantic entailment between step-indexed separation propositions. -/
def Entails (P Q : SProp Res) : Prop :=
  ∀ k r, P k r → Q k r

infix:25 " ⊢ " => Entails

theorem entails_refl (P : SProp Res) : P ⊢ P :=
  fun _ _ h => h

theorem entails_trans {P Q R : SProp Res} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun k r hp => h₂ k r (h₁ k r hp)

/-- Pure proposition embedding (affine: holds on any resource when `φ`
    holds). -/
def pure (φ : Prop) : SProp Res :=
  fun _ _ => φ

/-- Empirical empty resource assertion (`True`). -/
def emp : SProp Res :=
  fun _ _ => True

/-- Separating conjunction (`P ∗ Q`). -/
def sep (P Q : SProp Res) : SProp Res :=
  fun k r =>
    ∃ r₁ r₂,
      SepAlgebra.disjoint r₁ r₂ ∧
      r = SepAlgebra.op r₁ r₂ ∧
      P k r₁ ∧
      Q k r₂

infixr:35 " ∗ " => sep

/-- Separating implication / magic wand (`P -∗ Q`). -/
def wand (P Q : SProp Res) : SProp Res :=
  fun k r =>
    ∀ r', SepAlgebra.disjoint r r' → P k r' → Q k (SepAlgebra.op r r')

infixr:30 " -∗ " => wand

/-- Step-indexed later modality (`▷ P`). At step index `0`, `▷ P` holds
    trivially; at `k + 1`, it shifts the obligation to step index `k`. -/
def later (P : SProp Res) : SProp Res :=
  fun k r =>
    match k with
    | 0 => True
    | k' + 1 => P k' r

prefix:40 "▷ " => later

/-- Persistence modality (`□ P`): holds at the unit resource, duplicable across
    any disjoint resource split. -/
def persistently (P : SProp Res) : SProp Res :=
  fun k _ => P k SepAlgebra.unit

prefix:40 "□ " => persistently

/-- Frame-preserving basic update modality (`|==> P`): for any disjoint frame
    resource `r_f`, the resource `r` can be updated to some `r'` still disjoint
    from `r_f` such that `P k r'` holds. -/
def bupd (P : SProp Res) : SProp Res :=
  fun k r =>
    ∀ r_f, SepAlgebra.disjoint r r_f →
      ∃ r', SepAlgebra.disjoint r' r_f ∧ P k r'

prefix:38 "|==> " => bupd

theorem sep_comm {P Q : SProp Res} : (P ∗ Q) ⊢ (Q ∗ P) := by
  intro k r ⟨r₁, r₂, hdisj, hr, hp, hq⟩
  exact ⟨r₂, r₁, SepAlgebra.disjoint_symm hdisj,
    hr.trans (SepAlgebra.op_comm hdisj), hq, hp⟩

theorem sep_mono {P P' Q Q' : SProp Res} (hp : P ⊢ P') (hq : Q ⊢ Q') :
    (P ∗ Q) ⊢ (P' ∗ Q') := by
  intro k r ⟨r₁, r₂, hdisj, hr, h₁, h₂⟩
  exact ⟨r₁, r₂, hdisj, hr, hp k r₁ h₁, hq k r₂ h₂⟩

theorem wand_intro {P Q R : SProp Res} (h : (P ∗ Q) ⊢ R) : P ⊢ (Q -∗ R) := by
  intro k r hp r' hdisj hq
  exact h k (SepAlgebra.op r r') ⟨r, r', hdisj, rfl, hp, hq⟩

theorem wand_elim_l {P Q : SProp Res} : ((P -∗ Q) ∗ P) ⊢ Q := by
  intro k r ⟨r₁, r₂, hdisj, hr, hw, hp⟩
  rw [hr]
  exact hw r₂ hdisj hp

theorem later_mono {P Q : SProp Res} (h : P ⊢ Q) : (▷ P) ⊢ (▷ Q) := by
  intro k r hp
  cases k with
  | zero => trivial
  | succ k' => exact h k' r hp

theorem later_sep {P Q : SProp Res} : (▷ P ∗ ▷ Q) ⊢ ▷ (P ∗ Q) := by
  intro k r ⟨r₁, r₂, hdisj, hr, hp, hq⟩
  cases k with
  | zero => trivial
  | succ k' => exact ⟨r₁, r₂, hdisj, hr, hp, hq⟩

theorem bupd_intro {P : SProp Res} : P ⊢ |==> P := by
  intro k r hp r_f hdisj
  exact ⟨r, hdisj, hp⟩

theorem bupd_mono {P Q : SProp Res} (h : P ⊢ Q) : (|==> P) ⊢ (|==> Q) := by
  intro k r hup r_f hdisj
  rcases hup r_f hdisj with ⟨r', hdisj', hp⟩
  exact ⟨r', hdisj', h k r' hp⟩

theorem bupd_trans {P : SProp Res} : (|==> |==> P) ⊢ (|==> P) := by
  intro k r hup r_f hdisj
  rcases hup r_f hdisj with ⟨r', hdisj', hup'⟩
  exact hup' r_f hdisj'

/-- Frame rule for the basic update modality (`(|==> P) ∗ R ⊢ |==> (P ∗ R)`). -/
theorem bupd_frame_r {P R : SProp Res} : ((|==> P) ∗ R) ⊢ |==> (P ∗ R) := by
  intro k r ⟨r₁, r₂, hdisj₁₂, hr, hup, hr₂⟩ r_f hdisj_rf
  rw [hr] at hdisj_rf
  have hdisj₂f : SepAlgebra.disjoint r₂ r_f :=
    SepAlgebra.disjoint_assoc_l hdisj₁₂ hdisj_rf
  have hdisj₁_2f : SepAlgebra.disjoint r₁ (SepAlgebra.op r₂ r_f) :=
    SepAlgebra.disjoint_assoc_r hdisj₁₂ hdisj_rf
  rcases hup (SepAlgebra.op r₂ r_f) hdisj₁_2f with ⟨r₁', hdisj₁'_2f, hp⟩
  have hdisj_2f_1' : SepAlgebra.disjoint (SepAlgebra.op r₂ r_f) r₁' :=
    SepAlgebra.disjoint_symm hdisj₁'_2f
  have hdisj_f2 : SepAlgebra.disjoint r_f r₂ :=
    SepAlgebra.disjoint_symm hdisj₂f
  have hdisj_f2_1' : SepAlgebra.disjoint (SepAlgebra.op r_f r₂) r₁' := by
    rw [SepAlgebra.op_comm hdisj_f2]
    exact hdisj_2f_1'
  have hdisj_2_1' : SepAlgebra.disjoint r₂ r₁' :=
    SepAlgebra.disjoint_assoc_l hdisj_f2 hdisj_f2_1'
  have hdisj_1'_2 : SepAlgebra.disjoint r₁' r₂ :=
    SepAlgebra.disjoint_symm hdisj_2_1'
  have hdisj_f_21' : SepAlgebra.disjoint r_f (SepAlgebra.op r₂ r₁') :=
    SepAlgebra.disjoint_assoc_r hdisj_f2 hdisj_f2_1'
  have hdisj_1'2_f : SepAlgebra.disjoint (SepAlgebra.op r₁' r₂) r_f := by
    rw [SepAlgebra.op_comm hdisj_1'_2]
    exact SepAlgebra.disjoint_symm hdisj_f_21'
  exact ⟨SepAlgebra.op r₁' r₂, hdisj_1'2_f,
    ⟨r₁', r₂, hdisj_1'_2, rfl, hp, hr₂⟩⟩

/-- Soundness extraction for `|==> P` at the top level (using the unit
    frame). -/
theorem bupd_elim {P : SProp Res} {k : Nat} {r : Res}
    (h : (|==> P) k r) : ∃ r', P k r' := by
  rcases h SepAlgebra.unit (SepAlgebra.disjoint_unit_r r) with ⟨r', _, hp⟩
  exact ⟨r', hp⟩

end SProp

open SProp

/-!
## 3. Step-Indexed Weakest Precondition (`wpAt`) Over `SmallStepMachine`
-/

variable {Prog State Obs Val Res : Type} [SepAlgebra Res]

/-- Step-indexed weakest precondition over `SmallStepMachine Prog State Obs Val`
    for direct adequacy against `ReachesPrefix`. -/
def wpAt (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog) :
    Nat → State → List Obs →
      (List Obs → PrefixOutcome Val → SProp Res) → SProp Res
  | 0, s, hist, Φ =>
      stateInterp s hist -∗ |==> (stateInterp s hist ∗ Φ [] .running)
  | k + 1, s, hist, Φ =>
      stateInterp s hist -∗
        (SProp.pure (∃ r, M.step p s r) ∗
          fun idx r_own =>
            ∀ stepRes, M.step p s stepRes →
              match stepRes with
              | .step obs s' =>
                  (|==> ▷ (stateInterp s' (hist ++ [obs]) ∗
                    wpAt M stateInterp p k s' (hist ++ [obs])
                        (fun tr out => Φ (obs :: tr) out))) idx r_own
              | .choice _kind branches =>
                  (∃ s₀, branches s₀) ∧
                  ∀ s', branches s' →
                    (|==> ▷ (stateInterp s' hist ∗
                      wpAt M stateInterp p k s' hist Φ)) idx r_own
              | .terminated term =>
                  (|==> (stateInterp s hist ∗ Φ [] (.terminated term))) idx r_own
              | .failed _err =>
                  False)

/-- Consequence / monotonicity rule for `wpAt`. -/
theorem wpAt_mono (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res) (p : Prog) :
    ∀ (k : Nat) (s : State) (hist : List Obs)
      {Φ Ψ : List Obs → PrefixOutcome Val → SProp Res},
      (∀ tr out, Φ tr out ⊢ Ψ tr out) →
      wpAt M stateInterp p k s hist Φ ⊢ wpAt M stateInterp p k s hist Ψ := by
  intro k
  induction k with
  | zero =>
      intro s hist Φ Ψ hΦΨ idx r hwp r_s hdisj hs
      have hup := hwp r_s hdisj hs
      exact bupd_mono (sep_mono (entails_refl _) (hΦΨ [] .running))
        idx (SepAlgebra.op r r_s) hup
  | succ k ih =>
      intro s hist Φ Ψ hΦΨ idx r hwp r_s hdisj hs
      rcases hwp r_s hdisj hs with ⟨r₁, r₂, hdisj₁₂, hr, hprog, hstep⟩
      refine ⟨r₁, r₂, hdisj₁₂, hr, hprog, ?_⟩
      intro stepRes hm
      have hbranch := hstep stepRes hm
      cases stepRes with
      | step obs s' =>
          have ih' := ih s' (hist ++ [obs]) (fun tr out => hΦΨ (obs :: tr) out)
          exact bupd_mono (later_mono (sep_mono (entails_refl _) ih'))
            idx r₂ hbranch
      | choice kind branches =>
          rcases hbranch with ⟨hne, hbranches⟩
          refine ⟨hne, fun s' hbs => ?_⟩
          have ih' := ih s' hist hΦΨ
          exact bupd_mono (later_mono (sep_mono (entails_refl _) ih'))
            idx r₂ (hbranches s' hbs)
      | terminated term =>
          exact bupd_mono (sep_mono (entails_refl _) (hΦΨ [] (.terminated term)))
            idx r₂ hbranch
      | failed err =>
          exact False.elim hbranch

/-- Separation-logic frame rule for `wpAt`: framing a resource assertion `R`
    around `wpAt` preserves `R` into the postcondition across arbitrary steps,
    demonic choices, and termination. -/
theorem wpAt_frame_r (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res) (p : Prog) :
    ∀ (k : Nat) (s : State) (hist : List Obs)
      (Φ : List Obs → PrefixOutcome Val → SProp Res) (R : SProp Res),
      (∀ idx' r, R (idx' + 1) r → R idx' r) →
      (wpAt M stateInterp p k s hist Φ ∗ R) ⊢
        wpAt M stateInterp p k s hist (fun tr out => Φ tr out ∗ R) := by
  intro k
  induction k with
  | zero =>
      intro s hist Φ R _hR_down idx r
        ⟨r_wp, r_R, hdisj_wpR, hr, hwp, hR⟩ r_s hdisj_r_s hs
      subst hr
      have hdisj_R_wp : SepAlgebra.disjoint r_R r_wp :=
        SepAlgebra.disjoint_symm hdisj_wpR
      have hdisj_Rwp_s : SepAlgebra.disjoint (SepAlgebra.op r_R r_wp) r_s := by
        rw [SepAlgebra.op_comm hdisj_R_wp]
        exact hdisj_r_s
      have hdisj_wp_s : SepAlgebra.disjoint r_wp r_s :=
        SepAlgebra.disjoint_assoc_l hdisj_R_wp hdisj_Rwp_s
      have hdisj_R_wps : SepAlgebra.disjoint r_R (SepAlgebra.op r_wp r_s) :=
        SepAlgebra.disjoint_assoc_r hdisj_R_wp hdisj_Rwp_s
      have hdisj_wps_R : SepAlgebra.disjoint (SepAlgebra.op r_wp r_s) r_R :=
        SepAlgebra.disjoint_symm hdisj_R_wps
      have hup := hwp r_s hdisj_wp_s hs
      have hframed : ((|==> (stateInterp s hist ∗ Φ [] .running)) ∗ R)
          idx (SepAlgebra.op (SepAlgebra.op r_wp r_s) r_R) :=
        ⟨SepAlgebra.op r_wp r_s, r_R, hdisj_wps_R, rfl, hup, hR⟩
      have hup' := bupd_frame_r idx _ hframed
      have heq : SepAlgebra.op (SepAlgebra.op r_wp r_R) r_s =
          SepAlgebra.op (SepAlgebra.op r_wp r_s) r_R := by
        rw [SepAlgebra.op_comm hdisj_wpR]
        rw [SepAlgebra.op_assoc hdisj_R_wp hdisj_Rwp_s]
        exact SepAlgebra.op_comm hdisj_R_wps
      rw [heq]
      refine bupd_mono ?_ idx _ hup'
      intro idx' r'
        ⟨r₁₂, r₃, hdisj₁₂_3, hr', ⟨r₁, r₂, hdisj₁₂, hr₁₂, hs', hφ⟩, hR'⟩
      subst hr'
      subst hr₁₂
      have hdisj₂₃ : SepAlgebra.disjoint r₂ r₃ :=
        SepAlgebra.disjoint_assoc_l hdisj₁₂ hdisj₁₂_3
      have hdisj₁_23 : SepAlgebra.disjoint r₁ (SepAlgebra.op r₂ r₃) :=
        SepAlgebra.disjoint_assoc_r hdisj₁₂ hdisj₁₂_3
      exact ⟨r₁, SepAlgebra.op r₂ r₃, hdisj₁_23,
        SepAlgebra.op_assoc hdisj₁₂ hdisj₁₂_3, hs',
        ⟨r₂, r₃, hdisj₂₃, rfl, hφ, hR'⟩⟩
  | succ k ih =>
      intro s hist Φ R hR_down idx r
        ⟨r_wp, r_R, hdisj_wpR, hr, hwp, hR⟩ r_s hdisj_r_s hs
      subst hr
      have hdisj_R_wp : SepAlgebra.disjoint r_R r_wp :=
        SepAlgebra.disjoint_symm hdisj_wpR
      have hdisj_Rwp_s : SepAlgebra.disjoint (SepAlgebra.op r_R r_wp) r_s := by
        rw [SepAlgebra.op_comm hdisj_R_wp]
        exact hdisj_r_s
      have hdisj_wp_s : SepAlgebra.disjoint r_wp r_s :=
        SepAlgebra.disjoint_assoc_l hdisj_R_wp hdisj_Rwp_s
      have hdisj_R_wps : SepAlgebra.disjoint r_R (SepAlgebra.op r_wp r_s) :=
        SepAlgebra.disjoint_assoc_r hdisj_R_wp hdisj_Rwp_s
      have hdisj_wps_R : SepAlgebra.disjoint (SepAlgebra.op r_wp r_s) r_R :=
        SepAlgebra.disjoint_symm hdisj_R_wps
      rcases hwp r_s hdisj_wp_s hs with
        ⟨r₁, r₂, hdisj₁₂, hr_wps, hprog, hstep⟩
      rw [hr_wps] at hdisj_wps_R
      have hdisj₂_R : SepAlgebra.disjoint r₂ r_R :=
        SepAlgebra.disjoint_assoc_l hdisj₁₂ hdisj_wps_R
      have hdisj₁_2R : SepAlgebra.disjoint r₁ (SepAlgebra.op r₂ r_R) :=
        SepAlgebra.disjoint_assoc_r hdisj₁₂ hdisj_wps_R
      have heq : SepAlgebra.op (SepAlgebra.op r_wp r_R) r_s =
          SepAlgebra.op r₁ (SepAlgebra.op r₂ r_R) := by
        rw [SepAlgebra.op_comm hdisj_wpR]
        rw [SepAlgebra.op_assoc hdisj_R_wp hdisj_Rwp_s]
        rw [SepAlgebra.op_comm hdisj_R_wps]
        rw [hr_wps]
        exact SepAlgebra.op_assoc hdisj₁₂ hdisj_wps_R
      refine ⟨r₁, SepAlgebra.op r₂ r_R, hdisj₁_2R, heq, hprog, ?_⟩
      intro stepRes hm
      have hbranch := hstep stepRes hm
      cases stepRes with
      | step obs s' =>
          have hframed :
              ((|==> ▷ (stateInterp s' (hist ++ [obs]) ∗
                wpAt M stateInterp p k s' (hist ++ [obs])
                    (fun tr out => Φ (obs :: tr) out))) ∗ R)
              idx (SepAlgebra.op r₂ r_R) :=
            ⟨r₂, r_R, hdisj₂_R, rfl, hbranch, hR⟩
          have hup' := bupd_frame_r idx _ hframed
          refine bupd_mono ?_ idx _ hup'
          intro idx' r' ⟨r₁₂, r₃, hdisj₁₂_3, hr', hlat, hR'⟩
          cases idx' with
          | zero => trivial
          | succ idx'' =>
              rcases hlat with ⟨ra, rb, hdisj_ab, hr₁₂, hs', hwp'⟩
              subst hr'
              subst hr₁₂
              have hdisj_b3 : SepAlgebra.disjoint rb r₃ :=
                SepAlgebra.disjoint_assoc_l hdisj_ab hdisj₁₂_3
              have hdisj_a_b3 : SepAlgebra.disjoint ra (SepAlgebra.op rb r₃) :=
                SepAlgebra.disjoint_assoc_r hdisj_ab hdisj₁₂_3
              refine ⟨ra, SepAlgebra.op rb r₃, hdisj_a_b3,
                SepAlgebra.op_assoc hdisj_ab hdisj₁₂_3, hs', ?_⟩
              exact ih s' (hist ++ [obs])
                (fun tr out => Φ (obs :: tr) out) R hR_down
                idx'' (SepAlgebra.op rb r₃)
                ⟨rb, r₃, hdisj_b3, rfl, hwp', hR_down idx'' r₃ hR'⟩
      | choice kind branches =>
          rcases hbranch with ⟨hne, hbranches⟩
          refine ⟨hne, fun s' hbs => ?_⟩
          have hframed :
              ((|==> ▷ (stateInterp s' hist ∗
                wpAt M stateInterp p k s' hist Φ)) ∗ R)
              idx (SepAlgebra.op r₂ r_R) :=
            ⟨r₂, r_R, hdisj₂_R, rfl, hbranches s' hbs, hR⟩
          have hup' := bupd_frame_r idx _ hframed
          refine bupd_mono ?_ idx _ hup'
          intro idx' r' ⟨r₁₂, r₃, hdisj₁₂_3, hr', hlat, hR'⟩
          cases idx' with
          | zero => trivial
          | succ idx'' =>
              rcases hlat with ⟨ra, rb, hdisj_ab, hr₁₂, hs', hwp'⟩
              subst hr'
              subst hr₁₂
              have hdisj_b3 : SepAlgebra.disjoint rb r₃ :=
                SepAlgebra.disjoint_assoc_l hdisj_ab hdisj₁₂_3
              have hdisj_a_b3 : SepAlgebra.disjoint ra (SepAlgebra.op rb r₃) :=
                SepAlgebra.disjoint_assoc_r hdisj_ab hdisj₁₂_3
              refine ⟨ra, SepAlgebra.op rb r₃, hdisj_a_b3,
                SepAlgebra.op_assoc hdisj_ab hdisj₁₂_3, hs', ?_⟩
              exact ih s' hist Φ R hR_down idx'' (SepAlgebra.op rb r₃)
                ⟨rb, r₃, hdisj_b3, rfl, hwp', hR_down idx'' r₃ hR'⟩
      | terminated term =>
          have hframed :
              ((|==> (stateInterp s hist ∗ Φ [] (.terminated term))) ∗ R)
              idx (SepAlgebra.op r₂ r_R) :=
            ⟨r₂, r_R, hdisj₂_R, rfl, hbranch, hR⟩
          have hup' := bupd_frame_r idx _ hframed
          refine bupd_mono ?_ idx _ hup'
          intro idx' r'
            ⟨r₁₂, r₃, hdisj₁₂_3, hr',
             ⟨ra, rb, hdisj_ab, hr₁₂, hs', hφ⟩, hR'⟩
          subst hr'
          subst hr₁₂
          have hdisj_b3 : SepAlgebra.disjoint rb r₃ :=
            SepAlgebra.disjoint_assoc_l hdisj_ab hdisj₁₂_3
          have hdisj_a_b3 : SepAlgebra.disjoint ra (SepAlgebra.op rb r₃) :=
            SepAlgebra.disjoint_assoc_r hdisj_ab hdisj₁₂_3
          exact ⟨ra, SepAlgebra.op rb r₃, hdisj_a_b3,
            SepAlgebra.op_assoc hdisj_ab hdisj₁₂_3, hs',
            ⟨rb, r₃, hdisj_b3, rfl, hφ, hR'⟩⟩
      | failed err =>
          exact False.elim hbranch

/-!
## 4. All-Prefix Adequacy Theorems Connecting `wpAt` to `SpecOn`
-/

/-- Fundamental all-prefix adequacy lemma by induction on `ReachesPrefix`:
    if `stateInterp s hist ∗ wpAt M stateInterp p k s hist Φ` holds at step
    index `k` on some resource `r`, then for every trace `tr` and outcome `out`
    reachable via `ReachesPrefix M p init k s tr out`, `out.isSafe` holds and
    there exists a final index `idx_fin`, state `s_fin`, and resource `r'`
    satisfying `(stateInterp s_fin (hist ++ tr) ∗ Φ tr out) idx_fin r'`. -/
theorem wpAt_adequacy_aux
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog) (init : State) :
    ∀ {k : Nat} {s : State} {tr : List Obs} {out : PrefixOutcome Val},
      ReachesPrefix M p init k s tr out →
      ∀ (hist : List Obs)
        (Φ : List Obs → PrefixOutcome Val → SProp Res)
        (r : Res),
        (stateInterp s hist ∗ wpAt M stateInterp p k s hist Φ) k r →
        out.isSafe ∧
        ∃ idx_fin s_fin r',
          (stateInterp s_fin (hist ++ tr) ∗ Φ tr out) idx_fin r' := by
  intro k s tr out hreach
  induction hreach with
  | zero s =>
      intro hist Φ r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      have hup := hwp r_s (SepAlgebra.disjoint_symm hdisj) hs
      rcases bupd_elim hup with ⟨r', hpost⟩
      rw [List.append_nil]
      exact ⟨trivial, ⟨0, s, r', hpost⟩⟩
  | step k s s' obs tr' out' hm _hnext ih =>
      intro hist Φ r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, _hprog, hstep⟩
      have hup := hstep (.step obs s') hm
      rcases bupd_elim hup with ⟨r', hcomb⟩
      rcases ih (hist ++ [obs]) (fun tr out => Φ (obs :: tr) out) r' hcomb with
        ⟨hsafe, ⟨idx_fin, s_fin, r_fin, hfin⟩⟩
      rw [List.append_assoc, List.singleton_append] at hfin
      exact ⟨hsafe, ⟨idx_fin, s_fin, r_fin, hfin⟩⟩
  | choice k kind s s' branches tr' out' hm hbs _hnext ih =>
      intro hist Φ r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, _hprog, hstep⟩
      rcases hstep (.choice kind branches) hm with ⟨_hne, hbranches⟩
      have hup := hbranches s' hbs
      rcases bupd_elim hup with ⟨r', hcomb⟩
      exact ih hist Φ r' hcomb
  | emptyChoice k kind s branches hm hempty =>
      intro hist Φ r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, _hprog, hstep⟩
      rcases hstep (.choice kind branches) hm with ⟨hne, _⟩
      exact False.elim (hempty hne)
  | terminated k s term hm =>
      intro hist Φ r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, _hprog, hstep⟩
      have hup := hstep (.terminated term) hm
      rcases bupd_elim hup with ⟨r', hpost⟩
      rw [List.append_nil]
      exact ⟨trivial, ⟨k + 1, s, r', hpost⟩⟩
  | failed k s err hm =>
      intro hist Φ r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, _hprog, hstep⟩
      exact False.elim (hstep (.failed err) hm)
  | noStep k s hnostep =>
      intro hist Φ r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, hprog, _hstep⟩
      exact False.elim (hnostep hprog)

/-- All-prefix adequacy for `ReachesPrefix` starting from initial state `init`
    and empty history `[]`. -/
theorem wp_adequacy_reachesPrefix
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog) (init : State) (n : Nat)
    (post : List Obs → PrefixOutcome Val → Prop)
    (r₀ : Res)
    (hwp : (stateInterp init [] ∗
      wpAt M stateInterp p n init []
        (fun tr out => SProp.pure (post tr out))) n r₀) :
    ∀ tr out,
      ReachesPrefix M p init n init tr out →
      out.isSafe ∧ post tr out := by
  intro tr out hreach
  rcases wpAt_adequacy_aux M stateInterp p init hreach []
      (fun tr out => SProp.pure (post tr out)) r₀ hwp with
    ⟨hsafe, ⟨_idx_fin, _s_fin, _r', ⟨_r₁, _r₂, _hdisj, _hr, _hs, hpost⟩⟩⟩
  exact ⟨hsafe, hpost⟩

/-- Adequacy theorem connecting `wpAt` directly to Anneal's Layer 1A/1B
    `BehaviorOf M p ≤ (M.toLanguage).SpecOn pre post`. -/
theorem wp_adequacy_specOn
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog)
    (pre : ExecQuery State → Prop)
    (post : ExecQuery State → ExecOut Obs Val → Prop)
    (hwp : ∀ (q : ExecQuery State),
      pre q →
      M.initState p q.init →
      ∃ r₀ : Res,
        (stateInterp q.init [] ∗
          wpAt M stateInterp p q.steps q.init []
            (fun tr out => SProp.pure (post q ⟨tr, out⟩))) q.steps r₀) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre post := by
  intro q hpre
  refine ⟨?_, ?_⟩
  · intro hinit tr out hreach
    rcases hwp q hpre hinit with ⟨r₀, hq⟩
    exact (wp_adequacy_reachesPrefix M stateInterp p q.init q.steps
      (fun tr out => post q ⟨tr, out⟩) r₀ hq tr out hreach).1
  · intro out ⟨hinit, hreach⟩
    rcases hwp q hpre hinit with ⟨r₀, hq⟩
    exact (wp_adequacy_reachesPrefix M stateInterp p q.init q.steps
      (fun tr out => post q ⟨tr, out⟩) r₀ hq out.trace out.outcome hreach).2

/-- Unconditional specification adequacy
    (`BehaviorOf M p ≤ (M.toLanguage).Spec post`). -/
theorem wp_adequacy_spec
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog)
    (post : ExecQuery State → ExecOut Obs Val → Prop)
    (hwp : ∀ (q : ExecQuery State),
      M.initState p q.init →
      ∃ r₀ : Res,
        (stateInterp q.init [] ∗
          wpAt M stateInterp p q.steps q.init []
            (fun tr out => SProp.pure (post q ⟨tr, out⟩))) q.steps r₀) :
    BehaviorOf M p ≤ (M.toLanguage).Spec post :=
  wp_adequacy_specOn M stateInterp p (fun _ => True) post (fun q _ => hwp q)

/-- Conditional well-formedness / UB-freedom adequacy
    (`BehaviorOf M p ≤ (M.toLanguage).WellFormedOn pre`). -/
theorem wp_adequacy_wellFormedOn
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog)
    (pre : ExecQuery State → Prop)
    (hwp : ∀ (q : ExecQuery State),
      pre q →
      M.initState p q.init →
      ∃ r₀ : Res,
        (stateInterp q.init [] ∗
          wpAt M stateInterp p q.steps q.init []
            (fun _ _ => SProp.emp)) q.steps r₀) :
    BehaviorOf M p ≤ (M.toLanguage).WellFormedOn pre :=
  wp_adequacy_specOn M stateInterp p pre (fun _ _ => True) hwp

/-- Unconditional well-formedness / all-prefix UB-freedom adequacy
    (`BehaviorOf M p ≤ (M.toLanguage).WellFormed`). -/
theorem wp_adequacy_wellFormed
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog)
    (hwp : ∀ (q : ExecQuery State),
      M.initState p q.init →
      ∃ r₀ : Res,
        (stateInterp q.init [] ∗
          wpAt M stateInterp p q.steps q.init []
            (fun _ _ => SProp.emp)) q.steps r₀) :
    BehaviorOf M p ≤ (M.toLanguage).WellFormed :=
  wp_adequacy_wellFormedOn M stateInterp p (fun _ => True) (fun q _ => hwp q)

/-- End-to-end `Compiler.Verified` theorem combining `wp_adequacy_specOn` with
    `Compiler.SoundOn`. -/
theorem wp_adequacy_compiler_verified
    (M : SmallStepMachine Prog State Obs Val)
    {L_tgt : Language}
    (C : Compiler M.toLanguage L_tgt)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog)
    (pre : ExecQuery State → Prop)
    (post : ExecQuery State → ExecOut Obs Val → Prop)
    (hsound : C.SoundOn p)
    (hwp : ∀ (q : ExecQuery State),
      pre q →
      M.initState p q.init →
      ∃ r₀ : Res,
        (stateInterp q.init [] ∗
          wpAt M stateInterp p q.steps q.init []
            (fun tr out => SProp.pure (post q ⟨tr, out⟩))) q.steps r₀) :
    C.Verified p ((M.toLanguage).SpecOn pre post) := by
  have hspec : (M.toLanguage).sem p ≤ (M.toLanguage).SpecOn pre post :=
    wp_adequacy_specOn M stateInterp p pre post hwp
  exact ⟨hspec, hsound.2, Preorder.le_trans hsound.2 (hsound.1 hspec)⟩

/-!
## 5. Complete Audit and Resolution of `ChoiceKind.angelic` (Options A, B, C)

In `Trusted.StepResult`, `ReachesPrefix.choice` is parameterized by
`kind : ChoiceKind`, and `BehaviorOf.defined` universally quantifies over all
`ReachesPrefix` derivations:

```lean
defined :=
  M.initState p q.init →
    ∀ tr out, ReachesPrefix M p q.init q.steps q.init tr out → out.isSafe
```

Below we mechanize:
1. **Option B (Status Quo Trap):** `angelic_choice_phantom_in_reachesPrefix` and
   `optionB_angelic_trap_is_ub` prove that `ChoiceKind.angelic` is treated
   universally rather than existentially by `BehaviorOf.defined`.
2. **Option A (Removing `ChoiceKind`):** `StepResultA`, `SmallStepMachineA`,
   `ReachesPrefixA`, and `reachesPrefixA_iff_reachesPrefix` prove that removing
   `ChoiceKind` preserves exact equivalence with demonic `ReachesPrefix`.
3. **Option C (Two-Player Game and Strategy Semantics):** `wpDualAt`,
   `SafePrefixWithPost`, `GameHolds`, `GameBehaviorOf`, `ReachesWithStrategy`,
   `StrategyBehaviorOf`, `wpDualAt_sound_for_safePrefixWithPost`,
   `wpDualAt_sound_for_gameHolds`, and `wpDual_adequacy_specOn` provide two
   verified existential angelic semantics for future PNVI-ae-udi provenance
   prediction.
-/

/-- Counterexample 1 (`Bool` states): `ReachesPrefix` / `BehaviorOf.defined`
    treats `ChoiceKind.angelic` universally rather than existentially. -/
def angelicPhantomMachine : SmallStepMachine Unit Bool Unit Unit where
  initState _ s := s = true
  step _ s r :=
    match s with
    | true => r = .choice .angelic (fun _ => True)
    | false => r = .failed .ub

theorem angelic_choice_phantom_in_reachesPrefix :
    ReachesPrefix angelicPhantomMachine () true 2 true [] .running ∧
    ¬ (BehaviorOf angelicPhantomMachine () ⟨true, 2⟩).defined := by
  refine ⟨?_, ?_⟩
  · exact ReachesPrefix.choice 1 .angelic true true (fun _ => True) [] .running
      rfl trivial (ReachesPrefix.choice 0 .angelic true true (fun _ => True)
        [] .running rfl trivial (ReachesPrefix.zero true))
  · intro hdef
    have hub :
        ReachesPrefix angelicPhantomMachine () true 2 true [] (.failed .ub) :=
      ReachesPrefix.choice 1 .angelic true false (fun _ => True) [] (.failed .ub)
        rfl trivial (ReachesPrefix.failed 0 false .ub rfl)
    exact hdef rfl [] (.failed .ub) hub

/-- Counterexample 2 (`Nat` states `0, 1, 2`): state `0` steps via
    `.choice .angelic (fun s' => s' = 1 ∨ s' = 2)`, where branch `1` terminates
    normally via `.terminated (.normal ())` and branch `2` fails with
    `.failed .ub`. -/
def angelicTrapMachine : SmallStepMachine Unit Nat Unit Unit where
  initState _ s := s = 0
  step _ s r :=
    match s with
    | 0 => r = .choice .angelic (fun s' => s' = 1 ∨ s' = 2)
    | 1 => r = .terminated (.normal ())
    | _ => r = .failed .ub

/-- Under Option B (current `BehaviorOf`), `angelicTrapMachine` at `⟨0, 2⟩` is
    undefined (`defined = False`, i.e., `Partial.ub`) despite having the safe
    angelic branch `s' = 1`. -/
theorem optionB_angelic_trap_is_ub :
    ¬ (BehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined := by
  intro hdef
  have hinit : angelicTrapMachine.initState () 0 := rfl
  have hstep0 :
      angelicTrapMachine.step () 0
        (.choice .angelic (fun s' => s' = 1 ∨ s' = 2)) := rfl
  have hbranch2 : (fun s' => s' = 1 ∨ s' = 2) 2 := Or.inr rfl
  have hstep2 : angelicTrapMachine.step () 2 (.failed .ub) := rfl
  have hreach_bad :
      ReachesPrefix angelicTrapMachine () 0 2 0 [] (.failed .ub) :=
    ReachesPrefix.choice 1 .angelic 0 2 _ [] (.failed .ub)
      hstep0 hbranch2 (ReachesPrefix.failed 0 2 .ub hstep2)
  exact hdef hinit [] (.failed .ub) hreach_bad

/-!
### 5.1 Option A: Demonic-Only `StepResultA` (Removing `ChoiceKind`)
-/

/-- Option A `StepResultA`: removes `ChoiceKind` so `.choice` is unambiguously
    demonic (`branches : State → Prop`). -/
inductive StepResultA (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Option A `SmallStepMachineA`. -/
structure SmallStepMachineA (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResultA State Obs Val → Prop

/-- Option A `ReachesPrefixA`: identical to `ReachesPrefix` without the dead
    `kind : ChoiceKind` parameter on `.choice` and `.emptyChoice`. -/
inductive ReachesPrefixA (M : SmallStepMachineA Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefixA M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefixA M p init n s' tr out →
      ReachesPrefixA M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice branches) →
      branches s' →
      ReachesPrefixA M p init n s' tr out →
      ReachesPrefixA M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      M.step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefixA M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefixA M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefixA M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefixA M p init (n + 1) s [] .stuck

/-- Embedding an Option A machine into `SmallStepMachine` (mapping `.choice` to
    `.choice .demonic`). -/
def SmallStepMachineA.toTrusted (M : SmallStepMachineA Prog State Obs Val) :
    SmallStepMachine Prog State Obs Val where
  initState := M.initState
  step p s r :=
    match r with
    | .step obs s' => M.step p s (.step obs s')
    | .choice .demonic branches => M.step p s (.choice branches)
    | .choice .angelic _ => False
    | .terminated term => M.step p s (.terminated term)
    | .failed err => M.step p s (.failed err)

/-- Exact equivalence between `ReachesPrefixA` and `ReachesPrefix` on
    `M.toTrusted`. -/
theorem reachesPrefixA_iff_reachesPrefix
    (M : SmallStepMachineA Prog State Obs Val) (p : Prog) (init : State)
    (n : Nat) (s : State) (tr : List Obs) (out : PrefixOutcome Val) :
    ReachesPrefixA M p init n s tr out ↔
      ReachesPrefix M.toTrusted p init n s tr out := by
  constructor
  · intro h
    induction h with
    | zero s => exact .zero s
    | step n s s' obs tr out hstep _ ih =>
        exact .step n s s' obs tr out hstep ih
    | choice n s s' branches tr out hstep hbr _ ih =>
        exact .choice n .demonic s s' branches tr out hstep hbr ih
    | emptyChoice n s branches hstep hemp =>
        exact .emptyChoice n .demonic s branches hstep hemp
    | terminated n s term hstep => exact .terminated n s term hstep
    | failed n s err hstep => exact .failed n s err hstep
    | noStep n s hno =>
        refine .noStep n s (fun ⟨r, hr⟩ => hno ?_)
        cases r with
        | step obs s' => exact ⟨.step obs s', hr⟩
        | choice kind branches =>
            cases kind with
            | demonic => exact ⟨.choice branches, hr⟩
            | angelic => exact False.elim hr
        | terminated term => exact ⟨.terminated term, hr⟩
        | failed err => exact ⟨.failed err, hr⟩
  · intro h
    induction h with
    | zero s => exact .zero s
    | step n s s' obs tr out hstep _ ih =>
        exact .step n s s' obs tr out hstep ih
    | choice n kind s s' branches tr out hstep hbr _ ih =>
        cases kind with
        | demonic => exact .choice n s s' branches tr out hstep hbr ih
        | angelic => exact False.elim hstep
    | emptyChoice n kind s branches hstep hemp =>
        cases kind with
        | demonic => exact .emptyChoice n s branches hstep hemp
        | angelic => exact False.elim hstep
    | terminated n s term hstep => exact .terminated n s term hstep
    | failed n s err hstep => exact .failed n s err hstep
    | noStep n s hno =>
        refine .noStep n s (fun ⟨r, hr⟩ => hno ?_)
        cases r with
        | step obs s' => exact ⟨.step obs s', hr⟩
        | choice branches => exact ⟨.choice .demonic branches, hr⟩
        | terminated term => exact ⟨.terminated term, hr⟩
        | failed err => exact ⟨.failed err, hr⟩

/-!
### 5.2 Option C: Dual Weakest Precondition and Game / Strategy Semantics
-/

/-- Weakest precondition with **existential** angelic choice
    (`ChoiceKind.angelic`) and **universal + inhabited** demonic choice
    (`ChoiceKind.demonic`). -/
def wpDualAt (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog) :
    Nat → State → List Obs →
      (List Obs → PrefixOutcome Val → SProp Res) → SProp Res
  | 0, s, hist, Φ =>
      stateInterp s hist -∗ |==> (stateInterp s hist ∗ Φ [] .running)
  | k + 1, s, hist, Φ =>
      stateInterp s hist -∗
        (SProp.pure (∃ r, M.step p s r) ∗
          fun idx r_own =>
            ∀ stepRes, M.step p s stepRes →
              match stepRes with
              | .step obs s' =>
                  (|==> ▷ (stateInterp s' (hist ++ [obs]) ∗
                    wpDualAt M stateInterp p k s' (hist ++ [obs])
                        (fun tr out => Φ (obs :: tr) out))) idx r_own
              | .choice .demonic branches =>
                  (∃ s₀, branches s₀) ∧
                  ∀ s', branches s' →
                    (|==> ▷ (stateInterp s' hist ∗
                      wpDualAt M stateInterp p k s' hist Φ)) idx r_own
              | .choice .angelic branches =>
                  ∃ s', branches s' ∧
                    (|==> ▷ (stateInterp s' hist ∗
                      wpDualAt M stateInterp p k s' hist Φ)) idx r_own
              | .terminated term =>
                  (|==> (stateInterp s hist ∗ Φ [] (.terminated term))) idx r_own
              | .failed _err =>
                  False)

/-- Alternating step-indexed prefix semantics (`SafePrefixWithPost`) that gives
    `ChoiceKind.demonic` universal semantics and `ChoiceKind.angelic`
    existential semantics directly at the operational level. -/
def SafePrefixWithPost (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    Nat → State → (List Obs → PrefixOutcome Val → Prop) → Prop
  | 0, _s, post =>
      post [] .running
  | k + 1, s, post =>
      (∃ r, M.step p s r) ∧
      (∀ obs s', M.step p s (.step obs s') →
        SafePrefixWithPost M p k s' (fun tr out => post (obs :: tr) out)) ∧
      (∀ branches, M.step p s (.choice .demonic branches) →
        (∃ s₀, branches s₀) ∧
        ∀ s', branches s' → SafePrefixWithPost M p k s' post) ∧
      (∀ branches, M.step p s (.choice .angelic branches) →
        ∃ s', branches s' ∧ SafePrefixWithPost M p k s' post) ∧
      (∀ term, M.step p s (.terminated term) →
        post [] (.terminated term)) ∧
      (∀ err, ¬ M.step p s (.failed err))

/-- Dual adequacy theorem: `wpDualAt` (with universal demonic choice and
    existential angelic choice) is sound for `SafePrefixWithPost` at every
    step budget `k : Nat`. -/
theorem wpDualAt_sound_for_safePrefixWithPost
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog) :
    ∀ (k : Nat) (s : State) (hist : List Obs)
      (post : List Obs → PrefixOutcome Val → Prop) (r : Res),
      (stateInterp s hist ∗
        wpDualAt M stateInterp p k s hist
          (fun tr out => SProp.pure (post tr out))) k r →
      SafePrefixWithPost M p k s post := by
  intro k
  induction k with
  | zero =>
      intro s hist post r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      have hup := hwp r_s (SepAlgebra.disjoint_symm hdisj) hs
      rcases bupd_elim hup with ⟨_r', ⟨_ra, _rb, _hdisj_ab, _hr', _hs', hpost⟩⟩
      exact hpost
  | succ k ih =>
      intro s hist post r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, hprog, hstep⟩
      refine ⟨hprog, ?_, ?_, ?_, ?_, ?_⟩
      · intro obs s' hm
        have hup := hstep (.step obs s') hm
        rcases bupd_elim hup with ⟨r', hcomb⟩
        exact ih s' (hist ++ [obs]) (fun tr out => post (obs :: tr) out) r' hcomb
      · intro branches hm
        rcases hstep (.choice .demonic branches) hm with ⟨hne, hbranches⟩
        refine ⟨hne, fun s' hbs => ?_⟩
        rcases bupd_elim (hbranches s' hbs) with ⟨r', hcomb⟩
        exact ih s' hist post r' hcomb
      · intro branches hm
        rcases hstep (.choice .angelic branches) hm with ⟨s', hbs, hup⟩
        rcases bupd_elim hup with ⟨r', hcomb⟩
        exact ⟨s', hbs, ih s' hist post r' hcomb⟩
      · intro term hm
        rcases bupd_elim (hstep (.terminated term) hm) with
          ⟨_r', ⟨_ra, _rb, _hdisj_ab, _hr', _hs', hpost⟩⟩
        exact hpost
      · intro err hm
        exact hstep (.failed err) hm

/-- Option C (Formulation C1): Fuel-indexed two-player game / strategy
    satisfaction `GameHolds M p post fuel s hist`.
    - `.choice .demonic branches` is universal
      (`(∃ s0, branches s0) ∧ ∀ s', branches s' → ...`),
    - `.choice .angelic branches` is existential
      (`∃ s', branches s' ∧ ...`),
    - `.step` and `.terminated` require compatibility across enabled steps. -/
def GameHolds (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (post : List Obs → PrefixOutcome Val → Prop) :
    Nat → State → List Obs → Prop
  | 0, _, hist =>
      post hist .running
  | n + 1, s, hist =>
      (∃ r0, M.step p s r0) ∧
      ∀ r, M.step p s r →
        match r with
        | .step obs s' => GameHolds M p post n s' (hist ++ [obs])
        | .choice .demonic branches =>
            (∃ s0, branches s0) ∧ ∀ s', branches s' → GameHolds M p post n s' hist
        | .choice .angelic branches =>
            ∃ s', branches s' ∧ GameHolds M p post n s' hist
        | .terminated term => post hist (.terminated term)
        | .failed _ => False

/-- Monotonicity of `GameHolds` in its postcondition predicate `post`. -/
theorem GameHolds.mono {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {post₁ post₂ : List Obs → PrefixOutcome Val → Prop}
    (himp : ∀ tr out, post₁ tr out → post₂ tr out) :
    ∀ k s hist, GameHolds M p post₁ k s hist → GameHolds M p post₂ k s hist := by
  intro k
  induction k with
  | zero =>
      intro s hist h
      exact himp hist .running h
  | succ k ih =>
      intro s hist ⟨hprog, hstep⟩
      refine ⟨hprog, fun r hr => ?_⟩
      have hbr := hstep r hr
      cases r with
      | step obs s' => exact ih s' (hist ++ [obs]) hbr
      | choice kind branches =>
          cases kind with
          | demonic =>
              exact ⟨hbr.1, fun s' hbs => ih s' hist (hbr.2 s' hbs)⟩
          | angelic =>
              rcases hbr with ⟨s', hbs, hnext⟩
              exact ⟨s', hbs, ih s' hist hnext⟩
      | terminated term => exact himp hist (.terminated term) hbr
      | failed err => exact False.elim hbr

/-- Soundness of `wpDualAt` for `GameHolds`: if `wpDualAt` holds at step index
    `k`, then `GameHolds` holds for both `out.isSafe` and `post`. -/
theorem wpDualAt_sound_for_gameHolds
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog) :
    ∀ (k : Nat) (s : State) (hist : List Obs)
      (post : List Obs → PrefixOutcome Val → Prop) (r : Res),
      (stateInterp s hist ∗
        wpDualAt M stateInterp p k s hist
          (fun tr out => SProp.pure (post (hist ++ tr) out))) k r →
      GameHolds M p (fun tr out => out.isSafe ∧ post tr out) k s hist := by
  intro k
  induction k with
  | zero =>
      intro s hist post r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      have hup := hwp r_s (SepAlgebra.disjoint_symm hdisj) hs
      rcases bupd_elim hup with ⟨_r', ⟨_ra, _rb, _hdisj_ab, _hr', _hs', hpost⟩⟩
      rw [List.append_nil] at hpost
      exact ⟨trivial, hpost⟩
  | succ k ih =>
      intro s hist post r ⟨r_s, r_wp, hdisj, _hr, hs, hwp⟩
      rcases hwp r_s (SepAlgebra.disjoint_symm hdisj) hs with
        ⟨_r₁, _r₂, _hdisj₁₂, _hr₁₂, hprog, hstep⟩
      refine ⟨hprog, fun stepRes hm => ?_⟩
      have hbr := hstep stepRes hm
      cases stepRes with
      | step obs s' =>
          rcases bupd_elim hbr with ⟨r', hcomb⟩
          have hcomb' :
              (stateInterp s' (hist ++ [obs]) ∗
                wpDualAt M stateInterp p k s' (hist ++ [obs])
                  (fun tr out =>
                    SProp.pure (post ((hist ++ [obs]) ++ tr) out))) k r' := by
            simp only [List.append_assoc, List.singleton_append]
            exact hcomb
          exact ih s' (hist ++ [obs]) post r' hcomb'
      | choice kind branches =>
          cases kind with
          | demonic =>
              rcases hbr with ⟨hne, hbranches⟩
              refine ⟨hne, fun s' hbs => ?_⟩
              rcases bupd_elim (hbranches s' hbs) with ⟨r', hcomb⟩
              exact ih s' hist post r' hcomb
          | angelic =>
              rcases hbr with ⟨s', hbs, hup⟩
              rcases bupd_elim hup with ⟨r', hcomb⟩
              exact ⟨s', hbs, ih s' hist post r' hcomb⟩
      | terminated term =>
          rcases bupd_elim hbr with
            ⟨_r', ⟨_ra, _rb, _hdisj_ab, _hr', _hs', hpost⟩⟩
          rw [List.append_nil] at hpost
          exact ⟨trivial, hpost⟩
      | failed err =>
          exact False.elim hbr

/-- Induced partial behavior under Option C (`GameHolds`):
    - `defined`: from any valid initial state `q.init`, `GameHolds` holds for
      `out.isSafe` (requiring all demonic branches to be safe and at least one
      angelic branch to be safe).
    - `val`: the set of safe outcomes reachable along the machine's execution
      prefixes. -/
def GameBehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        GameHolds M p (fun _ out => out.isSafe) q.steps q.init []
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome ∧
      out.outcome.isSafe
  }

/-- Under Option C (`GameHolds`), `angelicTrapMachine` at query `⟨0, 2⟩` is
    safe and satisfies normal termination
    (`outcome = .terminated (.normal ())`), witnessed by the angelic choice
    `s' = 1`. -/
theorem optionC_angelic_trap_holds :
    GameHolds angelicTrapMachine ()
      (fun _ out => out.isSafe ∧ out = .terminated (.normal ())) 2 0 [] := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro r hr
  have hr' : r = .choice .angelic (fun s' => s' = 1 ∨ s' = 2) := hr
  subst hr'
  refine ⟨1, Or.inl rfl, ⟨_, rfl⟩, ?_⟩
  intro r1 hr1
  have hr1' : r1 = .terminated (.normal ()) := hr1
  subst hr1'
  exact ⟨trivial, rfl⟩

/-- Corollary: `GameBehaviorOf angelicTrapMachine () ⟨0, 2⟩` is `defined`
    (`True`), contrasting with `optionB_angelic_trap_is_ub`. -/
theorem optionC_angelic_trap_is_defined :
    (GameBehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined := by
  intro _
  exact GameHolds.mono (fun _ _ h => h.1) 2 0 [] optionC_angelic_trap_holds

/-- An angelic strategy (Skolem witness function) selecting the target state at
    each `.choice .angelic` transition as a function of remaining fuel and
    current state. -/
abbrev AngelicStrategy (State : Type) := Nat → State → State

/-- Option C (Formulation C2 — Skolemized Strategy-Tree Form): Inductive
    reachability parameterized by an angelic strategy
    `strat : AngelicStrategy State`.
    - `.choice .demonic` branches universally over all `s'` with `branches s'`.
    - `.choice .angelic` steps to the strategy's chosen witness `strat n s`
      (or `.stuck` if `¬ branches (strat n s)`). -/
inductive ReachesWithStrategy (M : SmallStepMachine Prog State Obs Val)
    (strat : AngelicStrategy State) (p : Prog) (init : State) :
    Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesWithStrategy M strat p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesWithStrategy M strat p init n s' tr out →
      ReachesWithStrategy M strat p init (n + 1) s (obs :: tr) out
  | demonicChoice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice .demonic branches) →
      branches s' →
      ReachesWithStrategy M strat p init n s' tr out →
      ReachesWithStrategy M strat p init (n + 1) s tr out
  | emptyDemonicChoice (n : Nat) (s : State) (branches : State → Prop) :
      M.step p s (.choice .demonic branches) →
      (¬ ∃ s', branches s') →
      ReachesWithStrategy M strat p init (n + 1) s [] .stuck
  | angelicChoice (n : Nat) (s : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice .angelic branches) →
      branches (strat n s) →
      ReachesWithStrategy M strat p init n (strat n s) tr out →
      ReachesWithStrategy M strat p init (n + 1) s tr out
  | invalidAngelicChoice (n : Nat) (s : State) (branches : State → Prop) :
      M.step p s (.choice .angelic branches) →
      ¬ branches (strat n s) →
      ReachesWithStrategy M strat p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesWithStrategy M strat p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesWithStrategy M strat p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesWithStrategy M strat p init (n + 1) s [] .stuck

/-- Strategy-indexed partial behavior (Option C Skolemized form):
    `defined` holds when there exists an angelic strategy `strat` under which
    every demonic path is safe (`out.isSafe`). -/
def StrategyBehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∃ strat : AngelicStrategy State,
          ∀ tr out,
            ReachesWithStrategy M strat p q.init q.steps q.init tr out →
            out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ∃ strat : AngelicStrategy State,
        (∀ tr' out',
          ReachesWithStrategy M strat p q.init q.steps q.init tr' out' →
          out'.isSafe) ∧
        ReachesWithStrategy M strat p q.init q.steps q.init out.trace out.outcome
  }

/-- Under `StrategyBehaviorOf`, `angelicTrapMachine` at `⟨0, 2⟩` is `defined`
    (`True`), witnessed by the constant angelic strategy
    `strat := fun _ _ => 1`. -/
theorem optionC_strategy_angelic_trap_is_defined :
    (StrategyBehaviorOf angelicTrapMachine () ⟨0, 2⟩).defined := by
  intro _
  refine ⟨fun _ _ => 1, ?_⟩
  intro tr out hreach
  cases hreach with
  | step _ _ _ _ _ _ h0 _ => cases h0
  | demonicChoice _ _ _ _ _ _ h0 _ _ => cases h0
  | emptyDemonicChoice _ _ _ h0 _ => cases h0
  | invalidAngelicChoice _ _ _ h0 hbad =>
    have h0' : StepResult.choice .angelic _ =
        StepResult.choice (State := Nat) (Obs := Unit) (Val := Unit)
          .angelic (fun s' => s' = 1 ∨ s' = 2) := h0
    injection h0' with _ hbr
    rw [hbr] at hbad
    exact False.elim (hbad (Or.inl rfl))
  | terminated _ _ _ h0 => cases h0
  | failed _ _ _ h0 => cases h0
  | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)
  | angelicChoice _ _ _ _ _ h0 _ hrest =>
    cases hrest with
    | step _ _ _ _ _ _ h1 _ => cases h1
    | demonicChoice _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyDemonicChoice _ _ _ h1 _ => cases h1
    | angelicChoice _ _ _ _ _ h1 _ _ => cases h1
    | invalidAngelicChoice _ _ _ h1 _ => cases h1
    | terminated _ _ _ _ => exact trivial
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hno => exact False.elim (hno ⟨_, rfl⟩)

/-- Resolving an angelic strategy `strat` turns any `SmallStepMachine` into a
    demonic-only machine `M.withStrategy strat`. -/
def SmallStepMachine.withStrategy
    (M : SmallStepMachine Prog State Obs Val)
    (strat : AngelicStrategy State) (k : Nat) :
    SmallStepMachine Prog State Obs Val where
  initState := M.initState
  step p s r :=
    match r with
    | .step obs s' => M.step p s (.step obs s')
    | .choice .demonic branches => M.step p s (.choice .demonic branches)
    | .choice .angelic branches =>
        ∃ branches₀,
          M.step p s (.choice .angelic branches₀) ∧
          branches = (fun s' => branches₀ s' ∧ s' = strat k s)
    | .terminated term => M.step p s (.terminated term)
    | .failed err => M.step p s (.failed err)

/-- Adequacy of `wpDualAt` for `GameBehaviorOf` against `SpecOn`: if `wpDualAt`
    holds at `q.steps` with `post q ⟨tr, out⟩` and `post` holds on safe
    reachable prefixes, then `GameBehaviorOf M p ≤ L.SpecOn pre post`. -/
theorem wpDual_adequacy_specOn
    (M : SmallStepMachine Prog State Obs Val)
    (stateInterp : State → List Obs → SProp Res)
    (p : Prog)
    (pre : ExecQuery State → Prop)
    (post : ExecQuery State → ExecOut Obs Val → Prop)
    (hwp : ∀ (q : ExecQuery State),
      pre q →
      M.initState p q.init →
      ∃ r₀ : Res,
        (stateInterp q.init [] ∗
          wpDualAt M stateInterp p q.steps q.init []
            (fun tr out => SProp.pure (post q ⟨tr, out⟩))) q.steps r₀)
    (hpost : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init →
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe →
      GameHolds M p (fun tr o => o.isSafe ∧ post q ⟨tr, o⟩)
        q.steps q.init [] →
      post q out) :
    let L : Language := ⟨Prog, ExecQuery State, ExecOut Obs Val, GameBehaviorOf M⟩
    GameBehaviorOf M p ≤ L.SpecOn pre post := by
  intro L q hpre
  refine ⟨?_, ?_⟩
  · intro hinit
    rcases hwp q hpre hinit with ⟨r₀, hq⟩
    have hgame := wpDualAt_sound_for_gameHolds M stateInterp p
      q.steps q.init [] (fun tr out => post q ⟨tr, out⟩) r₀ hq
    exact GameHolds.mono (fun _ _ h => h.1) q.steps q.init [] hgame
  · intro out ⟨hinit, hreach, hsafe⟩
    rcases hwp q hpre hinit with ⟨r₀, hq⟩
    have hgame := wpDualAt_sound_for_gameHolds M stateInterp p
      q.steps q.init [] (fun tr o => post q ⟨tr, o⟩) r₀ hq
    exact hpost q out hpre hinit hreach hsafe hgame

/-!
## 6. Concrete Canary Instantiations
-/

/-- Concrete partial finite-map heap resource for our canary separation algebra:
    two small 2-cell heaps (`cell0`, `cell1 : Option Nat`) are disjoint when
    they do not both own the same cell. -/
structure TwoCellHeap where
  cell0 : Option Nat
  cell1 : Option Nat

def Option.disjoint (a b : Option α) : Prop :=
  a = none ∨ b = none

def Option.merge (a b : Option α) : Option α :=
  match a with
  | some x => some x
  | none => b

theorem Option.disjoint_symm {a b : Option α} (h : Option.disjoint a b) :
    Option.disjoint b a :=
  h.symm

theorem Option.merge_comm {a b : Option α} (h : Option.disjoint a b) :
    Option.merge a b = Option.merge b a := by
  cases a <;> cases b <;> simp [Option.merge]
  cases h <;> contradiction

theorem Option.disjoint_assoc_l {a b c : Option α}
    (hab : Option.disjoint a b)
    (hab_c : Option.disjoint (Option.merge a b) c) :
    Option.disjoint b c := by
  cases a <;> cases b <;> cases c <;>
    simp [Option.disjoint, Option.merge] at hab hab_c ⊢

theorem Option.disjoint_assoc_r {a b c : Option α}
    (hab : Option.disjoint a b)
    (hab_c : Option.disjoint (Option.merge a b) c) :
    Option.disjoint a (Option.merge b c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Option.disjoint, Option.merge] at hab hab_c ⊢

theorem Option.merge_assoc {a b c : Option α}
    (hab : Option.disjoint a b)
    (hab_c : Option.disjoint (Option.merge a b) c) :
    Option.merge (Option.merge a b) c = Option.merge a (Option.merge b c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Option.disjoint, Option.merge] at hab hab_c ⊢

instance : SepAlgebra TwoCellHeap where
  unit := ⟨none, none⟩
  disjoint h₁ h₂ :=
    Option.disjoint h₁.cell0 h₂.cell0 ∧ Option.disjoint h₁.cell1 h₂.cell1
  op h₁ h₂ := ⟨Option.merge h₁.cell0 h₂.cell0, Option.merge h₁.cell1 h₂.cell1⟩
  disjoint_symm h := ⟨Option.disjoint_symm h.1, Option.disjoint_symm h.2⟩
  disjoint_unit_l _ := ⟨Or.inl rfl, Or.inl rfl⟩
  disjoint_unit_r _ := ⟨Or.inr rfl, Or.inr rfl⟩
  op_comm h := by
    cases h with
    | intro h0 h1 =>
        simp [Option.merge_comm h0, Option.merge_comm h1]
  op_unit_l h := by cases h; rfl
  op_unit_r h := by
    cases h with
    | mk c0 c1 =>
        cases c0 <;> cases c1 <;> rfl
  disjoint_assoc_l hab hab_c :=
    ⟨Option.disjoint_assoc_l hab.1 hab_c.1,
     Option.disjoint_assoc_l hab.2 hab_c.2⟩
  disjoint_assoc_r hab hab_c :=
    ⟨Option.disjoint_assoc_r hab.1 hab_c.1,
     Option.disjoint_assoc_r hab.2 hab_c.2⟩
  op_assoc hab hab_c := by
    simp [Option.merge_assoc hab.1 hab_c.1, Option.merge_assoc hab.2 hab_c.2]

/-- Canary 1: Infinite reactive counter loop that emits the current counter on
    every step and never terminates. -/
def counterLoopMachine : SmallStepMachine Unit Nat Nat Unit where
  initState _ s := s = 0
  step _ s r := r = .step s (s + 1)

def trivialStateInterp : Nat → List Nat → SProp TwoCellHeap :=
  fun _ _ _ _ => True

theorem wpAt_counterLoop (k : Nat) (s : Nat) (hist : List Nat) :
    wpAt counterLoopMachine trivialStateInterp () k s hist (fun _ _ => SProp.emp)
      k ⟨none, none⟩ := by
  induction k generalizing s hist with
  | zero =>
      intro r_s _hdisj _hs
      exact bupd_intro 0 _ ⟨r_s, ⟨none, none⟩, ⟨Or.inr rfl, Or.inr rfl⟩,
        (SepAlgebra.op_unit_r r_s).symm, trivial, trivial⟩
  | succ k ih =>
      intro r_s _hdisj _hs
      refine ⟨⟨none, none⟩, r_s, ⟨Or.inl rfl, Or.inl rfl⟩, rfl,
        ⟨.step s (s + 1), rfl⟩, ?_⟩
      intro stepRes hm
      subst hm
      exact bupd_intro (k + 1) r_s
        ⟨r_s, ⟨none, none⟩, ⟨Or.inr rfl, Or.inr rfl⟩,
          (SepAlgebra.op_unit_r r_s).symm, trivial, ih (s + 1) (hist ++ [s])⟩

/-- Canary 1 Adequacy: The diverging counter loop satisfies Anneal's
    all-prefix `WellFormed` specification across every step budget `q.steps`. -/
theorem counterLoop_wellFormed :
    BehaviorOf counterLoopMachine () ≤
      (counterLoopMachine.toLanguage).WellFormed := by
  apply wp_adequacy_wellFormed counterLoopMachine trivialStateInterp ()
  intro q _hinit
  refine ⟨⟨none, none⟩, ⟨⟨none, none⟩, ⟨none, none⟩, ⟨Or.inl rfl, Or.inl rfl⟩,
    rfl, trivial, wpAt_counterLoop q.steps q.init []⟩⟩

/-- Canary 2: Two-cell stateful swap-and-add program verified with genuine
    points-to ownership in `TwoCellHeap`, discharging `Spec` via
    `wp_adequacy_spec`. -/
inductive TwoCellPhase where
  | start
  | done
  deriving DecidableEq

structure TwoCellState where
  phase : TwoCellPhase
  c0 : Nat
  c1 : Nat

def twoCellMachine : SmallStepMachine Unit TwoCellState Nat Nat where
  initState _ s := s.phase = .start ∧ s.c0 = 10 ∧ s.c1 = 32
  step _ s r :=
    match s.phase with
    | .start => r = .step (s.c0 + s.c1) ⟨.done, s.c0 + s.c1, s.c1⟩
    | .done => r = .terminated (.normal s.c0)

def twoCellStateInterp (s : TwoCellState) (_hist : List Nat) :
    SProp TwoCellHeap :=
  fun _ h => h = ⟨some s.c0, some s.c1⟩

theorem twoCell_spec :
    BehaviorOf twoCellMachine () ≤
      (twoCellMachine.toLanguage).Spec (fun _q out =>
        match out.outcome with
        | .running => True
        | .terminated (.normal v) => v = 42 ∧ out.trace = [42]
        | .terminated .unwind => False
        | .failed _ => False
        | .stuck => False) := by
  apply wp_adequacy_spec twoCellMachine twoCellStateInterp ()
  intro q ⟨hphase, hc0, hc1⟩
  refine ⟨⟨some q.init.c0, some q.init.c1⟩,
    ⟨⟨some q.init.c0, some q.init.c1⟩, ⟨none, none⟩,
      ⟨Or.inr rfl, Or.inr rfl⟩, rfl, rfl, ?_⟩⟩
  cases hsteps : q.steps with
  | zero =>
      intro r_s _hdisj hs
      exact bupd_intro 0 _ ⟨r_s, ⟨none, none⟩, ⟨Or.inr rfl, Or.inr rfl⟩,
        by rw [hs]; rfl, hs, trivial⟩
  | succ k =>
      intro r_s _hdisj hs
      have hstep_start :
          twoCellMachine.step () q.init
            (.step (q.init.c0 + q.init.c1)
              ⟨.done, q.init.c0 + q.init.c1, q.init.c1⟩) := by
        simp [twoCellMachine, hphase]
      refine ⟨⟨none, none⟩, r_s, ⟨Or.inl rfl, Or.inl rfl⟩, rfl,
        ⟨_, hstep_start⟩, ?_⟩
      intro stepRes hm
      simp only [twoCellMachine, hphase] at hm
      subst hm
      intro r_f hdisj_rf
      have hr_f_none : r_f = ⟨none, none⟩ := by
        rw [hs] at hdisj_rf
        rcases hdisj_rf with ⟨h0 | h0, h1 | h1⟩
        · contradiction
        · contradiction
        · contradiction
        · cases r_f; subst h0 h1; rfl
      subst hr_f_none
      let s1 : TwoCellState := ⟨.done, q.init.c0 + q.init.c1, q.init.c1⟩
      let h1 : TwoCellHeap := ⟨some s1.c0, some s1.c1⟩
      refine ⟨h1, ⟨Or.inr rfl, Or.inr rfl⟩,
        ⟨h1, ⟨none, none⟩, ⟨Or.inr rfl, Or.inr rfl⟩, rfl, rfl, ?_⟩⟩
      cases k with
      | zero =>
          intro r_s1 _hdisj1 hs1
          exact bupd_intro 0 _ ⟨r_s1, ⟨none, none⟩, ⟨Or.inr rfl, Or.inr rfl⟩,
            by rw [hs1]; rfl, hs1, trivial⟩
      | succ k' =>
          intro r_s1 _hdisj1 hs1
          have hstep_done :
              twoCellMachine.step () s1 (.terminated (.normal s1.c0)) := by
            simp [twoCellMachine, s1]
          refine ⟨⟨none, none⟩, r_s1, ⟨Or.inl rfl, Or.inl rfl⟩, rfl,
            ⟨_, hstep_done⟩, ?_⟩
          intro stepRes1 hm1
          simp only [twoCellMachine] at hm1
          subst hm1
          refine bupd_intro (k' + 1) r_s1 ⟨r_s1, ⟨none, none⟩,
            ⟨Or.inr rfl, Or.inr rfl⟩, by rw [hs1]; rfl, hs1, ?_⟩
          simp [hc0, hc1]
          trivial

end AnnealStepWPAdequacyProbe

#print axioms AnnealStepWPAdequacyProbe.wp_adequacy_reachesPrefix
#print axioms AnnealStepWPAdequacyProbe.wp_adequacy_specOn
#print axioms AnnealStepWPAdequacyProbe.wp_adequacy_wellFormedOn
#print axioms AnnealStepWPAdequacyProbe.wp_adequacy_wellFormed
#print axioms AnnealStepWPAdequacyProbe.wp_adequacy_compiler_verified
#print axioms AnnealStepWPAdequacyProbe.angelic_choice_phantom_in_reachesPrefix
#print axioms AnnealStepWPAdequacyProbe.optionB_angelic_trap_is_ub
#print axioms AnnealStepWPAdequacyProbe.reachesPrefixA_iff_reachesPrefix
#print axioms AnnealStepWPAdequacyProbe.wpDualAt_sound_for_safePrefixWithPost
#print axioms AnnealStepWPAdequacyProbe.wpDualAt_sound_for_gameHolds
#print axioms AnnealStepWPAdequacyProbe.wpDual_adequacy_specOn
#print axioms AnnealStepWPAdequacyProbe.optionC_angelic_trap_holds
#print axioms AnnealStepWPAdequacyProbe.optionC_angelic_trap_is_defined
#print axioms AnnealStepWPAdequacyProbe.optionC_strategy_angelic_trap_is_defined
#print axioms AnnealStepWPAdequacyProbe.counterLoop_wellFormed
#print axioms AnnealStepWPAdequacyProbe.twoCell_spec
