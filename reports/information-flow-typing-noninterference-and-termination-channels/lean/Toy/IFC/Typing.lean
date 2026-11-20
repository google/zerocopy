import Toy.IFC.Core

/-!
# Information-Flow Security Type Systems

This module defines:
- `CmdTyped`: the syntax-directed program-counter (`pc`-label) presentation of
  information-flow security typing (Nipkow & Klein 2014, §9.2.2 `sec_type`,
  specialized to `{low, high}`, in the tradition of Volpano, Irvine & Smith 1996);
- `TsTyped`: its termination-sensitive strengthening requiring both `pc = low`
  and `exprLevel Γ e = low` at every `while` loop;
- four syntactic ablations and comparison disciplines:
  - `NoPcTyped`: drops program-counter tracking everywhere;
  - `WhileNoPcTyped`: raises `pc` at `if` but omits raising `pc` at `while`;
  - `LowGuardWhileTyped`: requires `exprLevel Γ e = low` on `while` without
    requiring `pc = low` on `while`;
  - `PcLowWhileTyped`: requires `pc = low` on `while` without requiring
    `exprLevel Γ e = low` on `while`;
  - `NoHighGuardTyped`: a `pc`-free sound discipline forbidding `high` guards
    in both `if` and `while` (matching `cf_well_typed` in Software Foundations
    Vol. 7, `StaticIFC`).
-/

namespace Toy.IFC

/-- Syntax-directed program-counter (`pc`-label) security type system,
    matching Nipkow & Klein's `sec_type` (2014, §9.2.2; HOL-IMP `Sec_Typing.thy`)
    specialized to the two-point lattice `{low, high}`, in the tradition of
    Volpano, Irvine & Smith (1996). (Volpano, Irvine & Smith's original system
    uses phrase types `τ var` / `τ cmd` with contravariant command subtyping,
    `letvar`, and an arbitrary lattice; equivalence with that presentation is
    not formalized here.)
    `CmdTyped Γ pc c` certifies that under security labeling `Γ` and program-counter
    context `pc` (a lower bound on the security level of variables assigned by `c`),
    command `c` has no explicit or implicit flows from `high` to `low`.
    By design, this system allows `while` loops guarded by `high` expressions and
    loops inside `high` branches, so it enforces termination-insensitive
    noninterference (`TINI`) only. -/
inductive CmdTyped {Var : Type} (Γ : Var → Level) : Level → Cmd Var → Prop where
  | skip {pc} :
      CmdTyped Γ pc .skip
  | assign {pc x e} :
      exprLevel Γ e ≤ Γ x →
      pc ≤ Γ x →
      CmdTyped Γ pc (.assign x e)
  | seq {pc c₁ c₂} :
      CmdTyped Γ pc c₁ →
      CmdTyped Γ pc c₂ →
      CmdTyped Γ pc (.seq c₁ c₂)
  | ite {pc e c₁ c₂} :
      CmdTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
      CmdTyped Γ (pc ⊔ exprLevel Γ e) c₂ →
      CmdTyped Γ pc (.ite e c₁ c₂)
  | whileLoop {pc e c} :
      CmdTyped Γ (pc ⊔ exprLevel Γ e) c →
      CmdTyped Γ pc (.whileLoop e c)

/-- Anti-monotonicity (command subsumption) for `CmdTyped`: any command well typed
    in a higher `pc` context is also well typed in any lower `pc` context. -/
theorem CmdTyped.antitone {Var : Type} {Γ : Var → Level} {pc₁ pc₂ : Level} {c : Cmd Var}
    (hle : pc₁ ≤ pc₂) (ht : CmdTyped Γ pc₂ c) : CmdTyped Γ pc₁ c := by
  induction ht generalizing pc₁ with
  | skip => exact .skip
  | assign he hpc => exact .assign he (Level.le_trans hle hpc)
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hle) (ih₂ hle)
  | ite _ _ ih₁ ih₂ =>
    exact .ite
      (ih₁ (Level.join_mono hle (Level.le_refl _)))
      (ih₂ (Level.join_mono hle (Level.le_refl _)))
  | whileLoop _ ih =>
    exact .whileLoop (ih (Level.join_mono hle (Level.le_refl _)))

/-- Explicit-flow-only ablation of `CmdTyped`: enforces `exprLevel Γ e ≤ Γ x` on
    every assignment, but omits program-counter (`pc`) tracking and the `pc ≤ Γ x`
    guard on assignments. Captures a naive static taint check that blocks direct
    flows (`l := h`) while overlooking control-flow implicit flows. -/
inductive NoPcTyped {Var : Type} (Γ : Var → Level) : Cmd Var → Prop where
  | skip :
      NoPcTyped Γ .skip
  | assign {x e} :
      exprLevel Γ e ≤ Γ x →
      NoPcTyped Γ (.assign x e)
  | seq {c₁ c₂} :
      NoPcTyped Γ c₁ →
      NoPcTyped Γ c₂ →
      NoPcTyped Γ (.seq c₁ c₂)
  | ite {e c₁ c₂} :
      NoPcTyped Γ c₁ →
      NoPcTyped Γ c₂ →
      NoPcTyped Γ (.ite e c₁ c₂)
  | whileLoop {e c} :
      NoPcTyped Γ c →
      NoPcTyped Γ (.whileLoop e c)

/-- Partial `pc`-tracking ablation of `CmdTyped`: raises `pc` by `exprLevel Γ e`
    at conditionals (`ite`) and enforces `pc ≤ Γ x` on assignments, but omits
    raising `pc` by the loop guard at `while` loops (typing the loop body at the
    outer `pc`). Isolates why `pc` must be raised at `while` as well as at `if`. -/
inductive WhileNoPcTyped {Var : Type} (Γ : Var → Level) : Level → Cmd Var → Prop where
  | skip {pc} :
      WhileNoPcTyped Γ pc .skip
  | assign {pc x e} :
      exprLevel Γ e ≤ Γ x →
      pc ≤ Γ x →
      WhileNoPcTyped Γ pc (.assign x e)
  | seq {pc c₁ c₂} :
      WhileNoPcTyped Γ pc c₁ →
      WhileNoPcTyped Γ pc c₂ →
      WhileNoPcTyped Γ pc (.seq c₁ c₂)
  | ite {pc e c₁ c₂} :
      WhileNoPcTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
      WhileNoPcTyped Γ (pc ⊔ exprLevel Γ e) c₂ →
      WhileNoPcTyped Γ pc (.ite e c₁ c₂)
  | whileLoop {pc e c} :
      WhileNoPcTyped Γ pc c →
      WhileNoPcTyped Γ pc (.whileLoop e c)

/-- A sound `pc`-free control-dependence discipline (matching `cf_well_typed` in
    Software Foundations Vol. 7, `StaticIFC`): enforces explicit-flow bounds on
    assignments and forbids `high` guards on every `if` and `while` altogether,
    without tracking a `pc` label. Embeds into `CmdTyped Γ .low`, illustrating
    that a `pc` label is not the only sound way to block implicit flows. -/
inductive NoHighGuardTyped {Var : Type} (Γ : Var → Level) : Cmd Var → Prop where
  | skip :
      NoHighGuardTyped Γ .skip
  | assign {x e} :
      exprLevel Γ e ≤ Γ x →
      NoHighGuardTyped Γ (.assign x e)
  | seq {c₁ c₂} :
      NoHighGuardTyped Γ c₁ →
      NoHighGuardTyped Γ c₂ →
      NoHighGuardTyped Γ (.seq c₁ c₂)
  | ite {e c₁ c₂} :
      exprLevel Γ e = .low →
      NoHighGuardTyped Γ c₁ →
      NoHighGuardTyped Γ c₂ →
      NoHighGuardTyped Γ (.ite e c₁ c₂)
  | whileLoop {e c} :
      exprLevel Γ e = .low →
      NoHighGuardTyped Γ c →
      NoHighGuardTyped Γ (.whileLoop e c)

/-- Intermediate ablation between `CmdTyped` and `TsTyped`: enforces `pc`-tracked
    typing and requires every `while` guard to have syntactic level `low`, but
    omits the requirement that `pc = low` at `while` loops.
    Demonstrates why restricting loop guards alone is insufficient for
    termination-sensitive noninterference (a low-guarded loop nested inside a
    high conditional still creates a termination channel). -/
inductive LowGuardWhileTyped {Var : Type} (Γ : Var → Level) : Level → Cmd Var → Prop where
  | skip {pc} :
      LowGuardWhileTyped Γ pc .skip
  | assign {pc x e} :
      exprLevel Γ e ≤ Γ x →
      pc ≤ Γ x →
      LowGuardWhileTyped Γ pc (.assign x e)
  | seq {pc c₁ c₂} :
      LowGuardWhileTyped Γ pc c₁ →
      LowGuardWhileTyped Γ pc c₂ →
      LowGuardWhileTyped Γ pc (.seq c₁ c₂)
  | ite {pc e c₁ c₂} :
      LowGuardWhileTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
      LowGuardWhileTyped Γ (pc ⊔ exprLevel Γ e) c₂ →
      LowGuardWhileTyped Γ pc (.ite e c₁ c₂)
  | whileLoop {pc e c} :
      exprLevel Γ e = .low →
      LowGuardWhileTyped Γ pc c →
      LowGuardWhileTyped Γ pc (.whileLoop e c)

/-- Symmetric intermediate ablation between `CmdTyped` and `TsTyped`: enforces
    `pc`-tracked typing and requires `pc = low` at every `while` loop, but
    omits the requirement that `exprLevel Γ e = low` on the loop guard (typing
    the loop body at `pc ⊔ exprLevel Γ e`).
    Demonstrates why requiring `pc = low` at `while` alone is insufficient for
    termination-sensitive noninterference without also restricting the loop guard. -/
inductive PcLowWhileTyped {Var : Type} (Γ : Var → Level) : Level → Cmd Var → Prop where
  | skip {pc} :
      PcLowWhileTyped Γ pc .skip
  | assign {pc x e} :
      exprLevel Γ e ≤ Γ x →
      pc ≤ Γ x →
      PcLowWhileTyped Γ pc (.assign x e)
  | seq {pc c₁ c₂} :
      PcLowWhileTyped Γ pc c₁ →
      PcLowWhileTyped Γ pc c₂ →
      PcLowWhileTyped Γ pc (.seq c₁ c₂)
  | ite {pc e c₁ c₂} :
      PcLowWhileTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
      PcLowWhileTyped Γ (pc ⊔ exprLevel Γ e) c₂ →
      PcLowWhileTyped Γ pc (.ite e c₁ c₂)
  | whileLoop {pc e c} :
      pc = .low →
      PcLowWhileTyped Γ (pc ⊔ exprLevel Γ e) c →
      PcLowWhileTyped Γ pc (.whileLoop e c)

/-- Termination-sensitive security type system (Volpano & Smith 1997; Sabelfeld &
    Myers 2003, §IV-C; Nipkow & Klein 2014, §9.2.6 Fig. 9.10 / HOL-IMP
    `Sec_TypingT.thy`; Software Foundations Vol. 7 `StaticIFC` `ts_well_typed`).
    Strengthens `CmdTyped` by requiring that every `while` loop execute in a
    `low` program-counter context (`pc = low`) with a `low` guard
    (`exprLevel Γ e = low`), so no loop's entry or iteration count can depend
    on a `high` variable. High conditionals remain permitted provided their
    branches are loop-free and assign only to `high` variables. -/
inductive TsTyped {Var : Type} (Γ : Var → Level) : Level → Cmd Var → Prop where
  | skip {pc} :
      TsTyped Γ pc .skip
  | assign {pc x e} :
      exprLevel Γ e ≤ Γ x →
      pc ≤ Γ x →
      TsTyped Γ pc (.assign x e)
  | seq {pc c₁ c₂} :
      TsTyped Γ pc c₁ →
      TsTyped Γ pc c₂ →
      TsTyped Γ pc (.seq c₁ c₂)
  | ite {pc e c₁ c₂} :
      TsTyped Γ (pc ⊔ exprLevel Γ e) c₁ →
      TsTyped Γ (pc ⊔ exprLevel Γ e) c₂ →
      TsTyped Γ pc (.ite e c₁ c₂)
  | whileLoop {pc e c} :
      pc = .low →
      exprLevel Γ e = .low →
      TsTyped Γ .low c →
      TsTyped Γ pc (.whileLoop e c)

/-- Anti-monotonicity (command subsumption) for `TsTyped`. -/
theorem TsTyped.antitone {Var : Type} {Γ : Var → Level} {pc₁ pc₂ : Level} {c : Cmd Var}
    (hle : pc₁ ≤ pc₂) (ht : TsTyped Γ pc₂ c) : TsTyped Γ pc₁ c := by
  induction ht generalizing pc₁ with
  | skip => exact .skip
  | assign he hpc => exact .assign he (Level.le_trans hle hpc)
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hle) (ih₂ hle)
  | ite _ _ ih₁ ih₂ =>
    exact .ite
      (ih₁ (Level.join_mono hle (Level.le_refl _)))
      (ih₂ (Level.join_mono hle (Level.le_refl _)))
  | whileLoop hpc he hbody _ =>
    subst hpc
    exact .whileLoop (Level.eq_low_of_le_low hle) he hbody

/-! ### Inclusion Hierarchy Among Typing Relations -/

theorem tsTyped_implies_lowGuardWhileTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : TsTyped Γ pc c) :
    LowGuardWhileTyped Γ pc c := by
  induction h with
  | skip => exact .skip
  | assign he hpc => exact .assign he hpc
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite _ _ ih₁ ih₂ => exact .ite ih₁ ih₂
  | whileLoop hpc he _ ih =>
    subst hpc
    exact .whileLoop he ih

theorem tsTyped_implies_pcLowWhileTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : TsTyped Γ pc c) :
    PcLowWhileTyped Γ pc c := by
  induction h with
  | skip => exact .skip
  | assign he hpc => exact .assign he hpc
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite _ _ ih₁ ih₂ => exact .ite ih₁ ih₂
  | whileLoop hpc he _ ih =>
    subst hpc
    apply PcLowWhileTyped.whileLoop rfl
    simpa [he] using ih

theorem lowGuardWhileTyped_implies_cmdTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : LowGuardWhileTyped Γ pc c) :
    CmdTyped Γ pc c := by
  induction h with
  | skip => exact .skip
  | assign he hpc => exact .assign he hpc
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite _ _ ih₁ ih₂ => exact .ite ih₁ ih₂
  | whileLoop he _ ih =>
    apply CmdTyped.whileLoop
    simpa [he] using ih

theorem pcLowWhileTyped_implies_cmdTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : PcLowWhileTyped Γ pc c) :
    CmdTyped Γ pc c := by
  induction h with
  | skip => exact .skip
  | assign he hpc => exact .assign he hpc
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite _ _ ih₁ ih₂ => exact .ite ih₁ ih₂
  | whileLoop _ _ ih => exact .whileLoop ih

theorem tsTyped_implies_cmdTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : TsTyped Γ pc c) :
    CmdTyped Γ pc c :=
  lowGuardWhileTyped_implies_cmdTyped (tsTyped_implies_lowGuardWhileTyped h)

theorem noHighGuardTyped_implies_cmdTyped_low {Var : Type} {Γ : Var → Level}
    {c : Cmd Var} (h : NoHighGuardTyped Γ c) :
    CmdTyped Γ .low c := by
  induction h with
  | skip => exact .skip
  | assign he => exact .assign he (Level.low_le _)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite he _ _ ih₁ ih₂ =>
    exact .ite (by simpa [he] using ih₁) (by simpa [he] using ih₂)
  | whileLoop he _ ih =>
    exact .whileLoop (by simpa [he] using ih)

/-- Anti-monotonicity for `WhileNoPcTyped`. -/
theorem WhileNoPcTyped.antitone {Var : Type} {Γ : Var → Level} {pc₁ pc₂ : Level} {c : Cmd Var}
    (hle : pc₁ ≤ pc₂) (ht : WhileNoPcTyped Γ pc₂ c) : WhileNoPcTyped Γ pc₁ c := by
  induction ht generalizing pc₁ with
  | skip => exact .skip
  | assign he hpc => exact .assign he (Level.le_trans hle hpc)
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hle) (ih₂ hle)
  | ite _ _ ih₁ ih₂ =>
    exact .ite
      (ih₁ (Level.join_mono hle (Level.le_refl _)))
      (ih₂ (Level.join_mono hle (Level.le_refl _)))
  | whileLoop _ ih => exact .whileLoop (ih hle)

theorem cmdTyped_implies_whileNoPcTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : CmdTyped Γ pc c) :
    WhileNoPcTyped Γ pc c := by
  induction h with
  | skip => exact .skip
  | assign he hpc => exact .assign he hpc
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite _ _ ih₁ ih₂ => exact .ite ih₁ ih₂
  | whileLoop _ ih =>
    exact .whileLoop (WhileNoPcTyped.antitone (Level.le_join_left _ _) ih)

theorem whileNoPcTyped_implies_noPcTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : WhileNoPcTyped Γ pc c) :
    NoPcTyped Γ c := by
  induction h with
  | skip => exact .skip
  | assign he _ => exact .assign he
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite _ _ ih₁ ih₂ => exact .ite ih₁ ih₂
  | whileLoop _ ih => exact .whileLoop ih

theorem cmdTyped_implies_noPcTyped {Var : Type} {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (h : CmdTyped Γ pc c) :
    NoPcTyped Γ c :=
  whileNoPcTyped_implies_noPcTyped (cmdTyped_implies_whileNoPcTyped h)

/-! ### Positive & Negative Examples for All Typing Relations -/

/-- Sample well-typed program exercising high branching, high writes, and low writes:
    `if h then h := h + 1 else h := 0; l := l + 1`. -/
def sampleTypedProg : Cmd TwoVar :=
  .seq
    (.ite (.var .h)
      (.assign .h (.add (.var .h) (.lit 1)))
      (.assign .h (.lit 0)))
    (.assign .l (.add (.var .l) (.lit 1)))

/-- Sample termination-sensitive program exercising a low-guarded loop with a high
    conditional and high mutation inside:
    `while l do (if h then h := h - 1 else h := 0; l := l - 1)`. -/
def sampleTsProg : Cmd TwoVar :=
  .whileLoop (.var .l)
    (.seq
      (.ite (.var .h)
        (.assign .h (.sub (.var .h) (.lit 1)))
        (.assign .h (.lit 0)))
      (.assign .l (.sub (.var .l) (.lit 1))))

-- Positive & negative examples for `CmdTyped`

/-- Positive example for `CmdTyped`: high branching with high writes followed by
    a low write is accepted at `pc = low`. -/
theorem cmdTyped_pos_sampleTypedProg :
    CmdTyped twoVarEnv .low sampleTypedProg := by
  refine .seq (.ite (.assign ?_ ?_) (.assign ?_ ?_)) (.assign ?_ ?_) <;>
    simp [exprLevel, twoVarEnv, Level.join, LE.le, Level.le]

/-- Positive example for `CmdTyped`: high-guarded `while h do skip` is accepted. -/
theorem cmdTyped_pos_while_h :
    CmdTyped twoVarEnv .low (termChannelProg .h) :=
  .whileLoop .skip

/-- Positive example for `CmdTyped`: `while h do h := 0` is accepted even at `pc = high`. -/
theorem whileHZero_cmdTyped_high :
    CmdTyped twoVarEnv .high whileHZero :=
  .whileLoop (.assign (by simp [exprLevel, twoVarEnv, LE.le, Level.le])
    (by simp [twoVarEnv, Level.join, LE.le, Level.le]))

/-- Negative example for `CmdTyped`: direct explicit flow `l := h` is rejected. -/
theorem cmdTyped_neg_explicit_flow (pc : Level) :
    ¬ CmdTyped twoVarEnv pc (explicitFlowProg .l .h) := by
  intro h
  cases h with
  | assign he _ =>
    simp [exprLevel, twoVarEnv, LE.le, Level.le] at he

/-- Negative example for `CmdTyped`: implicit flow `if h then l := 1 else l := 0` is rejected. -/
theorem cmdTyped_neg_implicit_flow (pc : Level) :
    ¬ CmdTyped twoVarEnv pc (implicitFlowProg .l .h) := by
  intro h
  cases h with
  | ite h₁ _ =>
    cases h₁ with
    | assign _ hpc =>
      simp only [exprLevel, twoVarEnv, Level.join_high_right] at hpc
      exact hpc

-- Positive & negative examples for `NoPcTyped`

/-- Positive example for `NoPcTyped`: accepts `if h then l := 1 else l := 0`. -/
theorem noPcTyped_pos_implicit_flow :
    NoPcTyped twoVarEnv (implicitFlowProg .l .h) :=
  .ite (.assign (by simp [exprLevel, twoVarEnv, LE.le, Level.le]))
       (.assign (by simp [exprLevel, twoVarEnv, LE.le, Level.le]))

/-- Negative example for `NoPcTyped`: still rejects direct explicit flow `l := h`. -/
theorem noPcTyped_neg_explicit_flow :
    ¬ NoPcTyped twoVarEnv (explicitFlowProg .l .h) := by
  intro h
  cases h with
  | assign he =>
    simp [exprLevel, twoVarEnv, LE.le, Level.le] at he

-- Positive & negative examples for `WhileNoPcTyped`

/-- Positive example for `WhileNoPcTyped`: accepts `while h do (l := 1; h := 0)` at `pc = low`. -/
theorem whileNoPcTyped_pos_whileLeakProg :
    WhileNoPcTyped twoVarEnv .low (whileLeakProg .l .h) :=
  .whileLoop (.seq
    (.assign (Level.low_le _) (Level.low_le _))
    (.assign (Level.low_le _) (Level.low_le _)))

/-- Negative example for `WhileNoPcTyped`: still rejects `if h then l := 1 else l := 0`
    at every `pc` (since `pc` is raised at `ite`). -/
theorem whileNoPcTyped_neg_implicit_flow (pc : Level) :
    ¬ WhileNoPcTyped twoVarEnv pc (implicitFlowProg .l .h) := by
  intro h
  cases h with
  | ite h₁ _ =>
    cases h₁ with
    | assign _ hpc =>
      simp only [exprLevel, twoVarEnv, Level.join_high_right] at hpc
      exact hpc

-- Positive & negative examples for `NoHighGuardTyped`

/-- Positive example for `NoHighGuardTyped`: accepts a `low`-guarded conditional
    assigning to both `high` and `low` variables. -/
theorem noHighGuardTyped_pos_low_ite :
    NoHighGuardTyped twoVarEnv (.ite (.var .l) (.assign .h (.lit 1)) (.assign .l (.lit 0))) :=
  .ite rfl (.assign (Level.low_le _)) (.assign (Level.low_le _))

/-- Negative example for `NoHighGuardTyped`: rejects `if h then l := 1 else l := 0`. -/
theorem noHighGuardTyped_neg_implicit_flow :
    ¬ NoHighGuardTyped twoVarEnv (implicitFlowProg .l .h) := by
  intro h
  cases h with
  | ite he _ _ =>
    simp [exprLevel, twoVarEnv] at he

-- Positive & negative examples for `LowGuardWhileTyped`

/-- Positive example for `LowGuardWhileTyped`: accepts `if h then (while 1 do skip) else skip`. -/
theorem lowGuardWhileTyped_pos_high_if_low_while :
    LowGuardWhileTyped twoVarEnv .low (highIfLowWhileProg .h) :=
  .ite (.whileLoop rfl .skip) .skip

/-- Negative example for `LowGuardWhileTyped`: rejects high-guarded `while h do skip`. -/
theorem lowGuardWhileTyped_neg_while_h (pc : Level) :
    ¬ LowGuardWhileTyped twoVarEnv pc (termChannelProg .h) := by
  intro h
  cases h with
  | whileLoop he _ =>
    simp [exprLevel, twoVarEnv] at he

-- Positive & negative examples for `PcLowWhileTyped`

/-- Positive example for `PcLowWhileTyped`: accepts high-guarded `while h do skip` at `pc = low`. -/
theorem pcLowWhileTyped_pos_while_h :
    PcLowWhileTyped twoVarEnv .low (termChannelProg .h) :=
  .whileLoop rfl .skip

/-- Negative example for `PcLowWhileTyped`: rejects low-guarded loop nested under a
    high conditional (`if h then (while 1 do skip) else skip`) at every `pc`. -/
theorem pcLowWhileTyped_neg_high_if_low_while (pc : Level) :
    ¬ PcLowWhileTyped twoVarEnv pc (highIfLowWhileProg .h) := by
  intro h
  cases h with
  | ite h₁ _ =>
    cases h₁ with
    | whileLoop hpc _ =>
      simp [exprLevel, twoVarEnv] at hpc

-- Positive & negative examples for `TsTyped`

/-- Positive example for `TsTyped`: accepts a low-guarded loop containing a high
    conditional and high assignments. -/
theorem tsTyped_pos_sampleTsProg :
    TsTyped twoVarEnv .low sampleTsProg := by
  refine .whileLoop rfl rfl (.seq (.ite (.assign ?_ ?_) (.assign ?_ ?_)) (.assign ?_ ?_)) <;>
    simp [exprLevel, twoVarEnv, Level.join, LE.le, Level.le]

/-- Negative example for `TsTyped`: rejects high-guarded `while h do skip`. -/
theorem tsTyped_neg_while_h (pc : Level) :
    ¬ TsTyped twoVarEnv pc (termChannelProg .h) := by
  intro h
  cases h with
  | whileLoop _ he _ =>
    simp [exprLevel, twoVarEnv] at he

/-- Negative example for `TsTyped`: rejects low-guarded loop nested under a high conditional. -/
theorem tsTyped_neg_high_if_low_while (pc : Level) :
    ¬ TsTyped twoVarEnv pc (highIfLowWhileProg .h) := by
  intro h
  cases h with
  | ite h₁ _ =>
    cases h₁ with
    | whileLoop hpc _ _ =>
      simp [exprLevel, twoVarEnv] at hpc

end Toy.IFC
