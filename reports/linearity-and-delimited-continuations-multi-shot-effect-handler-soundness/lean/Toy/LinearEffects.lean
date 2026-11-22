/-!
# Toy Model: Control-Flow Linearity, Multi-Shot / 0-Shot Effect Handlers, and Discontinue Discipline

A self-contained, Mathlib-free Lean 4 (`v4.34.1`) toy operational and typing model
demonstrating:
  (a) 2-shot continuation resumption duplicates a value-linear capability (double-consume).
  (b) 0-shot abortive handling without finalization skips mandatory linear cleanup (leak),
      even when wrapped in `finally` if the handler silently drops `k` instead of unwinding.
  (c) Control-flow-linear typing + explicit `discontinue`/finalizer discipline preserves
      exact single-use resource accounting (`acquired = true`, `consumes = 1`, zero faults)
      across arbitrary well-typed programs, and statically rejects the unsafe counterexamples.

Model–system relation: none proved. This is a finite toy calculus illustrating the core
typing/operational seam, not a mechanized proof of any production compiler or runtime.
-/

namespace Toy.LinearEffects

/-- Resource state of a single linear capability tracked during evaluation. -/
structure ResState where
  acquired : Bool
  consumes : Nat
  faultDoubleConsume : Bool
  deriving DecidableEq, Repr

def ResState.init : ResState :=
  { acquired := false, consumes := 0, faultDoubleConsume := false }

/-- Acquire the linear capability. -/
def ResState.acquire (s : ResState) : ResState :=
  { s with acquired := true }

/-- Consume the linear capability; consuming an already-consumed capability flags a fault. -/
def ResState.consume (s : ResState) : ResState :=
  { s with
      consumes := s.consumes + 1
      faultDoubleConsume := s.faultDoubleConsume || decide (s.consumes ≥ 1) }

/-- Static control-flow linearity grade of an effect operation. -/
inductive OpGrade where
  /-- Control-flow linear: handler resumes continuation `k` exactly once on every path. -/
  | lin
  /-- Control-flow abortive with mandatory unwind: handler never resumes normally,
      and invokes `discontinue` exactly once on every path to run enclosing `finally` cleanup. -/
  | abortDiscontinue
  /-- Control-flow unrestricted: handler may drop `k` (0-shot) or duplicate `k` (≥2-shot). -/
  | unr
  deriving DecidableEq, Repr

/-- Handler clause AST describing how a handler invokes its captured continuation `k`. -/
inductive Clause where
  /-- Silently drop the captured continuation (0-shot abort without unwind). -/
  | dropK
  /-- Invoke `continue k` once (1-shot resumption). -/
  | continueOnce
  /-- Invoke `discontinue k` once (0-shot normal resumption, 1-shot exceptional unwind). -/
  | discontinueOnce
  /-- Invoke `continue k` sequentially twice (2-shot multi-shot resumption). -/
  | continueTwice
  /-- Branch between two clauses based on a runtime boolean. -/
  | branch (cond : Bool) (c1 c2 : Clause)
  deriving DecidableEq, Repr

/-- Computation AST with linear capability acquisition/consumption, guarded cleanup,
    branching, and a delimited effect `perform`. -/
inductive Comp where
  /-- Pure no-op completion. -/
  | pure
  /-- Acquire the linear capability, then run `body`. -/
  | acquire (body : Comp)
  /-- Consume the linear capability, then run `rest`. -/
  | consume (rest : Comp)
  /-- Perform the handled effect; `k` is the delimited continuation after resumption. -/
  | perform (k : Comp)
  /-- Register a `finally` cleanup computation `cleanup` around `body`.
      If `body` exits normally, `cleanup` runs after `body`; if `body` is unwound via
      `discontinue`, `cleanup` runs on the unwind path. -/
  | withFinally (cleanup : Comp) (body : Comp)
  /-- Runtime branch. -/
  | branch (cond : Bool) (c1 c2 : Comp)
  deriving DecidableEq, Repr

/-- Full handled program: a declared operation grade, a handler clause, and a handled body. -/
structure Program where
  grade : OpGrade
  clause : Clause
  body : Comp
  deriving DecidableEq, Repr

/-- Operational semantics of evaluating a handler clause given normal resumption `runNormal`
    and exceptional unwind `runUnwind`. -/
def evalClause (runNormal : ResState → ResState) (runUnwind : ResState → ResState) :
    Clause → ResState → ResState
  | .dropK, s => s
  | .continueOnce, s => runNormal s
  | .discontinueOnce, s => runUnwind s
  | .continueTwice, s => runNormal (runNormal s)
  | .branch b c1 c2, s =>
      if b then evalClause runNormal runUnwind c1 s
      else evalClause runNormal runUnwind c2 s

/-- Evaluate a computation `c` under handler clause `cl`, given:
    - `kNormal`: remaining normal continuation after `c` completes
    - `kUnwind`: accumulated `finally` cleanup continuation to execute if `discontinue` fires. -/
def evalComp (cl : Clause) :
    Comp → (ResState → ResState) → (ResState → ResState) → ResState → ResState
  | .pure, kNormal, _, s => kNormal s
  | .acquire body, kNormal, kUnwind, s =>
      evalComp cl body kNormal kUnwind s.acquire
  | .consume rest, kNormal, kUnwind, s =>
      evalComp cl rest kNormal kUnwind s.consume
  | .perform k, kNormal, kUnwind, s =>
      let runNormal := fun st => evalComp cl k kNormal kUnwind st
      evalClause runNormal kUnwind cl s
  | .withFinally cleanup body, kNormal, kUnwind, s =>
      let nextNormal := fun st => evalComp cl cleanup kNormal kUnwind st
      let nextUnwind := fun st => evalComp cl cleanup kUnwind kUnwind st
      evalComp cl body nextNormal nextUnwind s
  | .branch b c1 c2, kNormal, kUnwind, s =>
      if b then evalComp cl c1 kNormal kUnwind s
      else evalComp cl c2 kNormal kUnwind s

/-- Evaluate a full handled program from the initial empty resource state. -/
def evalProgram (p : Program) : ResState :=
  evalComp p.clause p.body id id ResState.init

/-! ### Parts (a) & (b): Soundness-violation counterexamples -/

/-- A syntactically value-linear body: acquires the capability once, performs an effect,
    and consumes the capability exactly once in the continuation `k`. -/
def valueLinearBody : Comp :=
  .acquire (.perform (.consume .pure))

/-- Counterexample (a): 2-shot multi-shot handler duplicates the linear capability. -/
def twoShotProgram : Program :=
  { grade := .unr, clause := .continueTwice, body := valueLinearBody }

theorem two_shot_duplicates_linear_capability :
    (evalProgram twoShotProgram).consumes = 2 ∧
    (evalProgram twoShotProgram).faultDoubleConsume = true := by
  decide

/-- Counterexample (b): 0-shot abortive handler (silently dropping `k`) skips mandatory
    linear cleanup, leaking the capability (`consumes = 0`). -/
def zeroShotDropProgram : Program :=
  { grade := .unr, clause := .dropK, body := valueLinearBody }

theorem zero_shot_abort_skips_linear_cleanup :
    (evalProgram zeroShotDropProgram).acquired = true ∧
    (evalProgram zeroShotDropProgram).consumes = 0 := by
  decide

/-- Even wrapping the live capability in `withFinally` does NOT protect against a silent
    0-shot `dropK`, because dropping `k` never unwinds the delimited frame. -/
def zeroShotDropWithFinallyProgram : Program :=
  { grade := .unr
    clause := .dropK
    body := .acquire (.withFinally (.consume .pure) (.perform .pure)) }

theorem zero_shot_drop_bypasses_finally :
    (evalProgram zeroShotDropWithFinallyProgram).acquired = true ∧
    (evalProgram zeroShotDropWithFinallyProgram).consumes = 0 := by
  decide

/-! ### Part (c): Control-flow-linear typing + explicit `discontinue`/finalizer discipline -/

/-- Linear capability lifecycle phase. -/
inductive Phase where
  | unacquired
  | live
  | consumed
  deriving DecidableEq, Repr

/-- Exact runtime invariant corresponding to each static `Phase`. -/
def PhaseMatches (ph : Phase) (s : ResState) : Prop :=
  s.faultDoubleConsume = false ∧
  match ph with
  | .unacquired => s.acquired = false ∧ s.consumes = 0
  | .live       => s.acquired = true  ∧ s.consumes = 0
  | .consumed   => s.acquired = true  ∧ s.consumes = 1

/-- Static check that a handler clause obeys its declared `OpGrade` on every path. -/
inductive ClauseTyped : OpGrade → Clause → Prop where
  | lin_continue : ClauseTyped .lin .continueOnce
  | lin_branch {b c1 c2} :
      ClauseTyped .lin c1 → ClauseTyped .lin c2 → ClauseTyped .lin (.branch b c1 c2)
  | abort_discontinue : ClauseTyped .abortDiscontinue .discontinueOnce
  | abort_branch {b c1 c2} :
      ClauseTyped .abortDiscontinue c1 →
      ClauseTyped .abortDiscontinue c2 →
      ClauseTyped .abortDiscontinue (.branch b c1 c2)
  | unr_any (c : Clause) : ClauseTyped .unr c

/-- Phase-indexed control-flow-linear typing judgment `Typed g phIn hasCleanup c phOut`:
    - `g` is the control-flow grade of the handled effect;
    - `phIn` is the linear capability phase on entry;
    - `hasCleanup : Bool` records whether an enclosing `withFinally` cleanup is currently
      responsible for consuming a `.live` capability on `discontinue`;
    - `phOut` is the linear capability phase on normal exit.

    Core control-flow-linearity rules:
    1. `perform_lin`: a `.lin` (1-shot) operation is permitted in any phase.
    2. `perform_abort`: an `.abortDiscontinue` operation is permitted when `.live` ONLY if
       `hasCleanup = true` (an enclosing `withFinally` guarantees unwind consumption), or
       when `.consumed` with `hasCleanup = false` (already cleanly consumed).
    3. `perform_unr_consumed`: an `.unr` (multi-shot / 0-shot) operation is permitted ONLY
       when `phIn = .consumed` and `hasCleanup = false` (no live linear capability spans the
       suspension point, and the continuation does not touch linear resources).
    4. `consume` requires `hasCleanup = false` (preventing manual consumption inside a
       `withFinally` that also consumes on exit/unwind). -/
inductive Typed (g : OpGrade) : Phase → Bool → Comp → Phase → Prop where
  | pure {ph hc} :
      Typed g ph hc .pure ph
  | acquire {body phOut} :
      Typed g .live false body phOut →
      Typed g .unacquired false (.acquire body) phOut
  | consume {rest phOut} :
      Typed g .consumed false rest phOut →
      Typed g .live false (.consume rest) phOut
  | perform_lin {k ph hc phOut} :
      g = .lin →
      Typed g ph hc k phOut →
      Typed g ph hc (.perform k) phOut
  | perform_abort_live {k phOut} :
      g = .abortDiscontinue →
      Typed g .live true k phOut →
      Typed g .live true (.perform k) phOut
  | perform_abort_consumed {k phOut} :
      g = .abortDiscontinue →
      Typed g .consumed false k phOut →
      Typed g .consumed false (.perform k) phOut
  | perform_unr_consumed {k} :
      g = .unr →
      Typed g .consumed false k .consumed →
      Typed g .consumed false (.perform k) .consumed
  | withFinally_cleanup {cleanup body} :
      Typed g .live true body .live →
      Typed g .live false cleanup .consumed →
      Typed g .live false (.withFinally cleanup body) .consumed
  | branch {b c1 c2 ph hc phOut} :
      Typed g ph hc c1 phOut →
      Typed g ph hc c2 phOut →
      Typed g ph hc (.branch b c1 c2) phOut

/-- A complete program is well-typed when its clause obeys its grade and its body transitions
    from `.unacquired` (no enclosing cleanup) to `.consumed`. -/
structure WellTypedProgram (p : Program) : Prop where
  clauseOk : ClauseTyped p.grade p.clause
  bodyOk : Typed p.grade .unacquired false p.body .consumed

/-- Normal continuation soundness: maps states matching `ph` to `.consumed`. -/
def NormalCont (ph : Phase) (k : ResState → ResState) : Prop :=
  ∀ s, PhaseMatches ph s → PhaseMatches .consumed (k s)

/-- Unwind continuation soundness:
    - When `hasCleanup = true`, `kU` consumes a `.live` capability cleanly into `.consumed`.
    - When `hasCleanup = false`, `kU` preserves an already-`.consumed` state. -/
def UnwindCont (hasCleanup : Bool) (kU : ResState → ResState) : Prop :=
  match hasCleanup with
  | true  => ∀ s, PhaseMatches .live s → PhaseMatches .consumed (kU s)
  | false => ∀ s, PhaseMatches .consumed s → PhaseMatches .consumed (kU s)

theorem evalClause_lin {cl : Clause} (hcl : ClauseTyped .lin cl)
    (runNormal runUnwind : ResState → ResState) (s : ResState) :
    evalClause runNormal runUnwind cl s = runNormal s := by
  generalize hg : OpGrade.lin = g at hcl
  induction hcl with
  | lin_continue => rfl
  | @lin_branch b _ _ _ _ ih1 ih2 =>
      simp only [evalClause]
      cases b
      · exact ih2 hg
      · exact ih1 hg
  | abort_discontinue => cases hg
  | abort_branch _ _ => cases hg
  | unr_any _ => cases hg

theorem evalClause_abort {cl : Clause} (hcl : ClauseTyped .abortDiscontinue cl)
    (runNormal runUnwind : ResState → ResState) (s : ResState) :
    evalClause runNormal runUnwind cl s = runUnwind s := by
  generalize hg : OpGrade.abortDiscontinue = g at hcl
  induction hcl with
  | lin_continue => cases hg
  | lin_branch _ _ => cases hg
  | abort_discontinue => rfl
  | @abort_branch b _ _ _ _ ih1 ih2 =>
      simp only [evalClause]
      cases b
      · exact ih2 hg
      · exact ih1 hg
  | unr_any _ => cases hg

/-- Any unrestricted clause preserves `.consumed` when both `runNormal` and `runUnwind` do. -/
theorem evalClause_preserves_consumed (cl : Clause)
    (runNormal runUnwind : ResState → ResState)
    (hN : ∀ s, PhaseMatches .consumed s → PhaseMatches .consumed (runNormal s))
    (hU : ∀ s, PhaseMatches .consumed s → PhaseMatches .consumed (runUnwind s))
    (s : ResState) (hs : PhaseMatches .consumed s) :
    PhaseMatches .consumed (evalClause runNormal runUnwind cl s) := by
  induction cl generalizing s with
  | dropK => exact hs
  | continueOnce => exact hN s hs
  | discontinueOnce => exact hU s hs
  | continueTwice => exact hN _ (hN s hs)
  | branch b c1 c2 ih1 ih2 =>
      simp only [evalClause]
      cases b
      · exact ih2 s hs
      · exact ih1 s hs

/-- Inductive soundness theorem for `Typed`:
    evaluating any well-typed computation under a grade-conforming handler clause and
    valid normal/unwind continuations terminates in `.consumed` (zero faults, `consumes = 1`). -/
theorem typed_eval_sound
    {g : OpGrade} {cl : Clause} {c : Comp} {phIn : Phase} {hc : Bool} {phOut : Phase}
    (hcl : ClauseTyped g cl)
    (ht : Typed g phIn hc c phOut) :
    ∀ (kNormal kUnwind : ResState → ResState),
      NormalCont phOut kNormal →
      UnwindCont hc kUnwind →
      ∀ s, PhaseMatches phIn s →
        PhaseMatches .consumed (evalComp cl c kNormal kUnwind s) := by
  induction ht with
  | pure =>
      intro kN _ hkN _ s hs
      exact hkN s hs
  | acquire _ ih =>
      intro kN kU hkN hkU s hs
      simp only [evalComp]
      rcases hs with ⟨hf, _, hc0⟩
      exact ih kN kU hkN hkU s.acquire ⟨hf, rfl, hc0⟩
  | consume _ ih =>
      intro kN kU hkN hkU s hs
      simp only [evalComp]
      rcases hs with ⟨hf, ha, hc0⟩
      have hs' : PhaseMatches .consumed s.consume := by
        refine ⟨?_, ha, by simp [ResState.consume, hc0]⟩
        simp [ResState.consume, hf, hc0]
      exact ih kN kU hkN hkU s.consume hs'
  | perform_lin heq _ ih =>
      intro kN kU hkN hkU s hs
      subst heq
      simp only [evalComp]
      rw [evalClause_lin hcl]
      exact ih kN kU hkN hkU s hs
  | perform_abort_live heq _ _ =>
      intro kN kU _ hkU s hs
      subst heq
      simp only [evalComp]
      rw [evalClause_abort hcl]
      exact hkU s hs
  | perform_abort_consumed heq _ _ =>
      intro kN kU _ hkU s hs
      subst heq
      simp only [evalComp]
      rw [evalClause_abort hcl]
      exact hkU s hs
  | perform_unr_consumed heq _ ih =>
      intro kN kU hkN hkU s hs
      subst heq
      simp only [evalComp]
      exact evalClause_preserves_consumed cl _ kU (ih kN kU hkN hkU) hkU s hs
  | withFinally_cleanup _ _ ihBody ihClean =>
      intro kN kU hkN hkU s hs
      simp only [evalComp]
      have hkN' : NormalCont .live (fun st => evalComp cl _ kN kU st) :=
        fun st hst => ihClean kN kU hkN hkU st hst
      have hkU' : UnwindCont true (fun st => evalComp cl _ kU kU st) :=
        fun st hst => ihClean kU kU hkU hkU st hst
      exact ihBody _ _ hkN' hkU' s hs
  | @branch b _ _ _ _ _ _ _ ih1 ih2 =>
      intro kN kU hkN hkU s hs
      simp only [evalComp]
      cases b
      · exact ih2 kN kU hkN hkU s hs
      · exact ih1 kN kU hkN hkU s hs

/-- Main Soundness Corollary (Part c):
    Every well-typed program acquires and consumes the linear capability EXACTLY ONCE
    (`acquired = true`, `consumes = 1`, `faultDoubleConsume = false`). -/
theorem wellTypedProgram_exact_single_use (p : Program) (hwt : WellTypedProgram p) :
    (evalProgram p).acquired = true ∧
    (evalProgram p).consumes = 1 ∧
    (evalProgram p).faultDoubleConsume = false := by
  have hInit : PhaseMatches .unacquired ResState.init := ⟨rfl, rfl, rfl⟩
  have hIdN : NormalCont .consumed id := fun _ hs => hs
  have hIdU : UnwindCont false id := fun _ hs => hs
  have hRes := typed_eval_sound hwt.clauseOk hwt.bodyOk id id hIdN hIdU ResState.init hInit
  rcases hRes with ⟨hf, ha, hc⟩
  exact ⟨ha, hc, hf⟩

/-! ### Static Rejection Witnesses & Positive Well-Typed Examples -/

/-- The control-flow-linear type system statically rejects `twoShotProgram`. -/
theorem twoShotProgram_rejected : ¬ WellTypedProgram twoShotProgram := by
  intro hwt
  have hbody := hwt.bodyOk
  cases hbody with
  | acquire hlive =>
      cases hlive with
      | perform_lin h => cases h

/-- The control-flow-linear type system statically rejects `zeroShotDropProgram`. -/
theorem zeroShotDropProgram_rejected : ¬ WellTypedProgram zeroShotDropProgram := by
  intro hwt
  have hbody := hwt.bodyOk
  cases hbody with
  | acquire hlive =>
      cases hlive with
      | perform_lin h => cases h

/-- Positive example 1: One-shot control-flow-linear handler (`lin`) around `valueLinearBody`. -/
def oneShotLinearProgram : Program :=
  { grade := .lin, clause := .continueOnce, body := valueLinearBody }

theorem oneShotLinearProgram_wellTyped : WellTypedProgram oneShotLinearProgram :=
  { clauseOk := .lin_continue
    bodyOk := .acquire (.perform_lin rfl (.consume .pure)) }

/-- Positive example 2: 0-shot abortive handler with explicit `discontinue` + `withFinally`. -/
def abortDiscontinueProgram : Program :=
  { grade := .abortDiscontinue
    clause := .discontinueOnce
    body := .acquire (.withFinally (.consume .pure) (.perform .pure)) }

theorem abortDiscontinueProgram_wellTyped : WellTypedProgram abortDiscontinueProgram :=
  { clauseOk := .abort_discontinue
    bodyOk := .acquire (.withFinally_cleanup (.perform_abort_live rfl .pure) (.consume .pure)) }

/-- Positive example 3: Unrestricted 2-shot handler AFTER the linear capability is consumed. -/
def twoShotAfterConsumeProgram : Program :=
  { grade := .unr
    clause := .continueTwice
    body := .acquire (.consume (.perform .pure)) }

theorem twoShotAfterConsumeProgram_wellTyped : WellTypedProgram twoShotAfterConsumeProgram :=
  { clauseOk := .unr_any .continueTwice
    bodyOk := .acquire (.consume (.perform_unr_consumed rfl .pure)) }

end Toy.LinearEffects
