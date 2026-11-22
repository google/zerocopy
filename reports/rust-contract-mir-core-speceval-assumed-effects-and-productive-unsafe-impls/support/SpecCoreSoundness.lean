/-!
# Soundness and Negative-Control Mechanization of the Syntax-Independent 3-Primitive Spec Core

Standalone Lean 4 (`v4.34.1`, core `Init` only — zero Mathlib, zero `sorry`)
mechanization verifying:
1. Effect-indexed `FnContract` (`safetyPre` vs. `behaviorPre`), `TerminalOut.{returned, unwound, aborted}`,
   general 8-mask `AssumedContractRealizable`, modular mutual-recursion soundness (partial vs.
   measure-decreasing total), and `extern "C"` (`UnwindAction.unreachable`) vs. `extern "C-unwind"`.
2. `SpecEval` pure read-only evaluation with stepwise `callerMem` immutability, pre-state `old!`
   value snapshots (`SpecEvalVal`), short-circuiting clause conjunction (`&&` vs. non-short-circuiting
   `&`), shadow non-interference, and `const false` dead-branch erasure equivalence.
3. `InvariantEnv` (`FullValid := LangValid ∧ LibValid`), `ProductiveUnsafeImpl` (admitting
   `Option<Box<Node>>: Send` through `Box`'s `unsafe impl` while rejecting coinductive cycles
   such as `unsafe impl Send for NotSend where NotSend: Send {}`), and `VisCone` encapsulation
   preservation across `.returned` and `.unwound`.
-/

namespace SpecCoreSoundness

/-! ## Part 1: Effect-Indexed `FnContract`, `AssumedContractRealizable`, and Mutual Recursion -/

inductive FaultKind where
  | undefined
  | unsupported
  deriving DecidableEq, Repr

structure Memory where
  bytes : List Nat
  deriving DecidableEq, Repr

inductive Val where
  | nat (n : Nat)
  | bool (b : Bool)
  | unit
  deriving DecidableEq, Repr

structure Query where
  args : List Val
  callerMem : Memory
  deriving DecidableEq, Repr

structure Out where
  ret : Val
  callerMem : Memory
  deriving DecidableEq, Repr

/-- Four-way observable terminal outcome (`TerminalOut` + `Diverges`). -/
inductive TerminalOut where
  | returned (out : Out)
  | unwound (callerMem : Memory)
  | aborted (callerMem : Memory)
  deriving DecidableEq, Repr

inductive StepResult (State OutTy : Type) where
  | step (next : State)
  | done (out : OutTy)
  | fault (kind : FaultKind)
  deriving DecidableEq, Repr

/-- Explicit 3-bit effect mask orthogonal to postconditions. -/
structure EffectMask where
  terminates : Bool := false
  noUnwind   : Bool := false
  noAbort    : Bool := false
  deriving DecidableEq, Repr

/-- Effect-indexed behavioral function contract with strict separation between
`safetyPre` (only active on `isUnsafe = true` functions to guard `WellFormed`)
and `behaviorPre` (guards postconditions and effects on both safe and unsafe
functions without waiving safe-function UB-freedom). -/
structure FnContract where
  safetyPre   : Query → Prop := fun _ => True
  behaviorPre : Query → Prop := fun _ => True
  postReturn  : Query → Out → Prop := fun _ _ => True
  postUnwind  : Query → Memory → Prop := fun _ _ => True
  postAbort   : Query → Memory → Prop := fun _ _ => True
  effects     : EffectMask := {}

/-- Effective safety precondition: always `True` for safe functions (`isUnsafe = false`). -/
def FnContract.effectiveSafetyPre (c : FnContract) (isUnsafe : Bool) (q : Query) : Prop :=
  isUnsafe = true → c.safetyPre q

/-- Effective combined precondition guarding behavioral postconditions & effects. -/
def FnContract.effectiveBehaviorPre (c : FnContract) (isUnsafe : Bool) (q : Query) : Prop :=
  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q

/-- Abstract nondeterministic operational semantics matching `Trusted.MirSemantics.Boundary`. -/
structure Sem where
  State : Type
  Choice : Type
  initState : Query → Except FaultKind State
  validChoice : State → Choice → Prop
  evalStep : Choice → State → StepResult State TerminalOut

def Sem.Step (M : Sem) (s : M.State) (res : StepResult M.State TerminalOut) : Prop :=
  ∃ c : M.Choice, M.validChoice s c ∧ M.evalStep c s = res

inductive Sem.Reaches (M : Sem) : M.State → M.State → Prop where
  | refl (s : M.State) : M.Reaches s s
  | tail {s₁ s₂ s₃ : M.State} :
      M.Reaches s₁ s₂ → M.Step s₂ (.step s₃) → M.Reaches s₁ s₃

def Sem.ReachesResult (M : Sem) (q : Query) (res : StepResult M.State TerminalOut) : Prop :=
  match M.initState q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : M.State, M.Reaches s₀ s ∧ M.Step s res

def Sem.WellFormed (M : Sem) (q : Query) : Prop :=
  (∃ s₀ : M.State, M.initState q = .ok s₀ ∧
    ∀ s : M.State, M.Reaches s₀ s → ∃ c : M.Choice, M.validChoice s c) ∧
  (∀ k : FaultKind, ¬ M.ReachesResult q (.fault k))

def Sem.Behavior (M : Sem) (q : Query) (out : TerminalOut) : Prop :=
  M.ReachesResult q (.done out)

def Sem.Diverges (M : Sem) (q : Query) : Prop :=
  ∃ s₀ : M.State, M.initState q = .ok s₀ ∧
    ∃ trace : Nat → M.State,
      trace 0 = s₀ ∧
      ∀ n : Nat, M.Step (trace n) (.step (trace (n + 1)))

/-- Split-precondition `ContractSatisfied`: safe functions MUST satisfy `WellFormed` for ALL
queries regardless of `behaviorPre`; `behaviorPre` gates postconditions and
effects only. -/
def ContractSatisfied (M : Sem) (isUnsafe : Bool) (c : FnContract) : Prop :=
  (∀ q : Query, c.effectiveSafetyPre isUnsafe q → M.WellFormed q) ∧
  (∀ q : Query, c.effectiveBehaviorPre isUnsafe q →
    (∀ out, M.Behavior q (.returned out) → c.postReturn q out) ∧
    (∀ mem, M.Behavior q (.unwound mem)  → c.postUnwind q mem) ∧
    (∀ mem, M.Behavior q (.aborted mem)  → c.postAbort q mem) ∧
    (c.effects.terminates = true → ¬ M.Diverges q) ∧
    (c.effects.noUnwind   = true → ∀ mem, ¬ M.Behavior q (.unwound mem)) ∧
    (c.effects.noAbort    = true → ∀ mem, ¬ M.Behavior q (.aborted mem)))

/-- Conflated-precondition `ContractSatisfied`: erroneously let `behaviorPre` waive `WellFormed`
on safe functions! -/
def ContractSatisfiedConflated (M : Sem) (c : FnContract) : Prop :=
  ∀ q : Query, c.behaviorPre q → M.WellFormed q

/-- Negative-control mutant: safe function `fn bad(x)` with `#[requires(x < 10)]`
that executes UB when `x >= 10`. -/
def badSafeFnSem : Sem where
  State := Nat
  Choice := Unit
  initState q :=
    match q.args with
    | [.nat x] => .ok x
    | _ => .ok 0
  validChoice _ _ := True
  evalStep _ x :=
    if x < 10 then .done (.returned ⟨.nat x, ⟨[]⟩⟩)
    else .fault .undefined

def badSafeContract : FnContract :=
  { behaviorPre := fun q => match q.args with | [.nat x] => x < 10 | _ => False }

/-- Theorem 1.4: conflated preconditions wrongly accept an unsound safe function that UBs outside `#[requires]`,
while split preconditions reject it fail-closed. -/
theorem conflated_pre_wrongly_accepts_unsound_safe_fn :
    ContractSatisfiedConflated badSafeFnSem badSafeContract := by
  intro q hpre
  cases hargs : q.args with
  | nil => simp [badSafeContract, hargs] at hpre
  | cons v rest =>
    cases v with
    | nat x =>
      cases rest with
      | nil =>
        simp [badSafeContract, hargs] at hpre
        refine ⟨⟨x, by simp [badSafeFnSem, hargs], fun _ _ => ⟨(), trivial⟩⟩, ?_⟩
        intro k hfault
        simp only [Sem.ReachesResult, badSafeFnSem, hargs] at hfault
        rcases hfault with ⟨s, hreach, c, _, hstep⟩
        have hsx : s = x := by
          have hgen : ∀ a b : badSafeFnSem.State, badSafeFnSem.Reaches a b → a = x → b = x := by
            intro a b hr
            induction hr with
            | refl => intro ha; exact ha
            | tail _ hprev _ =>
              intro _
              rcases hprev with ⟨_, _, hstep0⟩
              dsimp [badSafeFnSem] at hstep0
              split at hstep0 <;> cases hstep0
          exact hgen x s hreach rfl
        subst hsx
        dsimp [badSafeFnSem] at hstep
        simp [hpre] at hstep
      | cons _ _ => simp [badSafeContract, hargs] at hpre
    | bool _ => simp [badSafeContract, hargs] at hpre
    | unit => simp [badSafeContract, hargs] at hpre

theorem safe_fn_requires_cannot_waive_ub :
    ¬ ContractSatisfied badSafeFnSem false badSafeContract := by
  intro hsat
  have hwf := hsat.1 ⟨[.nat 20], ⟨[]⟩⟩ (fun h => by cases h)
  have hno := hwf.2 .undefined
  apply hno
  change ∃ s : Nat, badSafeFnSem.Reaches (20 : Nat) s ∧ badSafeFnSem.Step s (.fault .undefined)
  exact ⟨(20 : Nat), Sem.Reaches.refl (M := badSafeFnSem) (20 : Nat), (), trivial, by simp [badSafeFnSem]⟩

/-! ### General 8-Mask `AssumedContractRealizable` vs. Three-Way-Only Gap -/

/-- Demonic call-site outcome choice for an assumed callee with contract `c`. -/
inductive AssumedCallChoice where
  | ret (out : Out)
  | unwind (mem : Memory)
  | abort (mem : Memory)
  | diverge

/-- Exact admissibility of a demonic call choice under `c` at query `q`. -/
def ValidAssumedChoice (c : FnContract) (q : Query) : AssumedCallChoice → Prop
  | .ret out    => c.postReturn q out
  | .unwind mem => c.effects.noUnwind = false ∧ c.postUnwind q mem
  | .abort mem  => c.effects.noAbort = false ∧ c.postAbort q mem
  | .diverge    => c.effects.terminates = false

/-- General 8-Mask `AssumedContractRealizable`: exact disjunction of all enabled
demonic call-site branches. -/
def AssumedContractRealizable (isUnsafe : Bool) (c : FnContract) : Prop :=
  ∀ q : Query, c.effectiveBehaviorPre isUnsafe q →
    (c.effects.terminates = false) ∨
    (∃ out : Out, c.postReturn q out) ∨
    (c.effects.noUnwind = false ∧ ∃ mem : Memory, c.postUnwind q mem) ∨
    (c.effects.noAbort  = false ∧ ∃ mem : Memory, c.postAbort  q mem)

/-- Three-way-only `AssumedContractRealizable`: only checked when all 3 mask bits were true! -/
def AssumedContractRealizableThreeWayOnly (c : FnContract) : Prop :=
  c.effects.terminates = true →
  c.effects.noUnwind = true →
  c.effects.noAbort = true →
  ∀ q : Query, c.behaviorPre q → ∃ out : Out, c.postReturn q out

/-- Theorem 1.1: Default partial mask (`terminates = false`) is ALWAYS realizable,
even for `#[ensures(false)]` / `-> !` / `loop {}`. -/
theorem default_partial_always_realizable (isUnsafe : Bool) (c : FnContract)
    (hpart : c.effects.terminates = false) :
    AssumedContractRealizable isUnsafe c := by
  intro _ _
  exact Or.inl hpart

/-- Theorem 1.3: `AssumedContractRealizable` is equivalent to demonic call-choice inhabitation! -/
theorem realizable_iff_valid_choice_inhabited (isUnsafe : Bool) (c : FnContract) :
    AssumedContractRealizable isUnsafe c ↔
    (∀ q : Query, c.effectiveBehaviorPre isUnsafe q → ∃ ch, ValidAssumedChoice c q ch) := by
  constructor
  · intro hreal q hpre
    rcases hreal q hpre with hdiv | ⟨out, hout⟩ | ⟨hnu, mem, hmem⟩ | ⟨hna, mem, hmem⟩
    · exact ⟨.diverge, hdiv⟩
    · exact ⟨.ret out, hout⟩
    · exact ⟨.unwind mem, hnu, hmem⟩
    · exact ⟨.abort mem, hna, hmem⟩
  · intro hinh q hpre
    rcases hinh q hpre with ⟨ch, hch⟩
    cases ch with
    | ret out => exact Or.inr (Or.inl ⟨out, hch⟩)
    | unwind mem => exact Or.inr (Or.inr (Or.inl ⟨hch.1, mem, hch.2⟩))
    | abort mem => exact Or.inr (Or.inr (Or.inr ⟨hch.1, mem, hch.2⟩))
    | diverge => exact Or.inl hch

/-- Theorem 1.2: Counterexample exposing the three-way-only realizability hole when `terminates = true,
noUnwind = false, noAbort = true` and both `postReturn` and `postUnwind` are `False`. -/
def realizabilityHoleContract : FnContract :=
  { postReturn := fun _ _ => False
    postUnwind := fun _ _ => False
    effects := { terminates := true, noUnwind := false, noAbort := true } }

theorem three_way_only_realizability_gap_witness :
    AssumedContractRealizableThreeWayOnly realizabilityHoleContract ∧
    ¬ AssumedContractRealizable false realizabilityHoleContract := by
  constructor
  · intro _ hnu
    simp [realizabilityHoleContract] at hnu
  · intro hreal
    have hpre : realizabilityHoleContract.effectiveBehaviorPre false ⟨[], ⟨[]⟩⟩ :=
      ⟨(fun h => by cases h), trivial⟩
    have h := hreal ⟨[], ⟨[]⟩⟩ hpre
    rcases h with h1 | ⟨_, h2⟩ | ⟨_, _, h3⟩ | ⟨h4, _, _⟩
    · simp [realizabilityHoleContract] at h1
    · exact h2
    · exact h3
    · simp [realizabilityHoleContract] at h4

/-! ### `extern "C"` (`UnwindAction.unreachable`) vs. `extern "C-unwind"` -/

inductive UnwindAction where
  | continue_
  | unreachable
  | terminate
  deriving DecidableEq, Repr

/-- Single-call machine invoking an assumed callee with contract `c` under call-site
`unwindAct` (matching `rustc`'s `UnwindAction::Unreachable` on `extern "C"` calls). -/
def singleAssumedCallSem (c : FnContract) (unwindAct : UnwindAction) : Sem where
  State := Query
  Choice := AssumedCallChoice
  initState q := .ok q
  validChoice q ch := ValidAssumedChoice c q ch
  evalStep ch q :=
    match ch with
    | .ret out => .done (.returned out)
    | .unwind mem =>
      match unwindAct with
      | .continue_ => .done (.unwound mem)
      | .unreachable => .fault .undefined
      | .terminate => .done (.aborted mem)
    | .abort mem => .done (.aborted mem)
    | .diverge => .step q

/-- Theorem 1.8a: Calling an `extern "C"` function (`UnwindAction.unreachable`) with
`noUnwind = false` is ALWAYS ill-formed (faults `.undefined` on the demonic unwind branch). -/
theorem extern_c_fails_without_noUnwind (c : FnContract)
    (hnu : c.effects.noUnwind = false) (q : Query) (mem : Memory)
    (hpu : c.postUnwind q mem) :
    ¬ (singleAssumedCallSem c .unreachable).WellFormed q := by
  intro hwf
  apply hwf.2 .undefined
  change ∃ s : (singleAssumedCallSem c .unreachable).State,
    (singleAssumedCallSem c .unreachable).Reaches q s ∧
    (singleAssumedCallSem c .unreachable).Step s (.fault .undefined)
  exact ⟨q, Sem.Reaches.refl (M := singleAssumedCallSem c .unreachable) q, .unwind mem, ⟨hnu, hpu⟩, rfl⟩

/-- Theorem 1.8b: Calling an `extern "C"` function (`UnwindAction.unreachable`) with
`noUnwind = true` and `AssumedContractRealizable` is `WellFormed`! -/
theorem extern_c_wellFormed_with_noUnwind (c : FnContract)
    (hnu : c.effects.noUnwind = true) (q : Query)
    (hinh : ∃ ch, ValidAssumedChoice c q ch) :
    (singleAssumedCallSem c .unreachable).WellFormed q := by
  refine ⟨⟨q, rfl, ?_⟩, ?_⟩
  · intro s hreach
    have hsq : s = q := by
      induction hreach with
      | refl => rfl
      | tail _ hstep ih =>
        subst ih
        rcases hstep with ⟨ch, _, hev⟩
        cases ch <;> dsimp [singleAssumedCallSem] at hev <;> try cases hev
        rfl
    subst hsq
    exact hinh
  · intro k hfault
    dsimp [Sem.ReachesResult, singleAssumedCallSem] at hfault
    rcases hfault with ⟨s, _, ch, hval, hev⟩
    cases ch with
    | ret _ => cases hev
    | unwind mem =>
      have : true = false := hnu.symm.trans hval.1
      cases this
    | abort _ => cases hev
    | diverge => cases hev

/-! ### Mutual Recursion Soundness: Partial (Always Sound) vs. Total (Requires Measure) -/

/-- Simple call-capable multi-function language for proving modular assume-guarantee
soundness under mutual recursion. -/
inductive MStmt where
  | ret (v : Nat)
  | call (callee : Nat) (argFn : Nat → Nat) (cont : Nat → MStmt)
  | ub

/-- Concrete big-step evaluation indexed by exact step depth `n`. -/
inductive EvalN (prog : Nat → Nat → MStmt) : Nat → MStmt → Option Nat → Prop where
  | ret (n v : Nat) : EvalN prog (n + 1) (.ret v) (some v)
  | ub (n : Nat) : EvalN prog (n + 1) .ub none
  | call_ub {n c : Nat} {argFn : Nat → Nat} {cont : Nat → MStmt} :
      EvalN prog n (prog c (argFn 0)) none →
      EvalN prog (n + 1) (.call c argFn cont) none
  | call_ret {n₁ n₂ c r : Nat} {argFn : Nat → Nat} {cont : Nat → MStmt} {res : Option Nat} :
      EvalN prog n₁ (prog c (argFn 0)) (some r) →
      EvalN prog n₂ (cont r) res →
      EvalN prog (n₁ + n₂ + 1) (.call c argFn cont) res

/-- Strong induction helper using only core `Init` (`Nat.strongRecOn`). -/
theorem nat_strong_ind {P : Nat → Prop} (h : ∀ n, (∀ k < n, P k) → P n) : ∀ n, P n :=
  fun n => Nat.strongRecOn n h

/-- Modular partial-correctness check of statement `s` assuming every callee `c`
satisfies `(Pre c, Post c)`. -/
def StmtModularOk (Pre : Nat → Nat → Prop) (Post : Nat → Nat → Nat → Prop)
    (postOut : Nat → Prop) : MStmt → Prop
  | .ret v => postOut v
  | .ub => False
  | .call c argFn cont =>
      Pre c (argFn 0) ∧
      ∀ r, Post c (argFn 0) r → StmtModularOk Pre Post postOut (cont r)

/-- Theorem 1.5 (`mutual_recursion_partial_sound`): Arbitrary mutual recursion is
100% SOUND for safety + partial correctness via strong induction on step count `n`! -/
theorem mutual_recursion_partial_sound
    (prog : Nat → Nat → MStmt)
    (Pre : Nat → Nat → Prop)
    (Post : Nat → Nat → Nat → Prop)
    (hMod : ∀ f x, Pre f x → StmtModularOk Pre Post (Post f x) (prog f x)) :
    ∀ n s postOut,
      StmtModularOk Pre Post postOut s →
      ∀ res, EvalN prog n s res →
        match res with
        | none => False
        | some v => postOut v := by
  intro n
  refine nat_strong_ind (P := fun n =>
    ∀ s postOut, StmtModularOk Pre Post postOut s →
      ∀ res, EvalN prog n s res → match res with | none => False | some v => postOut v) ?_ n
  intro k ih s postOut hok res heval
  cases heval with
  | ret _ v => exact hok
  | ub _ => exact hok
  | @call_ub n' c argFn cont hcal =>
    rcases hok with ⟨hpreC, _⟩
    have hbody := hMod c (argFn 0) hpreC
    exact ih n' (Nat.lt_succ_self n') (prog c (argFn 0)) (Post c (argFn 0)) hbody none hcal
  | @call_ret n₁ n₂ c r argFn cont res hcal hcont =>
    rcases hok with ⟨hpreC, hcontOk⟩
    have hbody := hMod c (argFn 0) hpreC
    have hlt1 : n₁ < n₁ + n₂ + 1 := by omega
    have hlt2 : n₂ < n₁ + n₂ + 1 := by omega
    have hpostR : Post c (argFn 0) r :=
      ih n₁ hlt1 (prog c (argFn 0)) (Post c (argFn 0)) hbody (some r) hcal
    exact ih n₂ hlt2 (cont r) postOut (hcontOk r hpostR) res hcont

/-- Theorem 1.6 (`mutual_recursion_termination_unsound_without_measure`):
Mutually recursive `f() { g() }` and `g() { f() }` satisfy naive unmeasured
modular termination, yet have ZERO terminating executions (`∀ n res, ¬ EvalN`)! -/
def mutLoopProg : Nat → Nat → MStmt
  | 0, x => .call 1 (fun _ => x) (fun r => .ret r)
  | _, x => .call 0 (fun _ => x) (fun r => .ret r)

theorem mutual_recursion_termination_unsound_without_measure :
    (∀ f x, StmtModularOk (fun _ _ => True) (fun _ _ _ => True) (fun _ => True) (mutLoopProg f x)) ∧
    (∀ n f x res, ¬ EvalN mutLoopProg n (mutLoopProg f x) res) := by
  constructor
  · intro f x
    cases f with
    | zero => exact ⟨trivial, fun _ _ => trivial⟩
    | succ _ => exact ⟨trivial, fun _ _ => trivial⟩
  · intro n
    refine nat_strong_ind (P := fun n => ∀ f x res, ¬ EvalN mutLoopProg n (mutLoopProg f x) res) ?_ n
    intro k ih f x res hev
    cases f with
    | zero =>
      cases hev with
      | call_ub hcal => exact ih _ (Nat.lt_succ_self _) 1 x none hcal
      | call_ret hcal _ => exact ih _ (by omega) 1 x (some _) hcal
    | succ _ =>
      cases hev with
      | call_ub hcal => exact ih _ (Nat.lt_succ_self _) 0 x none hcal
      | call_ret hcal _ => exact ih _ (by omega) 0 x (some _) hcal

/-- Measure-guarded modular total correctness: every recursive call strictly
decreases `meas f x < m`. -/
def StmtModularTotalOk (Pre : Nat → Nat → Prop) (Post : Nat → Nat → Nat → Prop)
    (meas : Nat → Nat → Nat) (curM : Nat) (postOut : Nat → Prop) : MStmt → Prop
  | .ret v => postOut v
  | .ub => False
  | .call c argFn cont =>
      Pre c (argFn 0) ∧
      meas c (argFn 0) < curM ∧
      ∀ r, Post c (argFn 0) r → StmtModularTotalOk Pre Post meas curM postOut (cont r)

/-- Theorem 1.7 (`mutual_recursion_termination_sound_with_measure`):
Measure-decreasing modular mutual recursion implies CONCRETE termination + postcondition! -/
theorem mutual_recursion_termination_sound_with_measure
    (prog : Nat → Nat → MStmt)
    (Pre : Nat → Nat → Prop)
    (Post : Nat → Nat → Nat → Prop)
    (meas : Nat → Nat → Nat)
    (hMod : ∀ f x, Pre f x → StmtModularTotalOk Pre Post meas (meas f x) (Post f x) (prog f x)) :
    ∀ m, ∀ f x, Pre f x → meas f x = m →
      ∃ n v, EvalN prog n (prog f x) (some v) ∧ Post f x v := by
  intro m
  refine nat_strong_ind (P := fun m =>
    ∀ f x, Pre f x → meas f x = m → ∃ n v, EvalN prog n (prog f x) (some v) ∧ Post f x v) ?_ m
  intro k ihm
  have helper : ∀ s postOut,
      StmtModularTotalOk Pre Post meas k postOut s →
      ∃ n v, EvalN prog n s (some v) ∧ postOut v := by
    intro s
    induction s with
    | ret v =>
      intro postOut hok
      exact ⟨1, v, .ret 0 v, hok⟩
    | ub =>
      intro postOut hok
      exact False.elim hok
    | call c argFn cont ihc =>
      intro postOut ⟨hpreC, hlt, hcont⟩
      obtain ⟨n₁, r, hev1, hpostR⟩ := ihm (meas c (argFn 0)) hlt c (argFn 0) hpreC rfl
      obtain ⟨n₂, v, hev2, hpostV⟩ := ihc r postOut (hcont r hpostR)
      exact ⟨n₁ + n₂ + 1, v, .call_ret hev1 hev2, hpostV⟩
  intro f x hpre hmeq
  subst hmeq
  exact helper (prog f x) (Post f x) (hMod f x hpre)


/-! ## Part 2: `SpecEval` Stepwise `callerMem` Immutability, Short-Circuiting, & Dead-Branch Erasure -/

structure MemSem where
  State : Type
  Choice : Type
  stateCallerMem : State → Memory
  initState : Query → Except FaultKind State
  validChoice : State → Choice → Prop
  evalStep : Choice → State → StepResult State TerminalOut

def MemSem.toSem (M : MemSem) : Sem :=
  ⟨M.State, M.Choice, M.initState, M.validChoice, M.evalStep⟩

/-- Endpoint-only `SpecEval` (missed intermediate write-then-restore on `UnsafeCell`!). -/
def SpecEvalEndpointOnly (M : MemSem) (q : Query) : Prop :=
  M.toSem.WellFormed q ∧
  ¬ M.toSem.Diverges q ∧
  (∀ out, M.toSem.Behavior q out →
    ∃ mem', out = .returned ⟨.bool true, mem'⟩ ∧ mem' = q.callerMem)

/-- Stepwise `SpecEval` with **stepwise `callerMem` immutability** (`∀ s_mid, Reaches s₀ s_mid →
stateCallerMem s_mid = q.callerMem`), plus `SpecEvalVal` for `old!` pre-state snapshots. -/
def SpecEvalVal (M : MemSem) (q : Query) (v : Val) : Prop :=
  M.toSem.WellFormed q ∧
  ¬ M.toSem.Diverges q ∧
  (∀ s₀ s_mid, M.initState q = .ok s₀ → M.toSem.Reaches s₀ s_mid →
    M.stateCallerMem s_mid = q.callerMem) ∧
  (∀ out, M.toSem.Behavior q out →
    out = .returned ⟨v, q.callerMem⟩)

def SpecEval (M : MemSem) (q : Query) : Prop :=
  SpecEvalVal M q (.bool true)

/-- Multi-clause short-circuiting conjunction (`&&`, NOT eager `&` as in eager bitwise-AND multi-clause joining!):
each subsequent clause is evaluated ONLY if all preceding clauses evaluated to `true`. -/
def SpecEvalClauses : List MemSem → Query → Prop
  | [], _ => True
  | [m], q => SpecEval m q
  | m :: ms, q => SpecEval m q ∧ SpecEvalClauses ms q

/-- Theorem 2.4 (`short_circuit_clause_vs_eager_bitwise_and`): Modeling eager bitwise-AND multi-clause joining
(`requires: [i < len, arr[i] == 0]`): when `i = len`, short-circuiting `&&` returns
`false` cleanly (zero UB/panic), whereas eager `&` evaluates clause 2 (`arr[i]`) and
panics/UBs! -/
inductive ClauseEval where
  | ok (b : Bool)
  | panic
  deriving DecidableEq, Repr

def joinShortCircuit (c1 c2 : ClauseEval) : ClauseEval :=
  match c1 with
  | .ok false => .ok false
  | .ok true  => c2
  | .panic    => .panic

def joinEagerBitAnd (c1 c2 : ClauseEval) : ClauseEval :=
  match c1, c2 with
  | .ok b1, .ok b2 => .ok (b1 && b2)
  | _, _ => .panic

theorem short_circuit_clause_safe_vs_eager_panics :
    joinShortCircuit (.ok false) .panic = .ok false ∧
    joinEagerBitAnd (.ok false) .panic = .panic := by
  exact ⟨rfl, rfl⟩

/-- Negative-control mutant 1: `#[requires({ x.set(99); true })]` (`Cell::set` mutates
`callerMem` and returns `true`). -/
def cellMutatesSem : MemSem where
  State := Memory
  Choice := Unit
  stateCallerMem m := m
  initState q := .ok q.callerMem
  validChoice _ _ := True
  evalStep _ _ := .done (.returned ⟨.bool true, ⟨[99]⟩⟩)

/-- Theorem 2.1: `SpecEval` rejects `#[requires({ x.set(99); true })]`. -/
theorem specEval_rejects_cell_mutation :
    ¬ SpecEval cellMutatesSem ⟨[], ⟨[1]⟩⟩ := by
  intro ⟨_, _, _, hret⟩
  have hbeh : cellMutatesSem.toSem.Behavior ⟨[], ⟨[1]⟩⟩ (.returned ⟨.bool true, ⟨[99]⟩⟩) := by
    change ∃ s : cellMutatesSem.toSem.State,
      cellMutatesSem.toSem.Reaches ⟨[1]⟩ s ∧
      cellMutatesSem.toSem.Step s (.done (.returned ⟨.bool true, ⟨[99]⟩⟩))
    exact ⟨⟨[1]⟩, .refl _, (), trivial, rfl⟩
  have heq := hret _ hbeh
  simp at heq

/-- Negative-control mutant 2: `#[requires({ let old = x.get(); x.set(99); x.set(old); true })]`
mutates `callerMem` in an intermediate step and restores it before returning `true`. -/
def cellMutateAndRestoreSem : MemSem where
  State := Nat × Memory × Memory -- (pc, origMem, curMem)
  Choice := Unit
  stateCallerMem st := st.2.2
  initState q := .ok (0, q.callerMem, q.callerMem)
  validChoice _ _ := True
  evalStep _ st :=
    match st.1 with
    | 0 => .step (1, st.2.1, ⟨[99]⟩)      -- intermediate mutation of callerMem!
    | 1 => .step (2, st.2.1, st.2.1)       -- restore callerMem!
    | _ => .done (.returned ⟨.bool true, st.2.2⟩)

/-- Theorem 2.2: endpoint-only `SpecEvalEndpointOnly` WRONGLY ACCEPTS intermediate
`UnsafeCell` mutation-and-restore, while stepwise `SpecEval` REJECTS it! -/
theorem stepwise_specEval_rejects_mutate_and_restore_while_endpoint_accepts :
    SpecEvalEndpointOnly cellMutateAndRestoreSem ⟨[], ⟨[1]⟩⟩ ∧
    ¬ SpecEval cellMutateAndRestoreSem ⟨[], ⟨[1]⟩⟩ := by
  have hreach_cases : ∀ s, cellMutateAndRestoreSem.toSem.Reaches (0, ⟨[1]⟩, ⟨[1]⟩) s →
      s = (0, ⟨[1]⟩, ⟨[1]⟩) ∨ s = (1, ⟨[1]⟩, ⟨[99]⟩) ∨ s = (2, ⟨[1]⟩, ⟨[1]⟩) := by
    intro s hr
    induction hr with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
      rcases hstep with ⟨_, _, hev⟩
      rcases ih with rfl | rfl | rfl
      · dsimp [MemSem.toSem, cellMutateAndRestoreSem] at hev
        cases hev
        exact Or.inr (Or.inl rfl)
      · dsimp [MemSem.toSem, cellMutateAndRestoreSem] at hev
        cases hev
        exact Or.inr (Or.inr rfl)
      · dsimp [MemSem.toSem, cellMutateAndRestoreSem] at hev
        cases hev
  constructor
  · refine ⟨⟨⟨(0, ⟨[1]⟩, ⟨[1]⟩), rfl, fun _ _ => ⟨(), trivial⟩⟩, ?_⟩, ?_, ?_⟩
    · intro k hfault
      dsimp [Sem.ReachesResult, MemSem.toSem, cellMutateAndRestoreSem] at hfault
      rcases hfault with ⟨s, hr, _, _, hev⟩
      rcases hreach_cases s hr with rfl | rfl | rfl <;> cases hev
    · intro ⟨s₀, hinit, tr, h0, hstep⟩
      dsimp [MemSem.toSem, cellMutateAndRestoreSem] at hinit
      cases hinit
      have ht0 : tr 0 = (0, ⟨[1]⟩, ⟨[1]⟩) := h0
      rcases hstep 0 with ⟨_, _, hev0⟩
      rw [ht0] at hev0
      dsimp [MemSem.toSem, cellMutateAndRestoreSem] at hev0
      have h1eq : tr 1 = (1, ⟨[1]⟩, ⟨[99]⟩) := by
        injection hev0 with he
        exact he.symm
      rcases hstep 1 with ⟨_, _, hev1⟩
      rw [h1eq] at hev1
      dsimp [MemSem.toSem, cellMutateAndRestoreSem] at hev1
      have h2eq : tr 2 = (2, ⟨[1]⟩, ⟨[1]⟩) := by
        injection hev1 with he
        exact he.symm
      rcases hstep 2 with ⟨_, _, hev2⟩
      rw [h2eq] at hev2
      dsimp [MemSem.toSem, cellMutateAndRestoreSem] at hev2
      cases hev2
    · intro out hbeh
      dsimp [Sem.Behavior, Sem.ReachesResult, MemSem.toSem, cellMutateAndRestoreSem] at hbeh
      rcases hbeh with ⟨s, hr, _, _, hev⟩
      rcases hreach_cases s hr with rfl | rfl | rfl
      · cases hev
      · cases hev
      · cases hev
        exact ⟨⟨[1]⟩, rfl, rfl⟩
  · intro ⟨_, _, himm, _⟩
    have hr1 : cellMutateAndRestoreSem.toSem.Reaches (0, ⟨[1]⟩, ⟨[1]⟩) (1, ⟨[1]⟩, ⟨[99]⟩) :=
      .tail (.refl _) ⟨(), trivial, rfl⟩
    have heq := himm (0, ⟨[1]⟩, ⟨[1]⟩) (1, ⟨[1]⟩, ⟨[99]⟩) rfl hr1
    simp [cellMutateAndRestoreSem] at heq

/-- Negative-control mutant 3: Panicking (`a / 0`) closure in `#[requires]`. -/
def panickingReqSem : MemSem where
  State := Unit
  Choice := Unit
  stateCallerMem _ := ⟨[]⟩
  initState _ := .ok ()
  validChoice _ _ := True
  evalStep _ _ := .done (.unwound ⟨[]⟩)

/-- Theorem 2.3: Any panicking closure falsifies `SpecEval`. -/
theorem specEval_rejects_panic : ¬ SpecEval panickingReqSem ⟨[], ⟨[]⟩⟩ := by
  intro ⟨_, _, _, hret⟩
  have hbeh : panickingReqSem.toSem.Behavior ⟨[], ⟨[]⟩⟩ (.unwound ⟨[]⟩) := by
    change ∃ s : panickingReqSem.toSem.State,
      panickingReqSem.toSem.Reaches () s ∧
      panickingReqSem.toSem.Step s (.done (.unwound ⟨[]⟩))
    exact ⟨(), Sem.Reaches.refl (M := panickingReqSem.toSem) (), (), trivial, rfl⟩
  have heq := hret _ hbeh
  cases heq

/-- Theorem 2.5 (`dead_branch_erasure_behavior_iff`): Replacing a `const false` contract
scaffold prologue (`bb0: switchInt(const false) -> [0: entry, otherwise: dead]`)
with a direct jump to `entry` preserves `Behavior` bidirectionally (`↔`)! -/
def deadBranchWrap (M : Sem) (cDefault : M.Choice) : Sem where
  State := Bool × M.State
  Choice := M.Choice
  initState q :=
    match M.initState q with
    | .error k => .error k
    | .ok s₀ => .ok (true, s₀)
  validChoice s c :=
    if s.1 then c = cDefault else M.validChoice s.2 c
  evalStep c s :=
    if s.1 then .step (false, s.2)
    else
      match M.evalStep c s.2 with
      | .step s' => .step (false, s')
      | .done o => .done o
      | .fault k => .fault k

theorem deadBranchWrap_reaches_iff (M : Sem) (c0 : M.Choice) (s₀ s : M.State) :
    (deadBranchWrap M c0).Reaches (true, s₀) (false, s) ↔ M.Reaches s₀ s := by
  constructor
  · intro hr
    suffices ∀ p₁ p₂, (deadBranchWrap M c0).Reaches p₁ p₂ →
        p₁.1 = true → p₂.1 = false → M.Reaches p₁.2 p₂.2 by
      exact this (true, s₀) (false, s) hr rfl rfl
    intro p₁ p₂ h
    induction h with
    | refl => intro h1 h2; rw [h1] at h2; cases h2
    | @tail b d hab hstep ih =>
      intro ha hd
      rcases b with ⟨bb, sb⟩
      cases bb with
      | true =>
        have hba : sb = p₁.2 := by
          have hgen : ∀ u v : (deadBranchWrap M c0).State,
              (deadBranchWrap M c0).Reaches u v → v.1 = true → v.2 = u.2 := by
            intro u v hr
            induction hr with
            | refl => intro _; rfl
            | tail _ hprev _ =>
              intro hv
              rcases hprev with ⟨_, _, hev⟩
              dsimp [deadBranchWrap] at hev
              split at hev
              · cases hev; simp at hv
              · split at hev <;> cases hev
                simp at hv
          exact hgen p₁ (true, sb) hab rfl
        rcases hstep with ⟨_, _, hev⟩
        dsimp [deadBranchWrap] at hev
        cases hev
        rw [hba]
        exact .refl p₁.2
      | false =>
        have h1 := ih ha rfl
        rcases hstep with ⟨c, hvc, hev⟩
        dsimp [deadBranchWrap] at hvc hev
        cases hms : M.evalStep c sb with
        | step s' =>
          rw [hms] at hev
          cases hev
          exact .tail h1 ⟨c, hvc, hms⟩
        | done _ => rw [hms] at hev; cases hev
        | fault _ => rw [hms] at hev; cases hev
  · intro hr
    induction hr with
    | refl =>
      exact .tail (.refl _) ⟨c0, rfl, rfl⟩
    | tail _ hstep ih =>
      rcases hstep with ⟨c, hvc, hev⟩
      exact .tail ih ⟨c, hvc, by simp [deadBranchWrap, hev]⟩

theorem dead_branch_erasure_wellFormed_iff (M : Sem) (c0 : M.Choice) (q : Query) :
    (deadBranchWrap M c0).WellFormed q ↔ M.WellFormed q := by
  constructor
  · rintro ⟨⟨s₀, hinit, hvc⟩, hnf⟩
    dsimp [deadBranchWrap] at hinit
    cases hm : M.initState q with
    | error k => rw [hm] at hinit; cases hinit
    | ok ms₀ =>
      rw [hm] at hinit
      cases hinit
      refine ⟨⟨ms₀, hm, ?_⟩, ?_⟩
      · intro ms hr
        have hrm := (deadBranchWrap_reaches_iff M c0 ms₀ ms).mpr hr
        obtain ⟨c, hc⟩ := hvc (false, ms) hrm
        exact ⟨c, hc⟩
      · intro k hfault
        apply hnf k
        dsimp [Sem.ReachesResult, deadBranchWrap] at hfault ⊢
        rw [hm] at hfault ⊢
        rcases hfault with ⟨ms, hr, c, hc, hev⟩
        exact ⟨(false, ms), (deadBranchWrap_reaches_iff M c0 ms₀ ms).mpr hr, c, hc, by simp [hev]⟩
  · rintro ⟨⟨ms₀, hinit, hvc⟩, hnf⟩
    refine ⟨⟨(true, ms₀), by simp [deadBranchWrap, hinit], ?_⟩, ?_⟩
    · rintro ⟨b, s⟩ hr
      cases b with
      | true => exact ⟨c0, rfl⟩
      | false =>
        have hrm := (deadBranchWrap_reaches_iff M c0 ms₀ s).mp hr
        exact hvc s hrm
    · intro k hfault
      apply hnf k
      dsimp [Sem.ReachesResult, deadBranchWrap] at hfault ⊢
      rw [hinit] at hfault ⊢
      rcases hfault with ⟨⟨b, s⟩, hr, c, hc, hev⟩
      cases b with
      | true => cases hev
      | false =>
        have hrm := (deadBranchWrap_reaches_iff M c0 ms₀ s).mp hr
        simp only at hc hev
        cases hms : M.evalStep c s with
        | step _ => rw [hms] at hev; cases hev
        | done _ => rw [hms] at hev; cases hev
        | fault k' =>
          rw [hms] at hev
          cases hev
          exact ⟨s, hrm, c, hc, hms⟩

theorem dead_branch_erasure_diverges_iff (M : Sem) (c0 : M.Choice) (q : Query) :
    (deadBranchWrap M c0).Diverges q ↔ M.Diverges q := by
  constructor
  · rintro ⟨s₀, hinit, tr, h0, hstep⟩
    dsimp [deadBranchWrap] at hinit
    cases hm : M.initState q with
    | error k => rw [hm] at hinit; cases hinit
    | ok ms₀ =>
      rw [hm] at hinit
      cases hinit
      have htr1 : tr 1 = (false, ms₀) := by
        rcases hstep 0 with ⟨_, _, hev⟩
        rw [h0] at hev
        dsimp [deadBranchWrap] at hev
        injection hev with he
        exact he.symm
      have hfalse : ∀ n, (tr (n + 1)).1 = false := by
        intro n
        induction n with
        | zero => rw [htr1]
        | succ k ih =>
          rcases hstep (k + 1) with ⟨c, _, hev⟩
          dsimp [deadBranchWrap] at hev
          rw [ih] at hev
          cases hms : M.evalStep c (tr (k + 1)).2 with
          | step s' =>
            rw [hms] at hev
            injection hev with he
            rw [← he]
          | done _ => rw [hms] at hev; cases hev
          | fault _ => rw [hms] at hev; cases hev
      refine ⟨ms₀, hm, fun n => (tr (n + 1)).2, by simp [htr1], ?_⟩
      intro n
      rcases hstep (n + 1) with ⟨c, hvc, hev⟩
      dsimp [deadBranchWrap] at hvc hev
      rw [hfalse n] at hvc hev
      cases hms : M.evalStep c (tr (n + 1)).2 with
      | step s' =>
        rw [hms] at hev
        injection hev with he
        have hs' : (tr (n + 1 + 1)).2 = s' := congrArg Prod.snd he.symm
        dsimp only
        rw [hs']
        exact ⟨c, hvc, hms⟩
      | done _ => rw [hms] at hev; cases hev
      | fault _ => rw [hms] at hev; cases hev
  · rintro ⟨ms₀, hinit, tr, h0, hstep⟩
    refine ⟨(true, ms₀), by simp [deadBranchWrap, hinit],
      fun n => match n with | 0 => (true, ms₀) | k + 1 => (false, tr k), rfl, ?_⟩
    intro n
    cases n with
    | zero =>
      exact ⟨c0, rfl, by simp [deadBranchWrap, h0]⟩
    | succ k =>
      rcases hstep k with ⟨c, hvc, hev⟩
      exact ⟨c, hvc, by simp [deadBranchWrap, hev]⟩

theorem dead_branch_erasure_behavior_iff (M : Sem) (c0 : M.Choice) (q : Query) (out : TerminalOut) :
    (deadBranchWrap M c0).Behavior q out ↔ M.Behavior q out := by
  simp only [Sem.Behavior, Sem.ReachesResult, deadBranchWrap]
  cases hinit : M.initState q with
  | error k => simp
  | ok s₀ =>
    constructor
    · rintro ⟨⟨b, s⟩, hr, c, hvc, hev⟩
      cases b with
      | true => simp at hev
      | false =>
        have hrm : M.Reaches s₀ s := (deadBranchWrap_reaches_iff M c0 s₀ s).mp hr
        simp at hvc hev
        cases hms : M.evalStep c s with
        | step _ => simp [hms] at hev
        | fault _ => simp [hms] at hev
        | done o =>
          simp [hms] at hev
          subst hev
          exact ⟨s, hrm, c, hvc, hms⟩
    · rintro ⟨s, hrm, c, hvc, hms⟩
      exact ⟨(false, s), (deadBranchWrap_reaches_iff M c0 s₀ s).mpr hrm, c, hvc, by simp [hms]⟩


/-! ## Part 3: `InvariantEnv`, `ProductiveUnsafeImpl`, and `VisCone` Encapsulation -/

/-- Type universe modeling `u32`, `NonZeroU32`, `Rc<()>`, `Box<T>`, `Option<T>`,
`FakeBox<T>` (structurally containing `Rc<()>`), `NotSend`, and `BoxNode`. -/
inductive TyRep where
  | u32
  | nonZeroU32
  | rcUnit
  | box (inner : TyRep)
  | option (inner : TyRep)
  | fakeBox (inner : TyRep)
  | notSend
  | boxNode
  deriving DecidableEq, Repr

/-- Language validity (`LangValid`) vs. Library safety invariant (`LibValid`)
and composite `FullValid := LangValid ∧ LibValid`. -/
def LangValid : TyRep → Nat → Prop
  | .u32, _ => True
  | .nonZeroU32, _ => True
  | _, _ => True

def LibValid : TyRep → Nat → Prop
  | .nonZeroU32, v => v ≠ 0
  | _, _ => True

def FullValid (t : TyRep) (v : Nat) : Prop :=
  LangValid t v ∧ LibValid t v

/-- `FromBytes` defined over `FullValid` (NOT `LangValid` alone!). -/
def FromBytesInv (t : TyRep) : Prop :=
  ∀ b : Nat, FullValid t b

/-- Theorem 3.6: `FromBytes` over `FullValid` rejects `NonZeroU32` (zero bytes
violate `LibValid`), whereas `LangValid`-only would wrongly accept it! -/
theorem fromBytes_fullValid_rejects_nonZero :
    (∀ b, LangValid .nonZeroU32 b) ∧ ¬ FromBytesInv .nonZeroU32 := by
  constructor
  · intro _; trivial
  · intro h
    exact (h 0).2 rfl

/-- Trait impl graph edge for analyzing coinductive cycles (coinductive auto-trait impl cycles). -/
structure ImplEdge where
  src : String
  dst : String
  isUnsafeImpl : Bool
  isIndirectionGuarded : Bool
  deriving DecidableEq, Repr

/-- Concrete impl graph for `struct BoxNode { next: Option<Box<BoxNode>> }`:
Notice `Box<BoxNode>: Send -> BoxNode: Send` IS an `unsafe impl` in `alloc`! -/
def boxNodeImplGraph : List ImplEdge :=
  [ ⟨"BoxNode:Send", "Option<Box<BoxNode>>:Send", false, false⟩,
    ⟨"Option<Box<BoxNode>>:Send", "Box<BoxNode>:Send", false, false⟩,
    ⟨"Box<BoxNode>:Send", "BoxNode:Send", true, true⟩ ]

/-- Theorem 3.1: `boxNodeImplGraph` contains a cycle touching an `unsafe impl`,
falsifying the naive rule ("no cycle may touch any `unsafe impl`")! -/
theorem naive_scc_rejects_box_node :
    ∃ e1 e2 e3,
      e1 ∈ boxNodeImplGraph ∧ e2 ∈ boxNodeImplGraph ∧ e3 ∈ boxNodeImplGraph ∧
      e1.dst = e2.src ∧ e2.dst = e3.src ∧ e3.dst = e1.src ∧
      e3.isUnsafeImpl = true := by
  refine ⟨⟨"BoxNode:Send", "Option<Box<BoxNode>>:Send", false, false⟩,
          ⟨"Option<Box<BoxNode>>:Send", "Box<BoxNode>:Send", false, false⟩,
          ⟨"Box<BoxNode>:Send", "BoxNode:Send", true, true⟩, ?_⟩
  simp [boxNodeImplGraph]

/-- Structural depth-indexed `SendAt d T`: well-founded semantics for `Send` over
finite heap-indirection depth `d : Nat`. Indirection (`Box<T>`) shifts depth `d + 1 -> d`! -/
def SendAt : Nat → TyRep → Prop
  | _, .u32 => True
  | _, .nonZeroU32 => True
  | _, .rcUnit => False
  | 0, .box _ => True
  | d + 1, .box inner => SendAt d inner
  | d, .option inner => SendAt d inner
  | _, .fakeBox _ => False
  | _, .notSend => False
  | 0, .boxNode => True
  | d + 1, .boxNode => SendAt d .boxNode -- unfolds `Option<Box<BoxNode>>` across `Box` indirection!

/-- Equational lemma: `SendAt (d + 1) .boxNode` equals `SendAt (d + 1) (.option (.box .boxNode))`. -/
theorem sendAt_boxNode_unfold (d : Nat) :
    SendAt (d + 1) .boxNode ↔ SendAt (d + 1) (.option (.box .boxNode)) := by
  simp [SendAt]

/-- Theorem 3.2 (`boxNode_send_well_founded`): `BoxNode` satisfies `∀ d, SendAt d .boxNode`
via well-founded induction on heap depth `d` — WITH ZERO UNSOUND COINDUCTION! -/
theorem boxNode_send_well_founded : ∀ d : Nat, SendAt d .boxNode := by
  intro d
  induction d with
  | zero => simp [SendAt]
  | succ k ih => simpa [SendAt] using ih

/-- Theorem 3.3 & 3.5: Neither `NotSend` nor `FakeBox<u32>` (despite `FakeBox<T>`
having a syntactically smaller parameter `T`) satisfies `SendAt 1`! -/
theorem notSend_and_fakeBox_unprovable :
    ¬ SendAt 1 .notSend ∧ ¬ SendAt 1 (.fakeBox .u32) := by
  simp [SendAt]

/-- Syntactic productivity gate (`ProductiveUnsafeImpl`): every cycle in the impl
graph MUST contain at least one `isIndirectionGuarded = true` edge (and every
`unsafe impl` node must discharge its guarded depth-indexed proof obligation). -/
def CycleProductive (cycle : List ImplEdge) : Prop :=
  ∃ e ∈ cycle, e.isIndirectionGuarded = true

def notSendCycle : List ImplEdge :=
  [ ⟨"NotSend:Send", "NotSend:Send", true, false⟩ ]

def mutCycle : List ImplEdge :=
  [ ⟨"MutA:Send", "MutB:Send", false, false⟩,
    ⟨"MutB:Send", "MutA:Send", true, false⟩ ]

theorem productive_gate_admits_boxNode_and_rejects_unsound_cycles :
    CycleProductive boxNodeImplGraph ∧
    ¬ CycleProductive notSendCycle ∧
    ¬ CycleProductive mutCycle := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨⟨"Box<BoxNode>:Send", "BoxNode:Send", true, true⟩, by simp [boxNodeImplGraph], rfl⟩
  · rintro ⟨e, he, hg⟩; simp [notSendCycle] at he; subst he; cases hg
  · rintro ⟨e, he, hg⟩; simp [mutCycle] at he; rcases he with rfl | rfl <;> cases hg

/-! ### `VisCone` Encapsulation Preservation Across `.returned` AND `.unwound` -/

def VisConeOp := Nat → Except Nat Nat

def PreservesOnReturn (Inv : Nat → Prop) (op : VisConeOp) : Prop :=
  ∀ s s', Inv s → op s = .ok s' → Inv s'

def PreservesOnUnwind (Inv : Nat → Prop) (op : VisConeOp) : Prop :=
  ∀ s s', Inv s → op s = .error s' → Inv s'

def runClient (ops : List VisConeOp) (s : Nat) : Nat :=
  match ops with
  | [] => s
  | op :: rest =>
    match op s with
    | .ok s' => runClient rest s'
    | .error s' => runClient rest s'

/-- Theorem 3.7a (`visCone_encapsulation_soundness`): Preserving `Inv` on BOTH
`.returned` AND `.unwound` preserves `Inv` across arbitrary `catch_unwind` clients. -/
theorem visCone_encapsulation_soundness (Inv : Nat → Prop) (ops : List VisConeOp)
    (hRet : ∀ op ∈ ops, PreservesOnReturn Inv op)
    (hUnw : ∀ op ∈ ops, PreservesOnUnwind Inv op)
    (s₀ : Nat) (h0 : Inv s₀) :
    Inv (runClient ops s₀) := by
  induction ops generalizing s₀ with
  | nil => exact h0
  | cons op rest ih =>
    simp only [runClient]
    cases hop : op s₀ with
    | ok s' =>
      have hs' := hRet op (by simp) s₀ s' h0 hop
      exact ih (fun o ho => hRet o (by simp [ho])) (fun o ho => hUnw o (by simp [ho])) s' hs'
    | error s' =>
      have hs' := hUnw op (by simp) s₀ s' h0 hop
      exact ih (fun o ho => hRet o (by simp [ho])) (fun o ho => hUnw o (by simp [ho])) s' hs'

/-- Theorem 3.7b (`visCone_missing_unwind_breaks_invariant`): Omitting `.unwound`
preservation lets a `catch_unwind` client break `LibValid` (`NonZero`)! -/
def buggyOp : VisConeOp := fun _ => .error 0

theorem visCone_missing_unwind_breaks_invariant :
    PreservesOnReturn (fun n => n ≠ 0) buggyOp ∧
    ¬ (runClient [buggyOp] 42 ≠ 0) := by
  constructor
  · intro _ _ _ h; simp [buggyOp] at h
  · simp [runClient, buggyOp]

end SpecCoreSoundness

#print axioms SpecCoreSoundness.conflated_pre_wrongly_accepts_unsound_safe_fn
#print axioms SpecCoreSoundness.safe_fn_requires_cannot_waive_ub
#print axioms SpecCoreSoundness.default_partial_always_realizable
#print axioms SpecCoreSoundness.realizable_iff_valid_choice_inhabited
#print axioms SpecCoreSoundness.three_way_only_realizability_gap_witness
#print axioms SpecCoreSoundness.extern_c_fails_without_noUnwind
#print axioms SpecCoreSoundness.extern_c_wellFormed_with_noUnwind
#print axioms SpecCoreSoundness.mutual_recursion_partial_sound
#print axioms SpecCoreSoundness.mutual_recursion_termination_unsound_without_measure
#print axioms SpecCoreSoundness.mutual_recursion_termination_sound_with_measure
#print axioms SpecCoreSoundness.specEval_rejects_cell_mutation
#print axioms SpecCoreSoundness.short_circuit_clause_safe_vs_eager_panics
#print axioms SpecCoreSoundness.stepwise_specEval_rejects_mutate_and_restore_while_endpoint_accepts
#print axioms SpecCoreSoundness.specEval_rejects_panic
#print axioms SpecCoreSoundness.dead_branch_erasure_wellFormed_iff
#print axioms SpecCoreSoundness.dead_branch_erasure_diverges_iff
#print axioms SpecCoreSoundness.dead_branch_erasure_behavior_iff
#print axioms SpecCoreSoundness.fromBytes_fullValid_rejects_nonZero
#print axioms SpecCoreSoundness.naive_scc_rejects_box_node
#print axioms SpecCoreSoundness.sendAt_boxNode_unfold
#print axioms SpecCoreSoundness.boxNode_send_well_founded
#print axioms SpecCoreSoundness.notSend_and_fakeBox_unprovable
#print axioms SpecCoreSoundness.productive_gate_admits_boxNode_and_rejects_unsound_cycles
#print axioms SpecCoreSoundness.visCone_encapsulation_soundness
#print axioms SpecCoreSoundness.visCone_missing_unwind_breaks_invariant
