/-
Core operational model and properties for constant-time preservation under compilation.
All definitions live in `namespace Toy.CT` and use only core Lean.
-/

namespace Toy.CT

/-- Small-step operational machine parameterized by public input `Pub`, secret input `Sec`,
return value `Out`, and per-step observable leakage event `Leak`.

Captures deterministic or nondeterministic operational semantics (such as source IRs and
assembly-level machines in the program-counter or structured-leakage security models) in
which each transition step emits one leakage observation `Leak`. -/
structure Machine (Pub Sec Out Leak : Type) where
  /-- Internal machine configuration type. -/
  State : Type
  /-- Valid initial configurations for `(pub, sec)`. -/
  init : Pub → Sec → State → Prop
  /-- Single-step transition `step s l s'` from `s` to `s'` emitting leakage event `l`. -/
  step : State → Leak → State → Prop
  /-- Halting configurations `halted s out` yielding final output `out`. -/
  halted : State → Out → Prop

/-- Multi-step transition sequence `Steps M s tr s'` accumulating step-level leakage
events into trace `tr : List Leak`. Captures finite execution fragments of `M`. -/
inductive Steps {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) :
    M.State → List Leak → M.State → Prop where
  | nil (s : M.State) : Steps M s [] s
  | cons {s s' s'' : M.State} {l : Leak} {tr : List Leak} :
      M.step s l s' → Steps M s' tr s'' → Steps M s (l :: tr) s''

/-- Concatenation of two multi-step transition sequences. -/
theorem Steps.append {Pub Sec Out Leak : Type} {M : Machine Pub Sec Out Leak}
    {s₁ s₂ s₃ : M.State} {tr₁ tr₂ : List Leak}
    (h₁ : Steps M s₁ tr₁ s₂) (h₂ : Steps M s₂ tr₂ s₃) :
    Steps M s₁ (tr₁ ++ tr₂) s₃ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons hstep _ ih => exact Steps.cons hstep (ih h₂)

/-- Inversion of zero-event `Steps`: trace `[]` forces `sf = s`. -/
theorem Steps.nil_iff {Pub Sec Out Leak : Type} {M : Machine Pub Sec Out Leak}
    {s sf : M.State} :
    Steps M s [] sf ↔ sf = s := by
  constructor
  · intro h
    generalize htr : ([] : List Leak) = tr at h
    cases h with
    | nil _ => rfl
    | cons _ _ => cases htr
  · rintro rfl
    exact Steps.nil (M := M) _

/-- Inversion of non-empty `Steps`: trace `l :: tr` decomposes into one `M.step`
followed by `Steps M s' tr sf`. -/
theorem Steps.cons_iff {Pub Sec Out Leak : Type} {M : Machine Pub Sec Out Leak}
    {s sf : M.State} {l : Leak} {tr : List Leak} :
    Steps M s (l :: tr) sf ↔ ∃ s', M.step s l s' ∧ Steps M s' tr sf := by
  constructor
  · intro h
    generalize htr : l :: tr = tr₀ at h
    cases h with
    | nil _ => cases htr
    | cons hstep hrest =>
      injection htr with hl htail
      subst hl; subst htail
      exact ⟨_, hstep, hrest⟩
  · rintro ⟨s', hstep, hrest⟩
    exact Steps.cons (M := M) hstep hrest

/-- Complete case-split characterization of `Steps M s tr sf` for arbitrary expressions
`s`, `tr`, `sf`. -/
theorem Steps.cases_iff {Pub Sec Out Leak : Type} {M : Machine Pub Sec Out Leak}
    {s sf : M.State} {tr : List Leak} :
    Steps M s tr sf ↔
      (tr = [] ∧ sf = s) ∨ (∃ l s' tr', tr = l :: tr' ∧ M.step s l s' ∧ Steps M s' tr' sf) := by
  cases tr with
  | nil =>
    rw [Steps.nil_iff]
    constructor
    · intro h; exact Or.inl ⟨rfl, h⟩
    · rintro (⟨_, h⟩ | ⟨_, _, _, h, _⟩)
      · exact h
      · cases h
  | cons l tr' =>
    rw [Steps.cons_iff]
    constructor
    · rintro ⟨s', hstep, hrest⟩
      exact Or.inr ⟨l, s', tr', rfl, hstep, hrest⟩
    · rintro (⟨h, _⟩ | ⟨l', s', tr'', heq, hstep, hrest⟩)
      · cases h
      · injection heq with hl htr
        subst hl; subst htr
        exact ⟨s', hstep, hrest⟩

/-- Complete terminating execution `Executes M pub sec out tr`: starting from a valid
initial configuration for `(pub, sec)`, `M` steps to a halted configuration yielding
output `out` and full leakage trace `tr`. -/
def Executes {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak)
    (pub : Pub) (sec : Sec) (out : Out) (tr : List Leak) : Prop :=
  ∃ s₀ sf, M.init pub sec s₀ ∧ Steps M s₀ tr sf ∧ M.halted sf out

/-- Observable halting trace relation `HasTrace M pub sec tr`: `M` has at least one
complete terminating execution on `(pub, sec)` emitting leakage trace `tr`. -/
def HasTrace {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak)
    (pub : Pub) (sec : Sec) (tr : List Leak) : Prop :=
  ∃ out, Executes M pub sec out tr

/-- Configuration `s` is reachable in `M` on inputs `(pub, sec)` via some finite prefix
of steps from an initial configuration. -/
def Reachable {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak)
    (pub : Pub) (sec : Sec) (s : M.State) : Prop :=
  ∃ s₀ tr, M.init pub sec s₀ ∧ Steps M s₀ tr s

/-- Initial-state totality: every `(pub, sec)` input admits at least one initial
configuration in `M`. -/
def HasInit {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub sec, ∃ s₀, M.init pub sec s₀

/-- Operational progress (non-stuckness) on reachable configurations: every configuration
reachable from an initial state either halts with an output or can take a step. Allows
non-terminating machines while ruling out stuck configurations. -/
def Safe {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub sec s, Reachable M pub sec s →
    (∃ out, M.halted s out) ∨ (∃ l s', M.step s l s')

/-- Existential (may-)termination: every `(pub, sec)` input admits at least one complete
halting execution in `M`. For nondeterministic machines this does not rule out coexisting
diverging runs; under `Deterministic M`, `Terminates M` ensures that the unique execution
halts on every input. -/
def Terminates {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub sec, ∃ out tr, Executes M pub sec out tr

/-- Small-step transition determinism: initial configurations are unique per input,
single-step transitions are unique in both leakage event and successor state, and halted
configurations do not step.

Separated from `OutputDeterministic` so trace-level simulation theorems require only
control/transition determinism without bundling output-uniqueness hypotheses. -/
structure Deterministic {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) : Prop where
  init_det : ∀ pub sec s₁ s₂, M.init pub sec s₁ → M.init pub sec s₂ → s₁ = s₂
  step_det : ∀ s l₁ s₁ l₂ s₂, M.step s l₁ s₁ → M.step s l₂ s₂ → l₁ = l₂ ∧ s₁ = s₂
  halted_nostep : ∀ s out l s', M.halted s out → ¬ M.step s l s'

/-- Halted output determinism: any halted configuration yields at most one output value. -/
def OutputDeterministic {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ s out₁ out₂, M.halted s out₁ → M.halted s out₂ → out₁ = out₂

/-- Per-input uniqueness of halting leakage traces: on any fixed `(pub, sec)`, `M` admits
at most one halting leakage trace `tr`. Implied by `Deterministic M`, while still holding
for machines with secret-free state forks that emit identical traces. -/
def TraceUnique {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub sec tr₁ tr₂, HasTrace M pub sec tr₁ → HasTrace M pub sec tr₂ → tr₁ = tr₂

/-- Halting-domain agreement between `S` and `T`: on every `(pub, sec)`, `S` admits at
least one halting run if and only if `T` admits at least one halting run. -/
def HaltAgree {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak) : Prop :=
  ∀ pub sec, (∃ trS, HasTrace S pub sec trS) ↔ (∃ trT, HasTrace T pub sec trT)

/-- Constant-time security on halting executions (possibilistic halting-trace-set
indistinguishability): for every public input `pub` and every pair of secrets `s₁, s₂`,
`M` admits the exact same set of halting leakage traces on `(pub, s₁)` and `(pub, s₂)`.

Rules out secret-dependent halting trace differences (control-flow, memory-address, or
step-count variations) and secret-dependent halting versus non-halting behavior, while
admitting secret-oblivious nondeterministic leakage (unlike `ConstantTime M ∧ TraceUnique M`).
Quantifies over complete halting runs only, so non-halting execution branches are not
constrained unless every run halts (for instance under `Deterministic M ∧ Terminates M`). -/
def ConstantTime {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub s₁ s₂ tr, HasTrace M pub s₁ tr ↔ HasTrace M pub s₂ tr

/-- Two-sided equality of may-halting output sets between source machine `S` and target
machine `T`: for every `(pub, sec)` and output `out`, `S` has some halting execution
returning `out` if and only if `T` has some halting execution returning `out`.

Implies one-sided inclusion of halting outputs. Constrains complete halting runs only: on an
input where neither machine halts it imposes no condition, even when both machines are
deterministic (one may diverge while the other is stuck). -/
def FunctionallyCorrect {Pub Sec Out SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec Out SrcLeak)
    (T : Machine Pub Sec Out TgtLeak) : Prop :=
  ∀ pub sec out, (∃ trS, Executes S pub sec out trS) ↔ (∃ trT, Executes T pub sec out trT)

/-- Leakage-determined relation from `S` to `T` witnessed by secret-independent trace
transformer `leakMap : Pub → List SrcLeak → List TgtLeak`: for every `(pub, sec)`, the
halting target traces of `T` are exactly the images under `leakMap pub` of the halting
source traces of `S`. -/
def LeakageDetermined {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak) : Prop :=
  ∀ pub sec trT, HasTrace T pub sec trT ↔
    ∃ trS, HasTrace S pub sec trS ∧ trT = leakMap pub trS

/-- One-way trace inclusion plus halting transfer (`WeakLeakageDetermined`): every halting
target trace lies in the image under `leakMap pub` of `S`'s halting traces, and `T` halts
whenever `S` halts. Strictly weaker than `LeakageDetermined`; suffices to preserve
`ConstantTime` when `TraceUnique S` holds, but fails on nondeterministic sources without
`TraceUnique S`. -/
def WeakLeakageDetermined {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak) : Prop :=
  (∀ pub sec trT, HasTrace T pub sec trT →
      ∃ trS, HasTrace S pub sec trS ∧ trT = leakMap pub trS) ∧
  (∀ pub sec trS, HasTrace S pub sec trS → ∃ trT, HasTrace T pub sec trT)

/-- Variant of `LeakageDetermined` in which the trace transformer `leakMap` is permitted
to inspect the secret input `Sec` as well as `(Pub, List SrcLeak)`. Satisfiable for every
`TraceUnique` target with matching halting domain (`exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree`),
showing that dropping secret-independence vacates the restriction. -/
def SecretDependentLeakageDetermined {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → Sec → List SrcLeak → List TgtLeak) : Prop :=
  ∀ pub sec trT, HasTrace T pub sec trT ↔
    ∃ trS, HasTrace S pub sec trS ∧ trT = leakMap pub sec trS

/-- Lifts a step-level leakage transformer `stepLeak : Pub → SrcLeak → List TgtLeak`
homomorphically to full leakage traces by mapping each source step's leakage event to its
fixed sequence of target step leakage events and concatenating in order. -/
def liftStepLeak {Pub SrcLeak TgtLeak : Type}
    (stepLeak : Pub → SrcLeak → List TgtLeak)
    (pub : Pub) (tr : List SrcLeak) : List TgtLeak :=
  match tr with
  | [] => []
  | l :: rest => stepLeak pub l ++ liftStepLeak stepLeak pub rest

@[simp]
theorem liftStepLeak_nil {Pub SrcLeak TgtLeak : Type}
    (stepLeak : Pub → SrcLeak → List TgtLeak) (pub : Pub) :
    liftStepLeak stepLeak pub [] = [] := rfl

@[simp]
theorem liftStepLeak_cons {Pub SrcLeak TgtLeak : Type}
    (stepLeak : Pub → SrcLeak → List TgtLeak) (pub : Pub)
    (l : SrcLeak) (rest : List SrcLeak) :
    liftStepLeak stepLeak pub (l :: rest) =
      stepLeak pub l ++ liftStepLeak stepLeak pub rest := rfl

/-- Forward step-wise leakage simulation from `S` to `T` with secret-independent step
leakage map `stepLeak : Pub → SrcLeak → List TgtLeak`, source anti-stuttering measure
`measure : S.State → Nat`, and simulation relation `R : Pub → Sec → S.State → T.State → Prop`.

Each source step emitting `ls` is matched by a target multi-step sequence emitting the
fixed list `stepLeak pub ls` (`[lt]` for 1-to-1 lockstep, `[lt₁, ...]` for instruction
expansion, or `[]` when the source step is eliminated / stutters). Whenever a source step
stutters (`stepLeak pub ls = []`), `measure` strictly decreases so `S` cannot silently
diverge while `T` halts. Captures a leakage-functional single-run special case of general
relational constant-time simulations. -/
structure StepLeakSim {Pub Sec Out SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec Out SrcLeak)
    (T : Machine Pub Sec Out TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak)
    (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → T.halted t out
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    (∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t') ∧
    (stepLeak pub ls = [] → measure s' < measure s)

/-- Weakened variant of `StepLeakSim` omitting the anti-stuttering measure decrease
condition on silent/eliminated source steps (`stepLeak pub ls = []`). -/
structure UnmeasuredStepLeakSim {Pub Sec Out SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec Out SrcLeak)
    (T : Machine Pub Sec Out TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak)
    (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → T.halted t out
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    ∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t'

/-- Single-run forward option simulation allowing each source transition `S.step s ls s'`
from a related state `(s, t)` to choose from internal state `(s, t)` (without a relational
pair invariant across secrets) whether `T` executes `stepLeak pub ls` or stutters (`[]`
target steps with strict measure decrease `measure s' < measure s`). Used to show why
state-dependent stuttering in a single-run simulation can leak secrets via trace length. -/
structure OptionStepLeakSim {Pub Sec Out SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec Out SrcLeak)
    (T : Machine Pub Sec Out TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak)
    (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → T.halted t out
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    (∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t') ∨
    (measure s' < measure s ∧ R pub sec s' t)

/-- Composition of two secret-independent trace leakage transformers `f` and `g`. -/
def composeLeakMap {Pub Leak₁ Leak₂ Leak₃ : Type}
    (f : Pub → List Leak₁ → List Leak₂)
    (g : Pub → List Leak₂ → List Leak₃) :
    Pub → List Leak₁ → List Leak₃ :=
  fun pub tr₁ => g pub (f pub tr₁)

/-! ## Derivation and Reduction Lemmas -/

/-- Trace uniqueness for a `Deterministic` machine on fixed `(pub, sec)`. -/
theorem Deterministic.hasTrace_unique {Pub Sec Out Leak : Type}
    {M : Machine Pub Sec Out Leak} (hDet : Deterministic M)
    {pub : Pub} {sec : Sec} {tr₁ tr₂ : List Leak}
    (h₁ : HasTrace M pub sec tr₁) (h₂ : HasTrace M pub sec tr₂) :
    tr₁ = tr₂ := by
  rcases h₁ with ⟨out₁, s₀, sf₁, hInit₁, hSteps₁, hHalt₁⟩
  rcases h₂ with ⟨out₂, s₀', sf₂, hInit₂, hSteps₂, hHalt₂⟩
  have hs₀ : s₀' = s₀ := hDet.init_det pub sec s₀' s₀ hInit₂ hInit₁
  subst hs₀
  have aux : ∀ {s f₁ : M.State} {t₁ : List Leak},
      Steps M s t₁ f₁ → M.halted f₁ out₁ →
      ∀ {t₂ : List Leak} {f₂ : M.State},
      Steps M s t₂ f₂ → M.halted f₂ out₂ → t₁ = t₂ := by
    intro s f₁ t₁ hs₁ hf₁
    induction hs₁ with
    | nil s =>
      intro t₂ f₂ hs₂ _
      cases hs₂ with
      | nil _ => rfl
      | cons hstep _ => exact False.elim (hDet.halted_nostep s out₁ _ _ hf₁ hstep)
    | cons hstep₁ _ ih =>
      intro t₂ f₂ hs₂ hf₂
      cases hs₂ with
      | nil _ => exact False.elim (hDet.halted_nostep _ out₂ _ _ hf₂ hstep₁)
      | cons hstep₂ hrest₂ =>
        rcases hDet.step_det _ _ _ _ _ hstep₁ hstep₂ with ⟨hl, hnext⟩
        subst hl; subst hnext
        exact congrArg _ (ih hf₁ hrest₂ hf₂)
  exact aux hSteps₁ hHalt₁ hSteps₂ hHalt₂

/-- Every `Deterministic` machine satisfies `TraceUnique`. -/
theorem Deterministic.traceUnique {Pub Sec Out Leak : Type}
    {M : Machine Pub Sec Out Leak} (hDet : Deterministic M) :
    TraceUnique M :=
  fun _ _ _ _ h₁ h₂ => hDet.hasTrace_unique h₁ h₂

/-- Any two complete executions of a `Deterministic` and `OutputDeterministic` machine
on the same `(pub, sec)` produce identical outputs and leakage traces. -/
theorem Deterministic.executes_unique {Pub Sec Out Leak : Type}
    {M : Machine Pub Sec Out Leak} (hDet : Deterministic M) (hOut : OutputDeterministic M)
    {pub : Pub} {sec : Sec} {out₁ out₂ : Out} {tr₁ tr₂ : List Leak}
    (h₁ : Executes M pub sec out₁ tr₁) (h₂ : Executes M pub sec out₂ tr₂) :
    out₁ = out₂ ∧ tr₁ = tr₂ := by
  have htr : tr₁ = tr₂ := hDet.hasTrace_unique ⟨out₁, h₁⟩ ⟨out₂, h₂⟩
  subst htr
  refine ⟨?_, rfl⟩
  rcases h₁ with ⟨s₀, sf₁, hInit₁, hSteps₁, hHalt₁⟩
  rcases h₂ with ⟨s₀', sf₂, hInit₂, hSteps₂, hHalt₂⟩
  have hs₀ : s₀' = s₀ := hDet.init_det pub sec s₀' s₀ hInit₂ hInit₁
  subst hs₀
  have sameFinal : ∀ {s f₁ : M.State} {tr : List Leak},
      Steps M s tr f₁ → ∀ {f₂ : M.State}, Steps M s tr f₂ → f₁ = f₂ := by
    intro s f₁ tr hs₁
    induction hs₁ with
    | nil _ =>
      intro f₂ hs₂
      exact ((Steps.nil_iff (M := M)).mp hs₂).symm
    | cons hstep₁ _ ih =>
      intro f₂ hs₂
      rcases (Steps.cons_iff (M := M)).mp hs₂ with ⟨s₂, hstep₂, hrest₂⟩
      rcases hDet.step_det _ _ _ _ _ hstep₁ hstep₂ with ⟨_, hnext⟩
      subst hnext
      exact ih hrest₂
  have hsf : sf₁ = sf₂ := sameFinal hSteps₁ hSteps₂
  subst hsf
  exact hOut sf₁ out₁ out₂ hHalt₁ hHalt₂

/-- `ConstantTime M ∧ TraceUnique M` is equivalent to the combined unique-trace formula
`∀ pub s₁ s₂ tr₁, HasTrace M pub s₁ tr₁ → ∀ tr₂, (HasTrace M pub s₂ tr₂ ↔ tr₂ = tr₁)`. -/
theorem constantTime_and_traceUnique_iff {Pub Sec Out Leak : Type}
    (M : Machine Pub Sec Out Leak) :
    (ConstantTime M ∧ TraceUnique M) ↔
      (∀ pub s₁ s₂ tr₁, HasTrace M pub s₁ tr₁ →
        ∀ tr₂, (HasTrace M pub s₂ tr₂ ↔ tr₂ = tr₁)) := by
  constructor
  · rintro ⟨hCT, hU⟩ pub s₁ s₂ tr₁ h₁ tr₂
    constructor
    · intro h₂
      exact hU pub s₁ tr₂ tr₁ ((hCT pub s₁ s₂ tr₂).mpr h₂) h₁
    · intro hEq
      rw [hEq]
      exact (hCT pub s₁ s₂ tr₁).mp h₁
  · intro h
    refine ⟨fun pub s₁ s₂ tr => ⟨fun h₁ => (h pub s₁ s₂ tr h₁ tr).mpr rfl,
      fun h₂ => (h pub s₂ s₁ tr h₂ tr).mpr rfl⟩, ?_⟩
    intro pub sec tr₁ tr₂ h₁ h₂
    exact ((h pub sec sec tr₁ h₁ tr₂).mp h₂).symm

/-- On any machine satisfying `Terminates M` and `TraceUnique M` (for example any
`Deterministic` and `Terminates` machine), `ConstantTime M` is equivalent to pairwise
equality of halting traces across all pairs of secrets. -/
theorem constantTime_iff_trace_eq_of_terminates_traceUnique {Pub Sec Out Leak : Type}
    {M : Machine Pub Sec Out Leak} (hTerm : Terminates M) (hUnique : TraceUnique M) :
    ConstantTime M ↔
      (∀ pub s₁ s₂ tr₁ tr₂, HasTrace M pub s₁ tr₁ → HasTrace M pub s₂ tr₂ → tr₁ = tr₂) := by
  constructor
  · intro hCT pub s₁ s₂ tr₁ tr₂ h₁ h₂
    exact hUnique pub s₁ tr₁ tr₂ h₁ ((hCT pub s₁ s₂ tr₂).mpr h₂)
  · intro hEq pub s₁ s₂ tr
    constructor
    · intro h₁
      rcases hTerm pub s₂ with ⟨out₂, tr₂, hex₂⟩
      have h₂ : HasTrace M pub s₂ tr₂ := ⟨out₂, hex₂⟩
      have heq : tr = tr₂ := hEq pub s₁ s₂ tr tr₂ h₁ h₂
      rwa [heq]
    · intro h₂
      rcases hTerm pub s₁ with ⟨out₁, tr₁, hex₁⟩
      have h₁ : HasTrace M pub s₁ tr₁ := ⟨out₁, hex₁⟩
      have heq : tr = tr₁ := hEq pub s₂ s₁ tr tr₁ h₂ h₁
      rwa [heq]

/-- Two machines that both satisfy `Terminates` agree on their halting domain (`HaltAgree`). -/
theorem haltAgree_of_terminates {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    (hTermS : Terminates S) (hTermT : Terminates T) :
    HaltAgree S T := by
  intro pub sec
  rcases hTermS pub sec with ⟨outS, trS, hexS⟩
  rcases hTermT pub sec with ⟨outT, trT, hexT⟩
  exact ⟨fun _ => ⟨trT, outT, hexT⟩, fun _ => ⟨trS, outS, hexS⟩⟩

/-- Every `LeakageDetermined` pair agrees on its halting domain (`HaltAgree`). -/
theorem haltAgree_of_leakageDetermined {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    {leakMap : Pub → List SrcLeak → List TgtLeak}
    (hLD : LeakageDetermined S T leakMap) :
    HaltAgree S T := by
  intro pub sec
  constructor
  · rintro ⟨trS, hS⟩
    exact ⟨leakMap pub trS, (hLD pub sec _).mpr ⟨trS, hS, rfl⟩⟩
  · rintro ⟨trT, hT⟩
    rcases (hLD pub sec trT).mp hT with ⟨trS, hS, _⟩
    exact ⟨trS, hS⟩

/-- Sufficient-condition reduction on terminating machines: when both `S` and `T` satisfy
`Terminates`, two-sided `LeakageDetermined S T leakMap` follows from one-way functional
agreement `trT = leakMap pub trS` on halting traces. -/
theorem leakageDetermined_of_terminates_trace_eq
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    {leakMap : Pub → List SrcLeak → List TgtLeak}
    (hTermS : Terminates S) (hTermT : Terminates T)
    (hEq : ∀ pub sec trS trT, HasTrace S pub sec trS → HasTrace T pub sec trT →
      trT = leakMap pub trS) :
    LeakageDetermined S T leakMap := by
  intro pub sec trT
  constructor
  · intro hT
    rcases hTermS pub sec with ⟨outS, trS, hexS⟩
    have hS : HasTrace S pub sec trS := ⟨outS, hexS⟩
    exact ⟨trS, hS, hEq pub sec trS trT hS hT⟩
  · rintro ⟨trS, hS, rfl⟩
    rcases hTermT pub sec with ⟨outT, trT', hexT⟩
    have hT' : HasTrace T pub sec trT' := ⟨outT, hexT⟩
    have heq : trT' = leakMap pub trS := hEq pub sec trS trT' hS hT'
    rw [← heq]
    exact hT'

/-- One-way `WeakLeakageDetermined` suffices to preserve `ConstantTime` whenever the
source machine satisfies `TraceUnique S` (in particular for any `Deterministic S`). -/
theorem weakLeakageDetermined_preserves_ct_of_traceUnique
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    {leakMap : Pub → List SrcLeak → List TgtLeak}
    (hWeak : WeakLeakageDetermined S T leakMap)
    (hUniqueS : TraceUnique S)
    (hCT : ConstantTime S) :
    ConstantTime T := by
  have transfer : ∀ pub s₁ s₂ tr, HasTrace T pub s₁ tr → HasTrace T pub s₂ tr := by
    intro pub s₁ s₂ tr₁ hT₁
    rcases hWeak.1 pub s₁ tr₁ hT₁ with ⟨trS₁, hS₁, rfl⟩
    have hS₂ : HasTrace S pub s₂ trS₁ := (hCT pub s₁ s₂ trS₁).mp hS₁
    rcases hWeak.2 pub s₂ trS₁ hS₂ with ⟨trT₂, hT₂⟩
    rcases hWeak.1 pub s₂ trT₂ hT₂ with ⟨trS₂, hS₂', rfl⟩
    have heq : trS₁ = trS₂ := hUniqueS pub s₂ trS₁ trS₂ hS₂ hS₂'
    rwa [heq]
  intro pub s₁ s₂ tr
  exact ⟨transfer pub s₁ s₂ tr, transfer pub s₂ s₁ tr⟩

/-- A `SecretDependentLeakageDetermined` witness that ignores its `Sec` argument reduces
definitionally to `LeakageDetermined`. -/
theorem secretDependentLeakageDetermined_const_sec_iff
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak) :
    SecretDependentLeakageDetermined S T (fun pub _ trS => leakMap pub trS) ↔
      LeakageDetermined S T leakMap :=
  Iff.rfl

/-- Allowing the leakage transformer to inspect `Sec` vacates the restriction on any
`TraceUnique` target with matching halting domain (`HaltAgree S T`): some secret-dependent
map `m` always satisfies `SecretDependentLeakageDetermined S T m`. -/
theorem exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    (hUniqueT : TraceUnique T)
    (hHalt : HaltAgree S T) :
    ∃ m, SecretDependentLeakageDetermined S T m := by
  classical
  refine ⟨fun pub sec _ =>
    if h : ∃ trT, HasTrace T pub sec trT then Classical.choose h else [], ?_⟩
  intro pub sec trT
  constructor
  · intro hT
    rcases (hHalt pub sec).mpr ⟨trT, hT⟩ with ⟨trS, hS⟩
    have hex : ∃ trT', HasTrace T pub sec trT' := ⟨trT, hT⟩
    refine ⟨trS, hS, ?_⟩
    simp only [hex, ↓reduceDIte]
    exact hUniqueT pub sec trT _ hT (Classical.choose_spec hex)
  · rintro ⟨trS, hS, rfl⟩
    rcases (hHalt pub sec).mp ⟨trS, hS⟩ with ⟨trT', hT'⟩
    have hex : ∃ trT'', HasTrace T pub sec trT'' := ⟨trT', hT'⟩
    simp only [hex, ↓reduceDIte]
    exact Classical.choose_spec hex

/-- Specialization of `exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree`
to terminating source and deterministic terminating target machines. -/
theorem exists_secretDependentLeakageDetermined_of_det_terminates
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    (hTermS : Terminates S)
    (hDetT : Deterministic T)
    (hTermT : Terminates T) :
    ∃ m, SecretDependentLeakageDetermined S T m :=
  exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree
    hDetT.traceUnique (haltAgree_of_terminates hTermS hTermT)

/-- `Deterministic S` and `Terminates S` together imply `HasInit S` and `Safe S`, showing
that `step_leakage_sim_det_target_implies_leakage_determined` requires only `HasInit S`
and `Safe S` rather than `Deterministic S` or `Terminates S`. -/
theorem hasInit_and_safe_of_det_terminates {Pub Sec Out Leak : Type}
    {S : Machine Pub Sec Out Leak} (hDet : Deterministic S) (hTerm : Terminates S) :
    HasInit S ∧ Safe S := by
  refine ⟨?_, ?_⟩
  · intro pub sec
    rcases hTerm pub sec with ⟨_, _, s₀, _, hInit, _, _⟩
    exact ⟨s₀, hInit⟩
  · intro pub sec s ⟨s₀, trPre, hInitPre, hStepsPre⟩
    rcases hTerm pub sec with ⟨out, trFull, s₀', sf, hInitFull, hStepsFull, hHaltFull⟩
    have hs₀ : s₀' = s₀ := hDet.init_det pub sec s₀' s₀ hInitFull hInitPre
    subst hs₀
    have walk : ∀ {x y : S.State} {tp : List Leak},
        Steps S x tp y → ∀ {tf : List Leak},
        Steps S x tf sf → (∃ out', S.halted y out') ∨ (∃ l s', S.step y l s') := by
      intro x y tp hPre
      induction hPre with
      | nil _ =>
        intro tf hFull
        cases hFull with
        | nil _ => exact Or.inl ⟨out, hHaltFull⟩
        | cons hstep _ => exact Or.inr ⟨_, _, hstep⟩
      | cons hstepPre _ ih =>
        intro tf hFull
        cases hFull with
        | nil _ => exact False.elim (hDet.halted_nostep _ out _ _ hHaltFull hstepPre)
        | cons hstepFull hRestFull =>
          rcases hDet.step_det _ _ _ _ _ hstepPre hstepFull with ⟨_, hnext⟩
          subst hnext
          exact ih hRestFull
    exact walk hStepsPre hStepsFull

end Toy.CT
