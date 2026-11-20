import ToyCT.Defs

/-
Concrete small-step machines and exact execution/trace characterizations used across
definition examples, counterexamples, non-vacuity witnesses, and positive controls.
-/

namespace Toy.CT

/-! ## 1. Branchless Constant-Time Select (`branchlessSelect`) -/

/-- Control state for single-step branchless selection (`cmov` / arithmetic mask). -/
inductive SelectState where
  | entry (a b : Nat) (cond : Bool)
  | done (result : Nat)
  deriving DecidableEq, Repr

/-- Constant-time branchless selector: evaluates `if sec then pub.1 else pub.2` in a
single straight-line step at program counter `0`, emitting leakage trace `[0]` regardless
of the secret condition `sec`. -/
def branchlessSelect : Machine (Nat × Nat) Bool Nat Nat where
  State := SelectState
  init pub sec s := s = .entry pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .entry a b cond => pc = 0 ∧ s' = .done (if cond then a else b)
    | .done _ => False
  halted s out := s = .done out

theorem branchlessSelect_executes_iff (pub : Nat × Nat) (sec : Bool) (out : Nat) (tr : List Nat) :
    Executes branchlessSelect pub sec out tr ↔
      out = (if sec then pub.1 else pub.2) ∧ tr = [0] := by
  constructor
  · rintro ⟨s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      subst hs₀
      cases hHalt
    | cons hstep hrest =>
      subst hs₀
      rcases hstep with ⟨rfl, hnext⟩
      cases hrest with
      | nil _ =>
        rw [hnext] at hHalt
        injection hHalt with hout
        exact ⟨hout.symm, rfl⟩
      | cons hstep2 _ =>
        rw [hnext] at hstep2
        exact False.elim hstep2
  · rintro ⟨rfl, rfl⟩
    exact ⟨.entry pub.1 pub.2 sec, .done (if sec then pub.1 else pub.2), rfl,
      Steps.cons (M := branchlessSelect) ⟨rfl, rfl⟩
        (Steps.nil (M := branchlessSelect) _), rfl⟩

theorem branchlessSelect_hasTrace_iff (pub : Nat × Nat) (sec : Bool) (tr : List Nat) :
    HasTrace branchlessSelect pub sec tr ↔ tr = [0] := by
  constructor
  · rintro ⟨out, hex⟩
    exact ((branchlessSelect_executes_iff pub sec out tr).mp hex).2
  · rintro rfl
    exact ⟨if sec then pub.1 else pub.2,
      (branchlessSelect_executes_iff pub sec _ [0]).mpr ⟨rfl, rfl⟩⟩

theorem branchlessSelect_deterministic : Deterministic branchlessSelect where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det s _ _ _ _ h₁ h₂ := by
    cases s with
    | entry _ _ _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | done _ => exact False.elim h₁
  halted_nostep _ _ _ _ hHalt hStep := by
    cases hHalt
    exact hStep

theorem branchlessSelect_terminates : Terminates branchlessSelect := by
  intro pub sec
  exact ⟨if sec then pub.1 else pub.2, [0],
    (branchlessSelect_executes_iff pub sec _ [0]).mpr ⟨rfl, rfl⟩⟩

theorem branchlessSelect_constantTime : ConstantTime branchlessSelect := by
  intro pub s₁ s₂ tr
  rw [branchlessSelect_hasTrace_iff, branchlessSelect_hasTrace_iff]

/-! ## 2. Secret-Branching Select (`branchingSelect`) -/

/-- Control state for conditional-branch selection jumping to PC `1` (`true`) or PC `2` (`false`). -/
inductive BranchSelectState where
  | entry (a b : Nat) (cond : Bool)
  | thenBlock (a : Nat)
  | elseBlock (b : Nat)
  | done (result : Nat)
  deriving DecidableEq, Repr

/-- Functionally equivalent selector lowered via a secret-dependent branch: inspects `sec`
at PC `0`, then jumps either to `thenBlock` at PC `1` (trace `[0, 1]`) or `elseBlock` at
PC `2` (trace `[0, 2]`). -/
def branchingSelect : Machine (Nat × Nat) Bool Nat Nat where
  State := BranchSelectState
  init pub sec s := s = .entry pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .entry a b cond =>
        pc = 0 ∧ s' = (if cond then .thenBlock a else .elseBlock b)
    | .thenBlock a => pc = 1 ∧ s' = .done a
    | .elseBlock b => pc = 2 ∧ s' = .done b
    | .done _ => False
  halted s out := s = .done out

theorem branchingSelect_executes_iff (pub : Nat × Nat) (sec : Bool) (out : Nat) (tr : List Nat) :
    Executes branchingSelect pub sec out tr ↔
      out = (if sec then pub.1 else pub.2) ∧ tr = [0, if sec then 1 else 2] := by
  constructor
  · rintro ⟨s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      subst hs₀
      cases hHalt
    | cons h₁ hrest₁ =>
      subst hs₀
      rcases h₁ with ⟨rfl, hs₁⟩
      cases sec with
      | false =>
        cases hrest₁ with
        | nil _ =>
          rw [hs₁] at hHalt
          cases hHalt
        | cons h₂ hrest₂ =>
          rw [hs₁] at h₂
          rcases h₂ with ⟨rfl, hs₂⟩
          cases hrest₂ with
          | nil _ =>
            rw [hs₂] at hHalt
            injection hHalt with hout
            exact ⟨hout.symm, rfl⟩
          | cons h₃ _ =>
            rw [hs₂] at h₃
            exact False.elim h₃
      | true =>
        cases hrest₁ with
        | nil _ =>
          rw [hs₁] at hHalt
          cases hHalt
        | cons h₂ hrest₂ =>
          rw [hs₁] at h₂
          rcases h₂ with ⟨rfl, hs₂⟩
          cases hrest₂ with
          | nil _ =>
            rw [hs₂] at hHalt
            injection hHalt with hout
            exact ⟨hout.symm, rfl⟩
          | cons h₃ _ =>
            rw [hs₂] at h₃
            exact False.elim h₃
  · rintro ⟨rfl, rfl⟩
    cases sec with
    | false =>
      exact ⟨.entry pub.1 pub.2 false, .done pub.2, rfl,
        Steps.cons (M := branchingSelect) ⟨rfl, rfl⟩
          (Steps.cons (M := branchingSelect) ⟨rfl, rfl⟩
            (Steps.nil (M := branchingSelect) _)), rfl⟩
    | true =>
      exact ⟨.entry pub.1 pub.2 true, .done pub.1, rfl,
        Steps.cons (M := branchingSelect) ⟨rfl, rfl⟩
          (Steps.cons (M := branchingSelect) ⟨rfl, rfl⟩
            (Steps.nil (M := branchingSelect) _)), rfl⟩

theorem branchingSelect_hasTrace_iff (pub : Nat × Nat) (sec : Bool) (tr : List Nat) :
    HasTrace branchingSelect pub sec tr ↔ tr = [0, if sec then 1 else 2] := by
  constructor
  · rintro ⟨out, hex⟩
    exact ((branchingSelect_executes_iff pub sec out tr).mp hex).2
  · rintro rfl
    exact ⟨if sec then pub.1 else pub.2,
      (branchingSelect_executes_iff pub sec _ _).mpr ⟨rfl, rfl⟩⟩

/-- Every halting execution of `branchingSelect` takes exactly two steps regardless of
`sec`, showing that its violation of `ConstantTime` is a program-counter-value leak
rather than a step-count difference. -/
theorem branchingSelect_trace_length (pub : Nat × Nat) (sec : Bool) (tr : List Nat)
    (h : HasTrace branchingSelect pub sec tr) : tr.length = 2 := by
  rw [(branchingSelect_hasTrace_iff pub sec tr).mp h]
  rfl

theorem branchingSelect_deterministic : Deterministic branchingSelect where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det s _ _ _ _ h₁ h₂ := by
    cases s with
    | entry _ _ _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | thenBlock _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | elseBlock _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | done _ => exact False.elim h₁
  halted_nostep _ _ _ _ hHalt hStep := by
    cases hHalt
    exact hStep

theorem branchingSelect_terminates : Terminates branchingSelect := by
  intro pub sec
  exact ⟨if sec then pub.1 else pub.2, [0, if sec then 1 else 2],
    (branchingSelect_executes_iff pub sec _ _).mpr ⟨rfl, rfl⟩⟩

theorem branchingSelect_not_constantTime : ¬ ConstantTime branchingSelect := by
  intro hCT
  have hTrue : HasTrace branchingSelect (0, 0) true [0, 1] :=
    (branchingSelect_hasTrace_iff (0, 0) true [0, 1]).mpr rfl
  have hFalse : HasTrace branchingSelect (0, 0) false [0, 1] :=
    (hCT (0, 0) true false [0, 1]).mp hTrue
  have hEq : [0, 1] = [0, 2] := (branchingSelect_hasTrace_iff (0, 0) false [0, 1]).mp hFalse
  cases hEq

theorem branchless_branching_functionallyCorrect :
    FunctionallyCorrect branchlessSelect branchingSelect := by
  intro pub sec out
  constructor
  · rintro ⟨trS, hexS⟩
    have hout := ((branchlessSelect_executes_iff pub sec out trS).mp hexS).1
    exact ⟨[0, if sec then 1 else 2], (branchingSelect_executes_iff pub sec out _).mpr ⟨hout, rfl⟩⟩
  · rintro ⟨trT, hexT⟩
    have hout := ((branchingSelect_executes_iff pub sec out trT).mp hexT).1
    exact ⟨[0], (branchlessSelect_executes_iff pub sec out [0]).mpr ⟨hout, rfl⟩⟩

/-! ## 3. Stuttering Source and Constant-Time Lowered Targets (`branchlessWithNop`, `branchlessLowered`, `branchlessEncoded`) -/

/-- Source selector preceded by a dead `nop` instruction at PC `0` (eliminated during
compilation) before executing the branchless select at PC `1`. -/
inductive NopSelectState where
  | nop (a b : Nat) (cond : Bool)
  | select (a b : Nat) (cond : Bool)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchlessWithNop : Machine (Nat × Nat) Bool Nat Nat where
  State := NopSelectState
  init pub sec s := s = .nop pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .nop a b cond => pc = 0 ∧ s' = .select a b cond
    | .select a b cond => pc = 1 ∧ s' = .done (if cond then a else b)
    | .done _ => False
  halted s out := s = .done out

theorem branchlessWithNop_executes_iff (pub : Nat × Nat) (sec : Bool) (out : Nat) (tr : List Nat) :
    Executes branchlessWithNop pub sec out tr ↔
      out = (if sec then pub.1 else pub.2) ∧ tr = [0, 1] := by
  constructor
  · rintro ⟨s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      subst hs₀
      cases hHalt
    | cons h₁ hrest₁ =>
      subst hs₀
      rcases h₁ with ⟨rfl, hs₁⟩
      cases hrest₁ with
      | nil _ =>
        rw [hs₁] at hHalt
        cases hHalt
      | cons h₂ hrest₂ =>
        rw [hs₁] at h₂
        rcases h₂ with ⟨rfl, hs₂⟩
        cases hrest₂ with
        | nil _ =>
          rw [hs₂] at hHalt
          injection hHalt with hout
          exact ⟨hout.symm, rfl⟩
        | cons h₃ _ =>
          rw [hs₂] at h₃
          exact False.elim h₃
  · rintro ⟨rfl, rfl⟩
    exact ⟨.nop pub.1 pub.2 sec, .done (if sec then pub.1 else pub.2), rfl,
      Steps.cons (M := branchlessWithNop) ⟨rfl, rfl⟩
        (Steps.cons (M := branchlessWithNop) ⟨rfl, rfl⟩
          (Steps.nil (M := branchlessWithNop) _)), rfl⟩

theorem branchlessWithNop_deterministic : Deterministic branchlessWithNop where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det s _ _ _ _ h₁ h₂ := by
    cases s with
    | nop _ _ _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | select _ _ _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | done _ => exact False.elim h₁
  halted_nostep _ _ _ _ hHalt hStep := by
    cases hHalt
    exact hStep

theorem branchlessWithNop_terminates : Terminates branchlessWithNop := by
  intro pub sec
  exact ⟨if sec then pub.1 else pub.2, [0, 1],
    (branchlessWithNop_executes_iff pub sec _ [0, 1]).mpr ⟨rfl, rfl⟩⟩

/-- Two-instruction constant-time lowered target: executes unconditional mask generation
at PC `10` followed by unconditional masked combination at PC `11` (trace `[10, 11]`). -/
inductive LoweredSelectState where
  | mask (a b : Nat) (cond : Bool)
  | combine (chosen : Nat)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchlessLowered : Machine (Nat × Nat) Bool Nat Nat where
  State := LoweredSelectState
  init pub sec s := s = .mask pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .mask a b cond => pc = 10 ∧ s' = .combine (if cond then a else b)
    | .combine v => pc = 11 ∧ s' = .done v
    | .done _ => False
  halted s out := s = .done out

theorem branchlessLowered_executes_iff (pub : Nat × Nat) (sec : Bool) (out : Nat) (tr : List Nat) :
    Executes branchlessLowered pub sec out tr ↔
      out = (if sec then pub.1 else pub.2) ∧ tr = [10, 11] := by
  constructor
  · rintro ⟨s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      subst hs₀
      cases hHalt
    | cons h₁ hrest₁ =>
      subst hs₀
      rcases h₁ with ⟨rfl, hs₁⟩
      cases hrest₁ with
      | nil _ =>
        rw [hs₁] at hHalt
        cases hHalt
      | cons h₂ hrest₂ =>
        rw [hs₁] at h₂
        rcases h₂ with ⟨rfl, hs₂⟩
        cases hrest₂ with
        | nil _ =>
          rw [hs₂] at hHalt
          injection hHalt with hout
          exact ⟨hout.symm, rfl⟩
        | cons h₃ _ =>
          rw [hs₂] at h₃
          exact False.elim h₃
  · rintro ⟨rfl, rfl⟩
    exact ⟨.mask pub.1 pub.2 sec, .done (if sec then pub.1 else pub.2), rfl,
      Steps.cons (M := branchlessLowered) ⟨rfl, rfl⟩
        (Steps.cons (M := branchlessLowered) ⟨rfl, rfl⟩
          (Steps.nil (M := branchlessLowered) _)), rfl⟩

theorem branchlessLowered_hasTrace_iff (pub : Nat × Nat) (sec : Bool) (tr : List Nat) :
    HasTrace branchlessLowered pub sec tr ↔ tr = [10, 11] := by
  constructor
  · rintro ⟨out, hex⟩
    exact ((branchlessLowered_executes_iff pub sec out tr).mp hex).2
  · rintro rfl
    exact ⟨if sec then pub.1 else pub.2,
      (branchlessLowered_executes_iff pub sec _ [10, 11]).mpr ⟨rfl, rfl⟩⟩

theorem branchlessLowered_deterministic : Deterministic branchlessLowered where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det s _ _ _ _ h₁ h₂ := by
    cases s with
    | mask _ _ _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | combine _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | done _ => exact False.elim h₁
  halted_nostep _ _ _ _ hHalt hStep := by
    cases hHalt
    exact hStep

theorem branchlessLowered_terminates : Terminates branchlessLowered := by
  intro pub sec
  exact ⟨if sec then pub.1 else pub.2, [10, 11],
    (branchlessLowered_executes_iff pub sec _ [10, 11]).mpr ⟨rfl, rfl⟩⟩

theorem branchlessLowered_constantTime : ConstantTime branchlessLowered := by
  intro pub s₁ s₂ tr
  rw [branchlessLowered_hasTrace_iff, branchlessLowered_hasTrace_iff]

/-- Second-pass target relocating `branchlessLowered` to a public-input-dependent code
bank `100 + pub.1 % 2`, `101 + pub.1 % 2` (illustrating public-dependent, secret-free
leakage transformation in pass composition). -/
inductive EncodedSelectState where
  | instr0 (base : Nat) (a b : Nat) (cond : Bool)
  | instr1 (base : Nat) (chosen : Nat)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchlessEncoded : Machine (Nat × Nat) Bool Nat Nat where
  State := EncodedSelectState
  init pub sec s := s = .instr0 (pub.1 % 2) pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .instr0 base a b cond =>
        pc = 100 + base ∧ s' = .instr1 base (if cond then a else b)
    | .instr1 base v =>
        pc = 101 + base ∧ s' = .done v
    | .done _ => False
  halted s out := s = .done out

theorem branchlessEncoded_hasTrace_iff (pub : Nat × Nat) (sec : Bool) (tr : List Nat) :
    HasTrace branchlessEncoded pub sec tr ↔
      tr = [100 + pub.1 % 2, 101 + pub.1 % 2] := by
  constructor
  · rintro ⟨out, s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      subst hs₀
      cases hHalt
    | cons h₁ hrest₁ =>
      subst hs₀
      rcases h₁ with ⟨rfl, hs₁⟩
      cases hrest₁ with
      | nil _ =>
        rw [hs₁] at hHalt
        cases hHalt
      | cons h₂ hrest₂ =>
        rw [hs₁] at h₂
        rcases h₂ with ⟨rfl, hs₂⟩
        cases hrest₂ with
        | nil _ => rfl
        | cons h₃ _ =>
          rw [hs₂] at h₃
          exact False.elim h₃
  · rintro rfl
    exact ⟨if sec then pub.1 else pub.2,
      .instr0 (pub.1 % 2) pub.1 pub.2 sec, .done (if sec then pub.1 else pub.2), rfl,
      Steps.cons (M := branchlessEncoded) ⟨rfl, rfl⟩
        (Steps.cons (M := branchlessEncoded) ⟨rfl, rfl⟩
          (Steps.nil (M := branchlessEncoded) _)), rfl⟩

/-! ## 4. Diagnostic, Nondeterministic, and Boundary Counterexample Machines -/

/-- Machine that halts immediately on `sec = false` (`[]`) and gets stuck without halting
on `sec = true`, exhibiting a pure termination side channel. -/
def abortOnSecret : Machine Unit Bool Unit Nat where
  State := Bool
  init _ sec s := s = sec
  step _ _ _ := False
  halted s out := s = false ∧ out = ()

theorem abortOnSecret_traceUnique : TraceUnique abortOnSecret := by
  rintro _ _ tr₁ tr₂ ⟨_, _, _, _, hs₁, _⟩ ⟨_, _, _, _, hs₂, _⟩
  cases hs₁ with
  | nil _ =>
    cases hs₂ with
    | nil _ => rfl
    | cons h _ => exact False.elim h
  | cons h _ => exact False.elim h

/-- Machine that halts immediately with trace `[]` iff `sec = true` (getting stuck on
`sec = false`). Used as a deterministic non-constant-time target in tightness proofs. -/
def haltIfTrue : Machine Unit Bool Unit Nat where
  State := Bool
  init _ sec s := s = sec
  step _ _ _ := False
  halted s out := s = true ∧ out = ()

theorem haltIfTrue_deterministic : Deterministic haltIfTrue where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det _ _ _ _ _ h _ := False.elim h
  halted_nostep _ _ _ _ _ h := h

theorem haltIfTrue_hasTrace_iff (sec : Bool) (tr : List Nat) :
    HasTrace haltIfTrue () sec tr ↔ (sec = true ∧ tr = []) := by
  constructor
  · rintro ⟨_, s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      rw [hs₀] at hHalt
      exact ⟨hHalt.1, rfl⟩
    | cons h _ => exact False.elim h
  · rintro ⟨rfl, rfl⟩
    exact ⟨(), true, true, rfl, Steps.nil (M := haltIfTrue) true, ⟨rfl, rfl⟩⟩

theorem haltIfTrue_not_constantTime : ¬ ConstantTime haltIfTrue := by
  intro hCT
  have hTrue : HasTrace haltIfTrue () true [] := (haltIfTrue_hasTrace_iff true []).mpr ⟨rfl, rfl⟩
  have hFalse : HasTrace haltIfTrue () false [] := (hCT () true false []).mp hTrue
  have hEq := ((haltIfTrue_hasTrace_iff false []).mp hFalse).1
  cases hEq

/-- Trivial machine halting immediately with trace `[]` on every input; refined by
`haltIfTrue` on trace inclusion yet `ConstantTime` where `haltIfTrue` is not. -/
def allHalt : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted _ out := out = ()

theorem allHalt_hasTrace_iff (sec : Bool) (tr : List Nat) :
    HasTrace allHalt () sec tr ↔ tr = [] := by
  constructor
  · rintro ⟨_, _, _, _, hSteps, _⟩
    cases hSteps with
    | nil _ => rfl
    | cons h _ => exact False.elim h
  · rintro rfl
    exact ⟨(), (), (), rfl, Steps.nil (M := allHalt) (), rfl⟩

theorem allHalt_constantTime : ConstantTime allHalt := by
  intro _ s₁ s₂ tr
  rw [allHalt_hasTrace_iff, allHalt_hasTrace_iff]

/-- Secret-oblivious nondeterministic machine: `init`, `step`, and `halted` ignore `sec`,
while the single transition nondeterministically emits leakage `0` or `1`. Satisfies
`ConstantTime` (equal halting trace sets `{[0], [1]}` across secrets) while violating
`TraceUnique`. -/
def coinFlip : Machine Unit Bool Unit Nat where
  State := Bool
  init _ _ s := s = false
  step s l s' := s = false ∧ (l = 0 ∨ l = 1) ∧ s' = true
  halted s out := s = true ∧ out = ()

theorem coinFlip_hasTrace_iff (pub : Unit) (sec : Bool) (tr : List Nat) :
    HasTrace coinFlip pub sec tr ↔ (tr = [0] ∨ tr = [1]) := by
  constructor
  · rintro ⟨_, s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      rw [hs₀] at hHalt
      exact False.elim (Bool.noConfusion hHalt.1)
    | cons h₁ hrest =>
      rcases h₁ with ⟨_, hl, hs₁⟩
      cases hrest with
      | nil _ =>
        rcases hl with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      | cons h₂ _ =>
        rw [hs₁] at h₂
        exact False.elim (Bool.noConfusion h₂.1)
  · rintro (rfl | rfl)
    · exact ⟨(), false, true, rfl,
        Steps.cons (M := coinFlip) ⟨rfl, Or.inl rfl, rfl⟩
          (Steps.nil (M := coinFlip) true), ⟨rfl, rfl⟩⟩
    · exact ⟨(), false, true, rfl,
        Steps.cons (M := coinFlip) ⟨rfl, Or.inr rfl, rfl⟩
          (Steps.nil (M := coinFlip) true), ⟨rfl, rfl⟩⟩

theorem coinFlip_constantTime : ConstantTime coinFlip :=
  fun _ _ _ _ => Iff.rfl

theorem coinFlip_not_traceUnique : ¬ TraceUnique coinFlip := by
  intro hU
  have h₀ : HasTrace coinFlip () false [0] :=
    (coinFlip_hasTrace_iff () false [0]).mpr (Or.inl rfl)
  have h₁ : HasTrace coinFlip () false [1] :=
    (coinFlip_hasTrace_iff () false [1]).mpr (Or.inr rfl)
  have heq : [0] = [1] := hU () false [0] [1] h₀ h₁
  cases heq

/-- Diverging machine whose very first step reveals `sec` (`1` on `true`, `0` on `false`)
while never halting (`halted _ _ := False`). Satisfies `ConstantTime` vacuously because
`HasTrace` quantifies over halting runs only. -/
def leakyLoop : Machine Unit Bool Unit Nat where
  State := Bool
  init _ sec s := s = sec
  step s l s' := l = (if s then 1 else 0) ∧ s' = s
  halted _ _ := False

theorem leakyLoop_constantTime : ConstantTime leakyLoop := by
  intro _ _ _ _
  exact ⟨fun ⟨_, _, _, _, _, h⟩ => False.elim h, fun ⟨_, _, _, _, _, h⟩ => False.elim h⟩

/-- Nondeterministic machine that satisfies both `Terminates` and `ConstantTime` (every
halting run halts immediately with trace `[]`), yet from its initial state can also enter
a diverging loop whose first step leaks `if sec then 1 else 0`. -/
inductive HaltOrLeakState where
  | start (sec : Bool)
  | loop (sec : Bool)
  deriving DecidableEq, Repr

def haltOrLeak : Machine Unit Bool Unit Nat where
  State := HaltOrLeakState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start b => l = (if b then 1 else 0) ∧ s' = .loop b
    | .loop b => l = (if b then 1 else 0) ∧ s' = .loop b
  halted s out :=
    match s with
    | .start _ => out = ()
    | .loop _ => False

theorem haltOrLeak_step_loop {x s' : haltOrLeak.State} {l : Nat}
    (h : haltOrLeak.step x l s') : ∃ b, s' = HaltOrLeakState.loop b := by
  cases (x : HaltOrLeakState) with
  | start b => exact ⟨b, h.2⟩
  | loop b => exact ⟨b, h.2⟩

private theorem haltOrLeak_steps_nonempty {x y : haltOrLeak.State} {tr : List Nat}
    (h : Steps haltOrLeak x tr y) : tr = [] ∨ ∃ b, y = .loop b := by
  induction h with
  | nil _ => exact Or.inl rfl
  | cons hs hrest ih =>
    right
    rcases ih with rfl | hb
    · have hy := (Steps.nil_iff (M := haltOrLeak)).mp hrest
      subst hy
      exact haltOrLeak_step_loop hs
    · exact hb

theorem haltOrLeak_hasTrace_iff (sec : Bool) (tr : List Nat) :
    HasTrace haltOrLeak () sec tr ↔ tr = [] := by
  constructor
  · rintro ⟨_, s₀, sf, _, hSteps, hHalt⟩
    rcases haltOrLeak_steps_nonempty hSteps with h | ⟨b, rfl⟩
    · exact h
    · exact False.elim hHalt
  · rintro rfl
    exact ⟨(), .start sec, .start sec, rfl, Steps.nil (M := haltOrLeak) _, rfl⟩

theorem haltOrLeak_terminates : Terminates haltOrLeak :=
  fun _ sec => ⟨(), [], .start sec, .start sec, rfl, Steps.nil (M := haltOrLeak) _, rfl⟩

theorem haltOrLeak_constantTime : ConstantTime haltOrLeak := by
  intro _ s₁ s₂ tr
  rw [haltOrLeak_hasTrace_iff, haltOrLeak_hasTrace_iff]

/-- Constant-time machine returning constant `0` instead of selecting between `pub.1`
and `pub.2` (violating `FunctionallyCorrect` wrt `branchlessSelect`). -/
def wrongOutputSelect : Machine (Nat × Nat) Bool Nat Nat where
  State := Bool
  init _ _ s := s = false
  step s pc s' := s = false ∧ pc = 0 ∧ s' = true
  halted s out := s = true ∧ out = 0

/-- Machine with no valid initial configurations (`¬ HasInit`). -/
def emptyInitMachine : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ _ := False
  step _ _ _ := False
  halted _ out := out = ()

/-- Machine whose unique initial configuration is stuck (`HasInit` holds, `Safe` fails). -/
def stuckMachine : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted _ _ := False

/-- Trivial deterministic machine halting in zero steps with trace `[]` and output `()`. -/
def trivialHaltedMachine : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted s out := s = () ∧ out = ()

theorem trivialHaltedMachine_deterministic : Deterministic trivialHaltedMachine where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det _ _ _ _ _ h₁ _ := False.elim h₁
  halted_nostep _ _ _ _ _ hStep := hStep

theorem trivialHaltedMachine_hasTrace_iff (pub : Unit) (sec : Bool) (tr : List Nat) :
    HasTrace trivialHaltedMachine pub sec tr ↔ tr = [] := by
  constructor
  · rintro ⟨_, s₀, sf, _, hSteps, _⟩
    cases hSteps with
    | nil _ => rfl
    | cons hstep _ => exact False.elim hstep
  · rintro rfl
    exact ⟨(), (), (), rfl, Steps.nil (M := trivialHaltedMachine) (), ⟨rfl, rfl⟩⟩

/-- Deterministic single-step constant-time source machine emitting `[0]` on all inputs. -/
def constOneStep : Machine Unit Bool Unit Nat where
  State := Bool
  init _ _ s := s = false
  step s l s' := s = false ∧ l = 0 ∧ s' = true
  halted s out := s = true ∧ out = ()

theorem constOneStep_executes_iff (pub : Unit) (sec : Bool) (out : Unit) (tr : List Nat) :
    Executes constOneStep pub sec out tr ↔ out = () ∧ tr = [0] := by
  constructor
  · rintro ⟨s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      subst hs₀
      exact False.elim (Bool.noConfusion hHalt.1)
    | cons h₁ hrest =>
      rcases h₁ with ⟨_, rfl, hs₁⟩
      cases hrest with
      | nil _ => exact ⟨hHalt.2, rfl⟩
      | cons h₂ _ =>
        rw [hs₁] at h₂
        exact False.elim (Bool.noConfusion h₂.1)
  · rintro ⟨rfl, rfl⟩
    exact ⟨false, true, rfl,
      Steps.cons (M := constOneStep) ⟨rfl, rfl, rfl⟩
        (Steps.nil (M := constOneStep) true), ⟨rfl, rfl⟩⟩

theorem constOneStep_hasTrace_iff (pub : Unit) (sec : Bool) (tr : List Nat) :
    HasTrace constOneStep pub sec tr ↔ tr = [0] := by
  constructor
  · rintro ⟨out, hex⟩
    exact ((constOneStep_executes_iff pub sec out tr).mp hex).2
  · rintro rfl
    exact ⟨(), (constOneStep_executes_iff pub sec () [0]).mpr ⟨rfl, rfl⟩⟩

theorem constOneStep_deterministic : Deterministic constOneStep where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det _ _ _ _ _ h₁ h₂ := ⟨h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm⟩
  halted_nostep _ _ _ _ hHalt hStep := by
    rw [hHalt.1] at hStep
    exact Bool.noConfusion hStep.1

theorem constOneStep_terminates : Terminates constOneStep := by
  intro pub sec
  exact ⟨(), [0], (constOneStep_executes_iff pub sec () [0]).mpr ⟨rfl, rfl⟩⟩

theorem constOneStep_constantTime : ConstantTime constOneStep := by
  intro pub s₁ s₂ tr
  rw [constOneStep_hasTrace_iff, constOneStep_hasTrace_iff]

/-- Nondeterministic target machine that always admits the simulated step emitting `0`,
and when `sec = true` additionally admits a second transition emitting `1` while still
returning `()`. Demonstrates why forward simulation without `Deterministic T` fails to
establish `LeakageDetermined` or `ConstantTime`. -/
inductive NondetTargetState where
  | start (sec : Bool)
  | done
  deriving DecidableEq, Repr

def nondetSecretBranchTarget : Machine Unit Bool Unit Nat where
  State := NondetTargetState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start false => l = 0 ∧ s' = .done
    | .start true => (l = 0 ∨ l = 1) ∧ s' = .done
    | .done => False
  halted s out := s = .done ∧ out = ()

theorem nondetSecretBranchTarget_terminates : Terminates nondetSecretBranchTarget := by
  intro _ sec
  cases sec with
  | false =>
    exact ⟨(), [0], NondetTargetState.start false, NondetTargetState.done, rfl,
      Steps.cons (M := nondetSecretBranchTarget) ⟨rfl, rfl⟩
        (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done), ⟨rfl, rfl⟩⟩
  | true =>
    exact ⟨(), [0], NondetTargetState.start true, NondetTargetState.done, rfl,
      Steps.cons (M := nondetSecretBranchTarget) ⟨Or.inl rfl, rfl⟩
        (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done), ⟨rfl, rfl⟩⟩

/-- Determinized counterpart of `nondetSecretBranchTarget` over the same `NondetTargetState`
state space: removes the unsimulated `l = 1` transition on `.start true`, restoring
`Deterministic`, `LeakageDetermined`, and `ConstantTime` under the exact same simulation
relation `constNondetRel`. -/
def determinizedSecretBranchTarget : Machine Unit Bool Unit Nat where
  State := NondetTargetState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start _ => l = 0 ∧ s' = .done
    | .done => False
  halted s out := s = .done ∧ out = ()

theorem determinizedSecretBranchTarget_deterministic :
    Deterministic determinizedSecretBranchTarget where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det s _ _ _ _ h₁ h₂ := by
    cases s with
    | start _ => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | done => exact False.elim h₁
  halted_nostep _ _ _ _ hHalt hStep := by
    rw [hHalt.1] at hStep
    exact hStep

theorem determinizedSecretBranchTarget_hasTrace_iff (pub : Unit) (sec : Bool) (tr : List Nat) :
    HasTrace determinizedSecretBranchTarget pub sec tr ↔ tr = [0] := by
  constructor
  · rintro ⟨_, s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      rw [hs₀] at hHalt
      exact False.elim (NondetTargetState.noConfusion hHalt.1)
    | cons h₁ hrest =>
      rw [hs₀] at h₁
      rcases h₁ with ⟨rfl, hs₁⟩
      cases hrest with
      | nil _ => rfl
      | cons h₂ _ =>
        rw [hs₁] at h₂
        exact False.elim h₂
  · rintro rfl
    exact ⟨(), .start sec, .done, rfl,
      Steps.cons (M := determinizedSecretBranchTarget) ⟨rfl, rfl⟩
        (Steps.nil (M := determinizedSecretBranchTarget) .done), ⟨rfl, rfl⟩⟩

theorem determinizedSecretBranchTarget_constantTime :
    ConstantTime determinizedSecretBranchTarget := by
  intro pub s₁ s₂ tr
  rw [determinizedSecretBranchTarget_hasTrace_iff, determinizedSecretBranchTarget_hasTrace_iff]

/-! ## 5. Per-Clause `Deterministic` Necessity Targets (`secretTwoInitTarget`, `secretForkTarget`, `secretHaltOrStepTarget`) -/

inductive TwoInitState where
  | a
  | b
  | fin
  deriving DecidableEq, Repr

/-- Target machine violating `init_det` alone (`step_det` and `halted_nostep` hold):
always admits initial state `.a` (emitting `[0]`), and when `sec = true` also admits `.b`
(emitting `[1]`). -/
def secretTwoInitTarget : Machine Unit Bool Unit Nat where
  State := TwoInitState
  init _ sec s := s = .a ∨ (sec = true ∧ s = .b)
  step s l s' :=
    match s with
    | .a => l = 0 ∧ s' = .fin
    | .b => l = 1 ∧ s' = .fin
    | .fin => False
  halted s out := s = .fin ∧ out = ()

inductive SecretForkState where
  | start (sec : Bool)
  | a
  | b
  | fin
  deriving DecidableEq, Repr

/-- Target machine violating only the successor-state uniqueness half of `step_det`
(`init_det`, step-leakage uniqueness, and `halted_nostep` all hold): from `.start sec`
every transition emits `0`, moving to `.a` (halted) or, when `sec = true`, also to `.b`
(which then emits `1` before halting). -/
def secretForkTarget : Machine Unit Bool Unit Nat where
  State := SecretForkState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start sec => l = 0 ∧ (s' = .a ∨ (sec = true ∧ s' = .b))
    | .a => False
    | .b => l = 1 ∧ s' = .fin
    | .fin => False
  halted s out := (s = .a ∨ s = .fin) ∧ out = ()

/-- Target machine violating `halted_nostep` alone (`init_det` and `step_det` hold):
every configuration is halted with `()`, while `(false, true)` can additionally step
emitting `1` to `(true, true)`. -/
def secretHaltOrStepTarget : Machine Unit Bool Unit Nat where
  State := Bool × Bool
  init _ sec s := s = (false, sec)
  step s l s' := s.1 = false ∧ s.2 = true ∧ l = 1 ∧ s' = (true, s.2)
  halted _ out := out = ()

/-! ## 6. State-Dependent Option-Stutter Machines (`twoStepConstSource`, `secretStutterTarget`) -/

/-- Three-stage countdown state space shared by `twoStepConstSource` and
`secretStutterTarget`. -/
inductive TwoStepState where
  | s2
  | s1
  | s0
  deriving DecidableEq, Repr

/-- Decreasing anti-stuttering measure on `TwoStepState`. -/
def twoStepMeasure : TwoStepState → Nat
  | .s2 => 2
  | .s1 => 1
  | .s0 => 0

/-- Two-step deterministic constant-time source machine counting `.s2 →[0] .s1 →[0] .s0`
on every input (`HasTrace` iff `tr = [0, 0]`). -/
def twoStepConstSource : Machine Unit Bool Unit Nat where
  State := TwoStepState
  init _ _ s := s = .s2
  step s l s' :=
    match s with
    | .s2 => l = 0 ∧ s' = .s1
    | .s1 => l = 0 ∧ s' = .s0
    | .s0 => False
  halted s out := s = .s0 ∧ out = ()

theorem twoStepConstSource_deterministic : Deterministic twoStepConstSource where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det s _ _ _ _ h₁ h₂ := by
    cases s with
    | s2 => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | s1 => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | s0 => exact False.elim h₁
  halted_nostep _ _ _ _ hHalt hStep := by
    rw [hHalt.1] at hStep
    exact hStep

theorem twoStepConstSource_hasTrace_iff (pub : Unit) (sec : Bool) (tr : List Nat) :
    HasTrace twoStepConstSource pub sec tr ↔ tr = [0, 0] := by
  constructor
  · rintro ⟨_, s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      rw [hs₀] at hHalt
      exact False.elim (TwoStepState.noConfusion hHalt.1)
    | cons h₁ hrest₁ =>
      rw [hs₀] at h₁
      rcases h₁ with ⟨rfl, hs₁⟩
      cases hrest₁ with
      | nil _ =>
        rw [hs₁] at hHalt
        exact False.elim (TwoStepState.noConfusion hHalt.1)
      | cons h₂ hrest₂ =>
        rw [hs₁] at h₂
        rcases h₂ with ⟨rfl, hs₂⟩
        cases hrest₂ with
        | nil _ => rfl
        | cons h₃ _ =>
          rw [hs₂] at h₃
          exact False.elim h₃
  · rintro rfl
    exact ⟨(), .s2, .s0, rfl,
      Steps.cons (M := twoStepConstSource) ⟨rfl, rfl⟩
        (Steps.cons (M := twoStepConstSource) ⟨rfl, rfl⟩
          (Steps.nil (M := twoStepConstSource) .s0)), ⟨rfl, rfl⟩⟩

theorem twoStepConstSource_terminates : Terminates twoStepConstSource :=
  fun pub sec =>
    let ⟨out, hex⟩ := (twoStepConstSource_hasTrace_iff pub sec [0, 0]).mpr rfl
    ⟨out, [0, 0], hex⟩

theorem twoStepConstSource_constantTime : ConstantTime twoStepConstSource := by
  intro pub s₁ s₂ tr
  rw [twoStepConstSource_hasTrace_iff, twoStepConstSource_hasTrace_iff]

/-- Deterministic target machine taking 1 step (`[0]`) on `sec = true` (stuttering the
first source step) and 2 steps (`[0, 0]`) on `sec = false`, leaking `sec` via trace length. -/
def secretStutterTarget : Machine Unit Bool Unit Nat where
  State := TwoStepState
  init _ sec s := s = if sec then .s1 else .s2
  step s l s' :=
    match s with
    | .s2 => l = 0 ∧ s' = .s1
    | .s1 => l = 0 ∧ s' = .s0
    | .s0 => False
  halted s out := s = .s0 ∧ out = ()

theorem secretStutterTarget_deterministic : Deterministic secretStutterTarget where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det s _ _ _ _ h₁ h₂ := by
    cases s with
    | s2 => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | s1 => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | s0 => exact False.elim h₁
  halted_nostep _ _ _ _ hHalt hStep := by
    rw [hHalt.1] at hStep
    exact hStep

theorem secretStutterTarget_hasTrace_iff (pub : Unit) (sec : Bool) (tr : List Nat) :
    HasTrace secretStutterTarget pub sec tr ↔ tr = (if sec then [0] else [0, 0]) := by
  constructor
  · rintro ⟨_, s₀, sf, hs₀, hSteps, hHalt⟩
    cases sec with
    | false =>
      cases hSteps with
      | nil _ =>
        rw [hs₀] at hHalt
        exact False.elim (TwoStepState.noConfusion hHalt.1)
      | cons h₁ hrest₁ =>
        rw [hs₀] at h₁
        rcases h₁ with ⟨rfl, hs₁⟩
        cases hrest₁ with
        | nil _ =>
          rw [hs₁] at hHalt
          exact False.elim (TwoStepState.noConfusion hHalt.1)
        | cons h₂ hrest₂ =>
          rw [hs₁] at h₂
          rcases h₂ with ⟨rfl, hs₂⟩
          cases hrest₂ with
          | nil _ => rfl
          | cons h₃ _ =>
            rw [hs₂] at h₃
            exact False.elim h₃
    | true =>
      cases hSteps with
      | nil _ =>
        rw [hs₀] at hHalt
        exact False.elim (TwoStepState.noConfusion hHalt.1)
      | cons h₁ hrest₁ =>
        rw [hs₀] at h₁
        rcases h₁ with ⟨rfl, hs₁⟩
        cases hrest₁ with
        | nil _ => rfl
        | cons h₂ _ =>
          rw [hs₁] at h₂
          exact False.elim h₂
  · rintro rfl
    cases sec with
    | false =>
      exact ⟨(), .s2, .s0, rfl,
        Steps.cons (M := secretStutterTarget) ⟨rfl, rfl⟩
          (Steps.cons (M := secretStutterTarget) ⟨rfl, rfl⟩
            (Steps.nil (M := secretStutterTarget) .s0)), ⟨rfl, rfl⟩⟩
    | true =>
      exact ⟨(), .s1, .s0, rfl,
        Steps.cons (M := secretStutterTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := secretStutterTarget) .s0), ⟨rfl, rfl⟩⟩

theorem secretStutterTarget_not_constantTime : ¬ ConstantTime secretStutterTarget := by
  intro hCT
  have hT : HasTrace secretStutterTarget () true [0] :=
    (secretStutterTarget_hasTrace_iff () true [0]).mpr rfl
  have hF : HasTrace secretStutterTarget () false [0] := (hCT () true false [0]).mp hT
  have heq : [0] = [0, 0] := (secretStutterTarget_hasTrace_iff () false [0]).mp hF
  cases heq

/-- Deterministic non-terminating source machine stepping `() →[0] ()` forever without
halting (`HasInit`, `Safe`, `Deterministic`, and `ConstantTime` hold; used to show that
omitting the stuttering measure from `StepLeakSim` breaks `LeakageDetermined` and
`ConstantTime` preservation). -/
def silentLoopSource : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step s l s' := s = () ∧ l = 0 ∧ s' = ()
  halted _ _ := False

theorem silentLoopSource_deterministic : Deterministic silentLoopSource where
  init_det _ _ _ _ h₁ h₂ := h₁.trans h₂.symm
  step_det _ _ _ _ _ h₁ h₂ := ⟨h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm⟩
  halted_nostep _ _ _ _ hHalt _ := False.elim hHalt

/-- Transition-deterministic machine whose halted state relates to multiple outputs
(`Deterministic` holds, `OutputDeterministic` fails). -/
def ambiguousOutputMachine : Machine Unit Bool Bool Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted _ _ := True

end Toy.CT
