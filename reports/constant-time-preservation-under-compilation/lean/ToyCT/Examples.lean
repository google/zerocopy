import ToyCT.Machines

/-
Positive and negative adequacy examples for every definition in `ToyCT.Defs`, plus
model-boundary counterexamples characterizing `ConstantTime`, `Terminates`, and
`WeakLeakageDetermined`. Every theorem in this module is proved without `sorry`.
-/

namespace Toy.CT

/-! ## Leakage Maps and Simulation Witnesses Used in Examples -/

/-- Secret-independent trace transformer mapping `branchlessSelect` (`[0]`) to
`branchlessLowered` (`[10, 11]`). -/
def selectToLoweredLeakMap : (Nat × Nat) → List Nat → List Nat :=
  fun _ tr =>
    match tr with
    | [0] => [10, 11]
    | _ => []

/-- Secret-independent, public-input-dependent trace transformer mapping
`branchlessLowered` (`[10, 11]`) to `branchlessEncoded` (`[100 + pub.1 % 2, 101 + pub.1 % 2]`). -/
def loweredToEncodedLeakMap : (Nat × Nat) → List Nat → List Nat :=
  fun pub tr =>
    match tr with
    | [10, 11] => [100 + pub.1 % 2, 101 + pub.1 % 2]
    | _ => []

/-- Secret-dependent trace transformer mapping `branchlessSelect` (`[0]`) to
`branchingSelect` (`[0, 1]` on `true`, `[0, 2]` on `false`). -/
def secretBranchLeakMap : (Nat × Nat) → Bool → List Nat → List Nat :=
  fun _ sec tr =>
    match tr with
    | [0] => [0, if sec then 1 else 2]
    | _ => []

/-- Step-level leakage transformer eliminating PC `0` (`nop` -> `[]`) and expanding
PC `1` (`select` -> `[10, 11]`). -/
def nopToLoweredStepLeak : (Nat × Nat) → Nat → List Nat :=
  fun _ pc =>
    match pc with
    | 0 => []
    | 1 => [10, 11]
    | _ => [pc]

/-- Anti-stuttering measure on `branchlessWithNop` configurations. -/
def nopSelectMeasure : NopSelectState → Nat
  | .nop _ _ _ => 2
  | .select _ _ _ => 1
  | .done _ => 0

/-- Simulation relation matching `branchlessWithNop` states to `branchlessLowered` states. -/
def nopToLoweredRel (_pub : Nat × Nat) (_sec : Bool)
    (s : NopSelectState) (t : LoweredSelectState) : Prop :=
  match s with
  | .nop a b cond => t = .mask a b cond
  | .select a b cond => t = .mask a b cond
  | .done v => t = .done v

/-- Simulation relation matching `twoStepConstSource` to `secretStutterTarget` under
state-dependent stuttering (`OptionStepLeakSim`): on `sec = true`, both source states `.s2`
and `.s1` map to target state `.s1` (stuttering on `.s2 -> .s1`). -/
def optionStutterRel (_pub : Unit) (sec : Bool) (s t : TwoStepState) : Prop :=
  if sec then
    (s = .s2 ∧ t = .s1) ∨ (s = .s1 ∧ t = .s1) ∨ (s = .s0 ∧ t = .s0)
  else
    s = t

/-! ## 1. `Steps` Examples -/

theorem steps_pos_example :
    Steps branchingSelect (.entry 10 20 true) [0, 1] (.done 10) :=
  Steps.cons (M := branchingSelect) ⟨rfl, rfl⟩
    (Steps.cons (M := branchingSelect) ⟨rfl, rfl⟩
      (Steps.nil (M := branchingSelect) _))

theorem steps_neg_example :
    ¬ Steps branchingSelect (.entry 10 20 true) [0, 2] (.done 10) := by
  intro h
  rcases (Steps.cons_iff (M := branchingSelect)).mp h with ⟨s₁, ⟨_, hs₁⟩, hrest⟩
  rw [hs₁] at hrest
  rcases (Steps.cons_iff (M := branchingSelect)).mp hrest with ⟨_, ⟨h₂, _⟩, _⟩
  cases h₂

/-! ## 2. `Executes` Examples -/

theorem executes_pos_example :
    Executes branchlessSelect (10, 20) true 10 [0] :=
  (branchlessSelect_executes_iff (10, 20) true 10 [0]).mpr ⟨rfl, rfl⟩

theorem executes_neg_example :
    ¬ Executes branchlessSelect (10, 20) true 20 [0] := by
  intro h
  have hout := ((branchlessSelect_executes_iff (10, 20) true 20 [0]).mp h).1
  cases hout

/-! ## 3. `HasTrace` Examples -/

theorem hasTrace_pos_example :
    HasTrace branchingSelect (10, 20) false [0, 2] :=
  (branchingSelect_hasTrace_iff (10, 20) false [0, 2]).mpr rfl

theorem hasTrace_neg_example :
    ¬ HasTrace branchingSelect (10, 20) false [0, 1] := by
  intro h
  have htr := (branchingSelect_hasTrace_iff (10, 20) false [0, 1]).mp h
  cases htr

/-! ## 4. `Reachable` Examples -/

theorem reachable_pos_example :
    Reachable branchingSelect (10, 20) true (.thenBlock 10) :=
  ⟨.entry 10 20 true, [0], rfl,
    Steps.cons (M := branchingSelect) ⟨rfl, rfl⟩ (Steps.nil (M := branchingSelect) _)⟩

theorem reachable_neg_example :
    ¬ Reachable branchingSelect (10, 20) true (.elseBlock 20) := by
  rintro ⟨s₀, tr, hs₀, hSteps⟩
  cases hSteps with
  | nil _ => cases hs₀
  | cons h₁ hrest =>
    subst hs₀
    rcases h₁ with ⟨_, hs₁⟩
    cases hrest with
    | nil _ => cases hs₁
    | cons h₂ hrest₂ =>
      rw [hs₁] at h₂
      rcases h₂ with ⟨_, hs₂⟩
      cases hrest₂ with
      | nil _ => cases hs₂
      | cons h₃ _ =>
        rw [hs₂] at h₃
        exact False.elim h₃

/-! ## 5. `HasInit` Examples -/

theorem hasInit_pos_example : HasInit branchlessSelect :=
  (hasInit_and_safe_of_det_terminates branchlessSelect_deterministic branchlessSelect_terminates).1

theorem hasInit_neg_example : ¬ HasInit emptyInitMachine := by
  intro h
  rcases h () false with ⟨_, hInit⟩
  exact hInit

/-! ## 6. `Safe` Examples -/

theorem safe_pos_example : Safe branchlessSelect :=
  (hasInit_and_safe_of_det_terminates branchlessSelect_deterministic branchlessSelect_terminates).2

theorem safe_nonterminating_pos_example : Safe silentLoopSource := by
  intro _ _ s _
  cases s
  exact Or.inr ⟨0, (), rfl, rfl, rfl⟩

theorem safe_neg_example : ¬ Safe stuckMachine := by
  intro hSafe
  have hReach : Reachable stuckMachine () false () :=
    ⟨(), [], rfl, Steps.nil (M := stuckMachine) ()⟩
  rcases hSafe () false () hReach with ⟨_, hHalt⟩ | ⟨_, _, hStep⟩
  · exact hHalt
  · exact hStep

/-! ## 7. `Terminates` Examples -/

theorem terminates_pos_example : Terminates branchlessSelect :=
  branchlessSelect_terminates

theorem terminates_neg_example : ¬ Terminates silentLoopSource := by
  intro hTerm
  rcases hTerm () false with ⟨_, _, _, _, _, _, hHalt⟩
  exact hHalt

/-! ## 8. `Deterministic`, `OutputDeterministic`, `TraceUnique`, and `HaltAgree` Examples -/

theorem deterministic_pos_example : Deterministic branchlessSelect :=
  branchlessSelect_deterministic

theorem deterministic_neg_example : ¬ Deterministic nondetSecretBranchTarget := by
  intro hDet
  have h₀ : nondetSecretBranchTarget.step (.start true) 0 .done := ⟨Or.inl rfl, rfl⟩
  have h₁ : nondetSecretBranchTarget.step (.start true) 1 .done := ⟨Or.inr rfl, rfl⟩
  have heq : (0 : Nat) = 1 := (hDet.step_det (.start true) 0 .done 1 .done h₀ h₁).1
  cases heq

theorem outputDeterministic_pos_example : OutputDeterministic branchlessSelect := by
  intro _ _ _ h₁ h₂
  cases h₁
  cases h₂
  rfl

theorem outputDeterministic_neg_example : ¬ OutputDeterministic ambiguousOutputMachine := by
  intro hOut
  have heq : false = true := hOut () false true trivial trivial
  cases heq

theorem traceUnique_pos_example : TraceUnique branchlessSelect :=
  branchlessSelect_deterministic.traceUnique

theorem traceUnique_neg_example : ¬ TraceUnique coinFlip :=
  coinFlip_not_traceUnique

theorem haltAgree_pos_example : HaltAgree branchlessSelect branchingSelect :=
  haltAgree_of_terminates branchlessSelect_terminates branchingSelect_terminates

theorem haltAgree_neg_example : ¬ HaltAgree allHalt haltIfTrue := by
  intro hHalt
  have hAll : ∃ tr, HasTrace allHalt () false tr :=
    ⟨[], (allHalt_hasTrace_iff false []).mpr rfl⟩
  rcases (hHalt () false).mp hAll with ⟨tr, hIf⟩
  have hf := ((haltIfTrue_hasTrace_iff false tr).mp hIf).1
  cases hf

/-! ## 9. `ConstantTime` Adequacy and Boundary Examples -/

theorem constantTime_pos_example : ConstantTime branchlessSelect :=
  branchlessSelect_constantTime

theorem constantTime_nondet_pos_example : ConstantTime coinFlip :=
  coinFlip_constantTime

theorem constantTime_neg_example : ¬ ConstantTime branchingSelect :=
  branchingSelect_not_constantTime

theorem constantTime_abort_neg_example : ¬ ConstantTime abortOnSecret := by
  intro hCT
  have hFalse : HasTrace abortOnSecret () false [] :=
    ⟨(), false, false, rfl, Steps.nil (M := abortOnSecret) false, ⟨rfl, rfl⟩⟩
  have hTrue : HasTrace abortOnSecret () true [] :=
    (hCT () false true []).mp hFalse
  rcases hTrue with ⟨_, s₀, sf, hs₀, hSteps, hHalt⟩
  have hsf : sf = s₀ := (Steps.nil_iff (M := abortOnSecret)).mp hSteps
  rw [hsf, hs₀] at hHalt
  exact Bool.noConfusion hHalt.1

/-- Boundary of halting-trace `ConstantTime` on diverging programs: `leakyLoop` reveals
`sec` at its first step (`1` on `true`, `0` on `false`) yet satisfies `ConstantTime`
vacuously because no execution halts. -/
theorem leakyLoop_constantTime_despite_diverging_step_leak :
    ConstantTime leakyLoop ∧
    (∀ (sec : Bool) l s', leakyLoop.step sec l s' → l = if sec then 1 else 0) :=
  ⟨leakyLoop_constantTime, fun _ _ _ h => h.1⟩

/-- Boundary of halting-trace `ConstantTime` under trace-inclusion refinement: `haltIfTrue`'s
halting traces are a subset of `allHalt`'s on every input and `ConstantTime allHalt` holds,
yet `ConstantTime haltIfTrue` fails because `ConstantTime` is termination-sensitive. -/
theorem constantTime_not_refinement_closed :
    (∀ sec tr, HasTrace haltIfTrue () sec tr → HasTrace allHalt () sec tr) ∧
    ConstantTime allHalt ∧
    ¬ ConstantTime haltIfTrue := by
  refine ⟨?_, allHalt_constantTime, haltIfTrue_not_constantTime⟩
  intro sec tr h
  have htr : tr = [] := ((haltIfTrue_hasTrace_iff sec tr).mp h).2
  subst htr
  exact (allHalt_hasTrace_iff sec []).mpr rfl

/-- Boundary of existential `Terminates` on nondeterministic machines: `haltOrLeak`
satisfies both `Terminates` and `ConstantTime`, yet from `.start sec` can enter a
non-halting branch whose first step leaks `if sec then 1 else 0`. -/
theorem terminates_and_constantTime_unconstrained_diverging_branch :
    Terminates haltOrLeak ∧
    ConstantTime haltOrLeak ∧
    (∀ sec, haltOrLeak.step (.start sec) (if sec then 1 else 0) (.loop sec)) ∧
    (∀ sec tr sf, Steps haltOrLeak (.loop sec) tr sf → ¬ haltOrLeak.halted sf ()) := by
  refine ⟨haltOrLeak_terminates, haltOrLeak_constantTime, fun _ => ⟨rfl, rfl⟩, ?_⟩
  intro sec tr sf hSteps
  have aux : ∀ {x y : haltOrLeak.State} {t : List Nat},
      Steps haltOrLeak x t y → (∃ b, x = .loop b) → ∃ b, y = .loop b := by
    intro x y t h
    induction h with
    | nil _ => exact id
    | cons hs _ ih =>
      rintro ⟨_, _⟩
      exact ih (haltOrLeak_step_loop hs)
  rcases aux hSteps ⟨sec, rfl⟩ with ⟨b, hsf⟩
  rw [hsf]
  exact id

/-! ## 10. `FunctionallyCorrect` Examples -/

theorem functionallyCorrect_pos_example :
    FunctionallyCorrect branchlessSelect branchingSelect :=
  branchless_branching_functionallyCorrect

theorem functionallyCorrect_neg_example :
    ¬ FunctionallyCorrect branchlessSelect wrongOutputSelect := by
  intro hFC
  have hSrc : ∃ trS, Executes branchlessSelect (5, 5) true 5 trS :=
    ⟨[0], (branchlessSelect_executes_iff (5, 5) true 5 [0]).mpr ⟨rfl, rfl⟩⟩
  rcases (hFC (5, 5) true 5).mp hSrc with ⟨trT, s₀, sf, hs₀, hSteps, hHalt⟩
  cases hSteps with
  | nil _ =>
    subst hs₀
    exact Bool.noConfusion hHalt.1
  | cons h₁ hrest =>
    rcases h₁ with ⟨_, _, hs₁⟩
    cases hrest with
    | nil _ => cases hHalt.2
    | cons h₂ _ =>
      rw [hs₁] at h₂
      exact Bool.noConfusion h₂.1

/-! ## 11. `LeakageDetermined` and `WeakLeakageDetermined` Examples -/

theorem leakageDetermined_pos_example :
    LeakageDetermined branchlessSelect branchlessLowered selectToLoweredLeakMap := by
  intro pub sec trT
  rw [branchlessLowered_hasTrace_iff]
  constructor
  · rintro rfl
    exact ⟨[0], (branchlessSelect_hasTrace_iff pub sec [0]).mpr rfl, rfl⟩
  · rintro ⟨trS, hS, rfl⟩
    have htrS : trS = [0] := (branchlessSelect_hasTrace_iff pub sec trS).mp hS
    subst htrS
    rfl

theorem leakageDetermined_neg_example :
    ∀ f, ¬ LeakageDetermined branchlessSelect branchingSelect f := by
  intro f hLD
  have hTrue : HasTrace branchingSelect (0, 0) true [0, 1] :=
    (branchingSelect_hasTrace_iff (0, 0) true [0, 1]).mpr rfl
  have hFalse : HasTrace branchingSelect (0, 0) false [0, 2] :=
    (branchingSelect_hasTrace_iff (0, 0) false [0, 2]).mpr rfl
  rcases (hLD (0, 0) true [0, 1]).mp hTrue with ⟨tr₁, hS₁, heq₁⟩
  rcases (hLD (0, 0) false [0, 2]).mp hFalse with ⟨tr₂, hS₂, heq₂⟩
  have h₁ : tr₁ = [0] := (branchlessSelect_hasTrace_iff (0, 0) true tr₁).mp hS₁
  have h₂ : tr₂ = [0] := (branchlessSelect_hasTrace_iff (0, 0) false tr₂).mp hS₂
  subst h₁; subst h₂
  rw [← heq₁] at heq₂
  cases heq₂

theorem weakLeakageDetermined_pos_example :
    WeakLeakageDetermined coinFlip constOneStep (fun _ tr => tr) ∧
    ¬ LeakageDetermined coinFlip constOneStep (fun _ tr => tr) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro pub sec trT hT
    have htr : trT = [0] := (constOneStep_hasTrace_iff pub sec trT).mp hT
    subst htr
    exact ⟨[0], (coinFlip_hasTrace_iff pub sec [0]).mpr (Or.inl rfl), rfl⟩
  · intro pub sec _ _
    exact ⟨[0], (constOneStep_hasTrace_iff pub sec [0]).mpr rfl⟩
  · intro hLD
    have h₁ : HasTrace constOneStep () false [1] :=
      (hLD () false [1]).mpr ⟨[1], (coinFlip_hasTrace_iff () false [1]).mpr (Or.inr rfl), rfl⟩
    have heq : [1] = [0] := (constOneStep_hasTrace_iff () false [1]).mp h₁
    cases heq

theorem weakLeakageDetermined_neg_example :
    ∀ f, ¬ WeakLeakageDetermined branchlessSelect branchingSelect f := by
  intro f hWeak
  have hCT : ConstantTime branchingSelect :=
    weakLeakageDetermined_preserves_ct_of_traceUnique
      hWeak branchlessSelect_deterministic.traceUnique branchlessSelect_constantTime
  exact branchingSelect_not_constantTime hCT

/-- Without `TraceUnique S`, one-way `WeakLeakageDetermined` fails to preserve
`ConstantTime`: `coinFlip` (`{[0], [1]}` on all secrets) satisfies `WeakLeakageDetermined`
into `nondetSecretBranchTarget` (`{[0]}` on `false`, `{[0], [1]}` on `true`), yet
`nondetSecretBranchTarget` is not `ConstantTime`. -/
theorem weakLeakageDetermined_fails_without_traceUnique :
    WeakLeakageDetermined coinFlip nondetSecretBranchTarget (fun _ tr => tr) ∧
    ConstantTime coinFlip ∧
    ¬ ConstantTime nondetSecretBranchTarget := by
  refine ⟨⟨?_, ?_⟩, coinFlip_constantTime, ?_⟩
  · rintro _ sec trT ⟨_, s₀, sf, hs₀, hSteps, hHalt⟩
    cases hSteps with
    | nil _ =>
      rw [hs₀] at hHalt
      exact False.elim (NondetTargetState.noConfusion hHalt.1)
    | cons h₁ hrest =>
      rw [hs₀] at h₁
      cases sec with
      | false =>
        rcases h₁ with ⟨rfl, hs₁⟩
        cases hrest with
        | nil _ => exact ⟨[0], (coinFlip_hasTrace_iff () false [0]).mpr (Or.inl rfl), rfl⟩
        | cons h₂ _ => rw [hs₁] at h₂; exact False.elim h₂
      | true =>
        rcases h₁ with ⟨hl, hs₁⟩
        cases hrest with
        | nil _ =>
          rcases hl with rfl | rfl
          · exact ⟨[0], (coinFlip_hasTrace_iff () true [0]).mpr (Or.inl rfl), rfl⟩
          · exact ⟨[1], (coinFlip_hasTrace_iff () true [1]).mpr (Or.inr rfl), rfl⟩
        | cons h₂ _ => rw [hs₁] at h₂; exact False.elim h₂
  · intro _ sec _ _
    rcases nondetSecretBranchTarget_terminates () sec with ⟨out, trT, hex⟩
    exact ⟨trT, out, hex⟩
  · intro hCT
    have hT : HasTrace nondetSecretBranchTarget () true [1] :=
      ⟨(), .start true, .done, rfl,
        Steps.cons (M := nondetSecretBranchTarget) ⟨Or.inr rfl, rfl⟩
          (Steps.nil (M := nondetSecretBranchTarget) .done), ⟨rfl, rfl⟩⟩
    rcases (hCT () true false [1]).mp hT with ⟨_, s₀, _, hs₀, hSteps, _⟩
    subst hs₀
    rcases (Steps.cons_iff (M := nondetSecretBranchTarget)).mp hSteps with ⟨_, ⟨hl, _⟩, _⟩
    cases hl

/-! ## 12. `SecretDependentLeakageDetermined` Examples -/

theorem secretDependentLeakageDetermined_pos_example :
    SecretDependentLeakageDetermined branchlessSelect branchingSelect secretBranchLeakMap := by
  intro pub sec trT
  rw [branchingSelect_hasTrace_iff]
  constructor
  · rintro rfl
    exact ⟨[0], (branchlessSelect_hasTrace_iff pub sec [0]).mpr rfl, rfl⟩
  · rintro ⟨trS, hS, rfl⟩
    have htrS : trS = [0] := (branchlessSelect_hasTrace_iff pub sec trS).mp hS
    subst htrS
    rfl

theorem secretDependentLeakageDetermined_neg_example :
    ¬ SecretDependentLeakageDetermined branchlessSelect branchingSelect (fun _ _ _ => [99]) := by
  intro hSD
  have hTrue : HasTrace branchingSelect (0, 0) true [0, 1] :=
    (branchingSelect_hasTrace_iff (0, 0) true [0, 1]).mpr rfl
  rcases (hSD (0, 0) true [0, 1]).mp hTrue with ⟨_, _, heq⟩
  cases heq

/-! ## 13. `liftStepLeak` Examples -/

theorem liftStepLeak_pos_example :
    liftStepLeak nopToLoweredStepLeak (7, 8) [0, 1] = [10, 11] := rfl

theorem liftStepLeak_neg_example :
    liftStepLeak nopToLoweredStepLeak (7, 8) [0, 1] ≠ [0, 1] := by
  intro h
  cases h

/-! ## 14. `StepLeakSim`, `UnmeasuredStepLeakSim`, and `OptionStepLeakSim` Examples -/

theorem stepLeakSim_pos_example :
    StepLeakSim branchlessWithNop branchlessLowered
      nopToLoweredStepLeak nopSelectMeasure nopToLoweredRel where
  init_sim pub sec s₀ hs₀ := by
    subst hs₀
    exact ⟨.mask pub.1 pub.2 sec, rfl, rfl⟩
  halted_sim _ _ s t out hR hHalt := by
    cases hHalt
    exact hR
  step_sim _ _ s ls s' t hR hStep := by
    cases s with
    | nop a b cond =>
      rcases hStep with ⟨rfl, rfl⟩
      subst hR
      refine ⟨⟨.mask a b cond, Steps.nil (M := branchlessLowered) _, rfl⟩, ?_⟩
      intro _
      exact Nat.lt_succ_self 1
    | select a b cond =>
      rcases hStep with ⟨rfl, rfl⟩
      subst hR
      refine ⟨⟨.done (if cond then a else b),
        Steps.cons (M := branchlessLowered) ⟨rfl, rfl⟩
          (Steps.cons (M := branchlessLowered) ⟨rfl, rfl⟩
            (Steps.nil (M := branchlessLowered) _)), rfl⟩, ?_⟩
      intro hNil
      cases hNil
    | done _ => exact False.elim hStep

private theorem branchingSelect_steps_to_done_trace
    {a b out : Nat} {cond : Bool} {tr : List Nat} {tf : BranchSelectState}
    (hSteps : Steps branchingSelect (.entry a b cond) tr tf)
    (hHalt : branchingSelect.halted tf out) :
    tr = [0, if cond then 1 else 2] := by
  have hex : Executes branchingSelect (a, b) cond out tr :=
    ⟨.entry a b cond, tf, rfl, hSteps, hHalt⟩
  exact ((branchingSelect_executes_iff (a, b) cond out tr).mp hex).2

theorem stepLeakSim_neg_example :
    ∀ stepLeak measure R,
      ¬ StepLeakSim branchlessSelect branchingSelect stepLeak measure R := by
  intro stepLeak measure R hSim
  rcases hSim.init_sim (0, 0) true (.entry 0 0 true) rfl with ⟨t₀T, ht₀T, hRT⟩
  subst ht₀T
  have hStepT : branchlessSelect.step (.entry 0 0 true) 0 (.done 0) := ⟨rfl, rfl⟩
  rcases (hSim.step_sim (0, 0) true _ 0 _ _ hRT hStepT).1 with ⟨tfT, hStepsT, hRfT⟩
  have hHaltT : branchingSelect.halted tfT 0 := hSim.halted_sim (0, 0) true _ tfT 0 hRfT rfl
  have hEqT : stepLeak (0, 0) 0 = [0, 1] := branchingSelect_steps_to_done_trace hStepsT hHaltT
  rcases hSim.init_sim (0, 0) false (.entry 0 0 false) rfl with ⟨t₀F, ht₀F, hRF⟩
  subst ht₀F
  have hStepF : branchlessSelect.step (.entry 0 0 false) 0 (.done 0) := ⟨rfl, rfl⟩
  rcases (hSim.step_sim (0, 0) false _ 0 _ _ hRF hStepF).1 with ⟨tfF, hStepsF, hRfF⟩
  have hHaltF : branchingSelect.halted tfF 0 := hSim.halted_sim (0, 0) false _ tfF 0 hRfF rfl
  have hEqF : stepLeak (0, 0) 0 = [0, 2] := branchingSelect_steps_to_done_trace hStepsF hHaltF
  rw [hEqT] at hEqF
  cases hEqF

theorem unmeasuredStepLeakSim_pos_example :
    UnmeasuredStepLeakSim silentLoopSource trivialHaltedMachine
      (fun _ _ => []) (fun _ _ _ _ => True) where
  init_sim _ _ _ _ := ⟨(), rfl, trivial⟩
  halted_sim _ _ _ _ _ _ hHalt := False.elim hHalt
  step_sim _ _ _ _ _ t _ _ := ⟨t, Steps.nil (M := trivialHaltedMachine) t, trivial⟩

theorem unmeasuredStepLeakSim_neg_example :
    ¬ UnmeasuredStepLeakSim constOneStep trivialHaltedMachine
        (fun _ l => [l]) (fun _ _ _ _ => True) := by
  intro hSim
  rcases hSim.step_sim () false false 0 true () trivial ⟨rfl, rfl, rfl⟩ with ⟨_, hSteps, _⟩
  rcases (Steps.cons_iff (M := trivialHaltedMachine)).mp hSteps with ⟨_, hstep, _⟩
  exact hstep

theorem optionStepLeakSim_pos_example :
    OptionStepLeakSim twoStepConstSource secretStutterTarget
      (fun _ l => [l]) twoStepMeasure optionStutterRel where
  init_sim _ sec s₀ hs₀ := by
    subst hs₀
    cases sec with
    | false => exact ⟨.s2, rfl, rfl⟩
    | true => exact ⟨.s1, rfl, Or.inl ⟨rfl, rfl⟩⟩
  halted_sim _ sec s t out hR hHalt := by
    rcases hHalt with ⟨rfl, rfl⟩
    cases sec with
    | false =>
      have ht : t = .s0 := hR.symm
      exact ⟨ht, rfl⟩
    | true =>
      rcases hR with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, ht⟩
      · cases h
      · cases h
      · exact ⟨ht, rfl⟩
  step_sim _ sec s ls s' t hR hStep := by
    cases sec with
    | false =>
      have ht : s = t := hR
      subst ht
      cases (s : TwoStepState) with
      | s2 =>
        rcases hStep with ⟨rfl, rfl⟩
        exact Or.inl ⟨.s1, Steps.cons (M := secretStutterTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := secretStutterTarget) .s1), rfl⟩
      | s1 =>
        rcases hStep with ⟨rfl, rfl⟩
        exact Or.inl ⟨.s0, Steps.cons (M := secretStutterTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := secretStutterTarget) .s0), rfl⟩
      | s0 => exact False.elim hStep
    | true =>
      rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, _⟩
      · rcases hStep with ⟨rfl, rfl⟩
        exact Or.inr ⟨Nat.lt_succ_self 1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · rcases hStep with ⟨rfl, rfl⟩
        exact Or.inl ⟨.s0, Steps.cons (M := secretStutterTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := secretStutterTarget) .s0), Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      · exact False.elim hStep

theorem optionStepLeakSim_neg_example :
    ¬ OptionStepLeakSim constOneStep trivialHaltedMachine
        (fun _ l => [l]) (fun _ => 0) (fun _ _ _ _ => True) := by
  intro hSim
  rcases hSim.step_sim () false false 0 true () trivial ⟨rfl, rfl, rfl⟩ with
    ⟨_, hSteps, _⟩ | ⟨hLt, _⟩
  · rcases (Steps.cons_iff (M := trivialHaltedMachine)).mp hSteps with ⟨_, hstep, _⟩
    exact hstep
  · exact Nat.lt_irrefl 0 hLt

/-! ## 15. `composeLeakMap` Examples -/

theorem composeLeakMap_pos_example :
    composeLeakMap selectToLoweredLeakMap loweredToEncodedLeakMap (1, 0) [0] = [101, 102] := rfl

theorem composeLeakMap_neg_example :
    composeLeakMap selectToLoweredLeakMap loweredToEncodedLeakMap (1, 0) [0] ≠ [100, 101] := by
  intro h
  cases h

end Toy.CT
