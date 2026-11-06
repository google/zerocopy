import AnnealResearch.Execution

set_option Elab.async false

/-!
Realistic agent-assisted development evaluation pilot for `R-ADEV-07` (`E-ADEV-06`).
Models the 6-task population (`0..5`), five submission archetypes (`0..4`),
`OriginalClaimOracle` coupled to `AnnealResearch.Execution.NoUB`,
`UnpinnedProofCountOracle`, `ClaimPinnedDiagnosticOracle`, and `WorkflowCostLedger`.
-/

namespace AnnealResearch.AgentTaskEvaluation

abbrev TaskId := Nat

noncomputable def taskSpec (task : TaskId) : TaskId × Nat × Nat × Nat :=
  (task, task + 1, task + 11, 20)

abbrev CandidateSubmission :=
  TaskId × Nat × Nat × Bool × Bool × Bool × Bool × Nat × Bool × Nat × Nat

noncomputable def archetypeSubmission (task : TaskId) : Nat → CandidateSubmission
  | 0 => (task, task + 1, task + 11, true, true, true, true, 0, true, 1, 6)
  | 1 => (task, task + 1, task + 11, false, false, true, true, 2, false, 0, 5)
  | 2 => (task, task + 1, task + 11, true, false, false, true, 0, false, 0, 6)
  | 3 => (task, (task + 1) + 1, task + 11, true, false, false, true, 0, true, 2, 5)
  | _ + 4 => (task, task + 1, (task + 11) + 1, true, true, true, false, 0, true, 1, 4)

abbrev TaskExecState := Bool × Nat

def TaskBad (s : TaskExecState) : Prop := s.1 = true

def TaskStep (sub : CandidateSubmission) (s t : TaskExecState) : Prop :=
  (sub.2.2.2.2.1 = true ∧ s = (false, 0) ∧ t = (false, 1)) ∨
  (sub.2.2.2.2.1 = true ∧ s = (false, 1) ∧ t = (false, 10 + sub.2.2.2.2.2.2.2.1)) ∨
  (sub.2.2.2.2.1 = false ∧ s = (false, 0) ∧ t = (true, 2)) ∨
  (sub.2.2.2.2.1 = false ∧ s = (true, 2) ∧ t = (false, 10 + sub.2.2.2.2.2.2.2.1))

noncomputable def diagnoseSubmission (task : TaskId) (sub : CandidateSubmission) : Nat :=
  if !((sub.1 == task) && (sub.2.1 == (taskSpec task).2.1)) then 1
  else if !((sub.2.2.1 == (taskSpec task).2.2.1) && sub.2.2.2.2.2.2.1) then 4
  else if !sub.2.2.2.1 then 2
  else if !(sub.2.2.2.2.1 && sub.2.2.2.2.2.1) then 3
  else 0

noncomputable def OriginalClaimOracle (task : TaskId) (sub : CandidateSubmission) : Bool :=
  ((sub.1 == task) && (sub.2.1 == (taskSpec task).2.1)) &&
  ((sub.2.2.1 == (taskSpec task).2.2.1) && sub.2.2.2.2.2.2.1) &&
  sub.2.2.2.1 &&
  (sub.2.2.2.2.1 && sub.2.2.2.2.2.1)

noncomputable def ClaimPinnedDiagnosticOracle (task : TaskId) (sub : CandidateSubmission) : Bool :=
  diagnoseSubmission task sub == 0

noncomputable def UnpinnedProofCountOracle (_task : TaskId) (sub : CandidateSubmission) : Bool :=
  sub.2.2.2.2.2.2.2.2.1 && Nat.ble 1 sub.2.2.2.2.2.2.2.2.2.1

theorem original_claim_oracle_sound_for_noUB (task : TaskId) (sub : CandidateSubmission)
    (hAccept : OriginalClaimOracle task sub = true) :
    Execution.NoUB (TaskStep sub) TaskBad (false, 0) ∧
    (sub.2.1 == (taskSpec task).2.1) = true := by
  have hHash : (sub.2.1 == (taskSpec task).2.1) = true := by
    revert hAccept; unfold OriginalClaimOracle
    cases (sub.1 == task) <;> cases (sub.2.1 == (taskSpec task).2.1) <;>
    intro hAccept <;> first | rfl | exact hAccept
  have hSafe : sub.2.2.2.2.1 = true := by
    revert hAccept; unfold OriginalClaimOracle
    cases ((sub.1 == task) && (sub.2.1 == (taskSpec task).2.1)) <;>
    cases ((sub.2.2.1 == (taskSpec task).2.2.1) && sub.2.2.2.2.2.2.1) <;>
    cases sub.2.2.2.1 <;> cases sub.2.2.2.2.1 <;>
    intro hAccept <;> first | rfl | exact hAccept
  refine ⟨?_, hHash⟩
  apply Execution.invariant_noUB (Invariant := fun s => s.1 = false)
  · rfl
  · intro s t _hs edge
    cases edge with
    | inl h1 => rw [h1.2.2]
    | inr hRest1 =>
      cases hRest1 with
      | inl h2 => rw [h2.2.2]
      | inr hRest2 =>
        cases hRest2 with
        | inl h3 => have hFalse := h3.1; rw [hSafe] at hFalse; cases hFalse
        | inr h4 => have hFalse := h4.1; rw [hSafe] at hFalse; cases hFalse
  · intro s hs hBad; change s.1 = true at hBad; rw [hs] at hBad; cases hBad

theorem claim_pinned_workflow_matches_original_oracle (task : TaskId) (sub : CandidateSubmission) :
    ClaimPinnedDiagnosticOracle task sub = OriginalClaimOracle task sub ∧
    (ClaimPinnedDiagnosticOracle task sub = true ↔ OriginalClaimOracle task sub = true) := by
  have hEq : ClaimPinnedDiagnosticOracle task sub = OriginalClaimOracle task sub := by
    unfold ClaimPinnedDiagnosticOracle diagnoseSubmission OriginalClaimOracle
    cases ((sub.1 == task) && (sub.2.1 == (taskSpec task).2.1)) <;>
    cases ((sub.2.2.1 == (taskSpec task).2.2.1) && sub.2.2.2.2.2.2.1) <;>
    cases sub.2.2.2.1 <;> cases (sub.2.2.2.2.1 && sub.2.2.2.2.2.1) <;> rfl
  refine ⟨hEq, ?_⟩; rw [hEq]

theorem verified_repairs_succeed_on_all_six_tasks (task : TaskId) :
    ClaimPinnedDiagnosticOracle task (archetypeSubmission task 0) = true ∧
    OriginalClaimOracle task (archetypeSubmission task 0) = true ∧
    diagnoseSubmission task (archetypeSubmission task 0) = 0 ∧
    Execution.NoUB (TaskStep (archetypeSubmission task 0)) TaskBad (false, 0) := by
  have hBeqSelf : ∀ n : Nat, (n == n) = true := fun n => decide_eq_true rfl
  have hDiag : diagnoseSubmission task (archetypeSubmission task 0) = 0 := by
    change (if !((task == task) && (task + 1 == task + 1)) then 1
      else if !((task + 11 == task + 11) && true) then 4
      else if !true then 2 else if !(true && true) then 3 else 0) = 0
    rw [hBeqSelf task, hBeqSelf (task + 1), hBeqSelf (task + 11)]; rfl
  have hPinned : ClaimPinnedDiagnosticOracle task (archetypeSubmission task 0) = true := by
    unfold ClaimPinnedDiagnosticOracle; rw [hDiag]; rfl
  have hOracle : OriginalClaimOracle task (archetypeSubmission task 0) = true := by
    rw [← (claim_pinned_workflow_matches_original_oracle task _).1]; exact hPinned
  exact ⟨hPinned, hOracle, hDiag, (original_claim_oracle_sound_for_noUB task _ hOracle).1⟩

theorem diagnostic_feedback_identifies_exact_defect_class (task : TaskId) (k : Nat) :
    diagnoseSubmission task (archetypeSubmission task 1) = 2 ∧
    diagnoseSubmission task (archetypeSubmission task 2) = 3 ∧
    diagnoseSubmission task (archetypeSubmission task 3) = 1 ∧
    diagnoseSubmission task (archetypeSubmission task 4) = 4 ∧
    diagnoseSubmission task (archetypeSubmission task (k + 4)) = 4 := by
  have hBeqSelf : ∀ n : Nat, (n == n) = true := fun n => decide_eq_true rfl
  have hNe : ∀ n : Nat, n + 1 ≠ n := by
    intro n; induction n with
    | zero => intro h; cases h
    | succ m ih => intro h; exact ih (Nat.succ.inj h)
  have hSuccFalse : ∀ n : Nat, (n + 1 == n) = false := fun n => decide_eq_false (hNe n)
  have h1 : diagnoseSubmission task (archetypeSubmission task 1) = 2 := by
    change (if !((task == task) && (task + 1 == task + 1)) then 1
      else if !((task + 11 == task + 11) && true) then 4
      else if !false then 2 else if !(false && true) then 3 else 0) = 2
    rw [hBeqSelf task, hBeqSelf (task + 1), hBeqSelf (task + 11)]; rfl
  have h2 : diagnoseSubmission task (archetypeSubmission task 2) = 3 := by
    change (if !((task == task) && (task + 1 == task + 1)) then 1
      else if !((task + 11 == task + 11) && true) then 4
      else if !true then 2 else if !(false && false) then 3 else 0) = 3
    rw [hBeqSelf task, hBeqSelf (task + 1), hBeqSelf (task + 11)]; rfl
  have h3 : diagnoseSubmission task (archetypeSubmission task 3) = 1 := by
    change (if !((task == task) && ((task + 1) + 1 == task + 1)) then 1
      else if !((task + 11 == task + 11) && true) then 4
      else if !true then 2 else if !(false && false) then 3 else 0) = 1
    rw [hBeqSelf task, hSuccFalse (task + 1)]; rfl
  have h4 : ∀ m : Nat, diagnoseSubmission task (archetypeSubmission task (m + 4)) = 4 := by
    intro m
    change (if !((task == task) && (task + 1 == task + 1)) then 1
      else if !(((task + 11) + 1 == task + 11) && false) then 4
      else if !true then 2 else if !(true && true) then 3 else 0) = 4
    rw [hBeqSelf task, hBeqSelf (task + 1), hSuccFalse (task + 11)]; rfl
  exact ⟨h1, h2, h3, h4 0, h4 k⟩

noncomputable def applyDiagnosticRepair (task : TaskId) (initialSub : CandidateSubmission) : CandidateSubmission :=
  if diagnoseSubmission task initialSub == 0 then initialSub else archetypeSubmission task 0

noncomputable def twoStepRepairTotalCost (task : TaskId) (initialSub : CandidateSubmission) : Nat :=
  initialSub.2.2.2.2.2.2.2.2.2.2 + 2 + (if diagnoseSubmission task initialSub == 0 then 0 else 8)

theorem diagnostic_guided_repair_converges_within_budget (task : TaskId) (kind : Nat) :
    OriginalClaimOracle task (applyDiagnosticRepair task (archetypeSubmission task kind)) = true ∧
    ClaimPinnedDiagnosticOracle task (applyDiagnosticRepair task (archetypeSubmission task kind)) = true ∧
    Execution.NoUB
      (TaskStep (applyDiagnosticRepair task (archetypeSubmission task kind)))
      TaskBad
      (false, 0) ∧
    twoStepRepairTotalCost task (archetypeSubmission task kind) ≤ (taskSpec task).2.2.2 := by
  have hVer := verified_repairs_succeed_on_all_six_tasks task
  have hRep : applyDiagnosticRepair task (archetypeSubmission task kind) = archetypeSubmission task 0 := by
    unfold applyDiagnosticRepair
    cases kind with
    | zero => rw [hVer.2.2.1]; rfl
    | succ k1 =>
      cases k1 with
      | zero => rw [(diagnostic_feedback_identifies_exact_defect_class task 0).1]; rfl
      | succ k2 =>
        cases k2 with
        | zero => rw [(diagnostic_feedback_identifies_exact_defect_class task 0).2.1]; rfl
        | succ k3 =>
          cases k3 with
          | zero => rw [(diagnostic_feedback_identifies_exact_defect_class task 0).2.2.1]; rfl
          | succ k4 => rw [(diagnostic_feedback_identifies_exact_defect_class task k4).2.2.2.2]; rfl
  have hBudget : twoStepRepairTotalCost task (archetypeSubmission task kind) ≤ (taskSpec task).2.2.2 := by
    unfold twoStepRepairTotalCost
    cases kind with
    | zero => rw [hVer.2.2.1]; change 8 ≤ 20; decide
    | succ k1 =>
      cases k1 with
      | zero => rw [(diagnostic_feedback_identifies_exact_defect_class task 0).1]; change 15 ≤ 20; decide
      | succ k2 =>
        cases k2 with
        | zero => rw [(diagnostic_feedback_identifies_exact_defect_class task 0).2.1]; change 16 ≤ 20; decide
        | succ k3 =>
          cases k3 with
          | zero => rw [(diagnostic_feedback_identifies_exact_defect_class task 0).2.2.1]; change 15 ≤ 20; decide
          | succ k4 => rw [(diagnostic_feedback_identifies_exact_defect_class task k4).2.2.2.2]; change 14 ≤ 20; decide
  rw [hRep]; exact ⟨hVer.2.1, hVer.1, hVer.2.2.2, hBudget⟩

abbrev WorkflowCostLedger := Nat × Nat × Nat × Nat × Nat

noncomputable def sumNatList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNatList xs

noncomputable def totalCampaignCost (ledger : WorkflowCostLedger) (perTaskCosts : List Nat) : Nat :=
  ledger.1 + sumNatList perTaskCosts

theorem shared_setup_accounting_explicit (ledger : WorkflowCostLedger) (perTaskCosts : List Nat) :
    totalCampaignCost ledger perTaskCosts = ledger.1 + sumNatList perTaskCosts ∧
    (0 < ledger.1 → sumNatList perTaskCosts < totalCampaignCost ledger perTaskCosts) := by
  refine ⟨rfl, ?_⟩; intro hPos; unfold totalCampaignCost
  induction (sumNatList perTaskCosts) with
  | zero => exact hPos
  | succ _ ih => exact Nat.succ_le_succ ih

#print axioms original_claim_oracle_sound_for_noUB
#print axioms claim_pinned_workflow_matches_original_oracle
#print axioms verified_repairs_succeed_on_all_six_tasks
#print axioms diagnostic_feedback_identifies_exact_defect_class
#print axioms diagnostic_guided_repair_converges_within_budget
#print axioms shared_setup_accounting_explicit

end AnnealResearch.AgentTaskEvaluation
