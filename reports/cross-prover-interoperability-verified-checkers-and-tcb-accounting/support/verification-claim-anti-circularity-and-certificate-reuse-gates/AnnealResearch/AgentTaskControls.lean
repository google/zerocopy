import AnnealResearch.AgentTaskEvaluation

set_option Elab.async false

/-!
Evaluation controls for `R-ADEV-07` (`E-ADEV-06`).
Proves that unpinned theorem-checking and theorem-count metrics falsely accept
contract weakening, inflated lemma counts, and stale subject bindings, that
symptom-masking fixes violate prefix `Execution.NoUB` despite matching surface
return tags, and that `ClaimPinnedDiagnosticOracle` matches `OriginalClaimOracle`
across all 30 task-submission pairs.
-/

namespace AnnealResearch.AgentTaskControls

open AnnealResearch.AgentTaskEvaluation

theorem tempting_contract_weakening_passes_unpinned_checker (task : TaskId) :
    (archetypeSubmission task 3).2.2.2.2.2.2.2.2.1 = true ∧
    UnpinnedProofCountOracle task (archetypeSubmission task 3) = true ∧
    OriginalClaimOracle task (archetypeSubmission task 3) = false ∧
    ClaimPinnedDiagnosticOracle task (archetypeSubmission task 3) = false ∧
    diagnoseSubmission task (archetypeSubmission task 3) = 1 ∧
    ¬ Execution.NoUB (TaskStep (archetypeSubmission task 3)) TaskBad (false, 0) := by
  have hDiag := (diagnostic_feedback_identifies_exact_defect_class task 0).2.2.1
  have hPinned : ClaimPinnedDiagnosticOracle task (archetypeSubmission task 3) = false := by
    unfold ClaimPinnedDiagnosticOracle; rw [hDiag]; rfl
  have hOracle : OriginalClaimOracle task (archetypeSubmission task 3) = false := by
    rw [← (claim_pinned_workflow_matches_original_oracle task _).1]; exact hPinned
  refine ⟨rfl, rfl, hOracle, hPinned, hDiag, ?_⟩
  exact Execution.bad_prefix_not_noUB (Bad := TaskBad)
    (Execution.Reach.tail (Execution.Reach.refl (false, 0))
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
    rfl

noncomputable def inflatedWeakSubmission (task : TaskId) : CandidateSubmission :=
  (task, (task + 1) + 1, task + 11, true, false, false, true, 0, true, 5, 5)

theorem theorem_count_metric_rewards_inflated_weak_submission (task : TaskId) :
    (inflatedWeakSubmission task).2.2.2.2.2.2.2.2.2.1 = 5 ∧
    (archetypeSubmission task 0).2.2.2.2.2.2.2.2.2.1 = 1 ∧
    (archetypeSubmission task 0).2.2.2.2.2.2.2.2.2.1 <
      (inflatedWeakSubmission task).2.2.2.2.2.2.2.2.2.1 ∧
    UnpinnedProofCountOracle task (inflatedWeakSubmission task) = true ∧
    OriginalClaimOracle task (inflatedWeakSubmission task) = false ∧
    OriginalClaimOracle task (archetypeSubmission task 0) = true := by
  refine ⟨rfl, rfl, ?_, rfl,
    (tempting_contract_weakening_passes_unpinned_checker task).2.2.1,
    (verified_repairs_succeed_on_all_six_tasks task).2.1⟩
  change 1 < 5; decide

noncomputable def misleadingSub : CandidateSubmission :=
  archetypeSubmission 0 2

theorem misleading_fix_masks_symptom_but_violates_prefix_noUB :
    misleadingSub.2.2.2.2.2.2.2.1 = 0 ∧
    misleadingSub.2.2.2.2.2.2.2.1 = (archetypeSubmission 0 0).2.2.2.2.2.2.2.1 ∧
    Execution.Reach (TaskStep misleadingSub) (false, 0) (false, 10) ∧
    ¬ Execution.NoUB (TaskStep misleadingSub) TaskBad (false, 0) ∧
    ClaimPinnedDiagnosticOracle 0 misleadingSub = false ∧
    diagnoseSubmission 0 misleadingSub = 3 := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
  · exact Execution.Reach.tail
      (Execution.Reach.tail (Execution.Reach.refl (false, 0))
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))
  · exact Execution.bad_prefix_not_noUB (Bad := TaskBad)
      (Execution.Reach.tail (Execution.Reach.refl (false, 0))
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
      rfl

theorem stale_binding_submission_rejected_despite_valid_old_proof (task : TaskId) :
    (archetypeSubmission task 4).2.2.2.2.2.2.2.2.1 = true ∧
    UnpinnedProofCountOracle task (archetypeSubmission task 4) = true ∧
    ClaimPinnedDiagnosticOracle task (archetypeSubmission task 4) = false ∧
    OriginalClaimOracle task (archetypeSubmission task 4) = false ∧
    diagnoseSubmission task (archetypeSubmission task 4) = 4 := by
  have hDiag := (diagnostic_feedback_identifies_exact_defect_class task 0).2.2.2.1
  have hPinned : ClaimPinnedDiagnosticOracle task (archetypeSubmission task 4) = false := by
    unfold ClaimPinnedDiagnosticOracle; rw [hDiag]; rfl
  have hOracle : OriginalClaimOracle task (archetypeSubmission task 4) = false := by
    rw [← (claim_pinned_workflow_matches_original_oracle task _).1]; exact hPinned
  exact ⟨rfl, rfl, hPinned, hOracle, hDiag⟩

noncomputable def countAcceptedKinds (oracle : TaskId → CandidateSubmission → Bool)
    (task : TaskId) : List Nat → Nat
  | [] => 0
  | k :: ks =>
    (if oracle task (archetypeSubmission task k) then 1 else 0) +
      countAcceptedKinds oracle task ks

noncomputable def unpinnedDefectivePassCount (task : TaskId) : Nat :=
  countAcceptedKinds UnpinnedProofCountOracle task [1, 2, 3, 4]

noncomputable def pinnedDefectivePassCount (task : TaskId) : Nat :=
  countAcceptedKinds ClaimPinnedDiagnosticOracle task [1, 2, 3, 4]

noncomputable def trueOriginalClaimDefectivePassCount (task : TaskId) : Nat :=
  countAcceptedKinds OriginalClaimOracle task [1, 2, 3, 4]

theorem unmatched_claim_strength_comparison_invalid (task : TaskId) :
    unpinnedDefectivePassCount task = 2 ∧
    pinnedDefectivePassCount task = 0 ∧
    trueOriginalClaimDefectivePassCount task = 0 ∧
    pinnedDefectivePassCount task < unpinnedDefectivePassCount task := by
  have hDef := diagnostic_feedback_identifies_exact_defect_class task 0
  have hPin1 : ClaimPinnedDiagnosticOracle task (archetypeSubmission task 1) = false := by
    unfold ClaimPinnedDiagnosticOracle; rw [hDef.1]; rfl
  have hPin2 : ClaimPinnedDiagnosticOracle task (archetypeSubmission task 2) = false := by
    unfold ClaimPinnedDiagnosticOracle; rw [hDef.2.1]; rfl
  have hPin3 : ClaimPinnedDiagnosticOracle task (archetypeSubmission task 3) = false := by
    unfold ClaimPinnedDiagnosticOracle; rw [hDef.2.2.1]; rfl
  have hPin4 : ClaimPinnedDiagnosticOracle task (archetypeSubmission task 4) = false := by
    unfold ClaimPinnedDiagnosticOracle; rw [hDef.2.2.2.1]; rfl
  have hOr1 : OriginalClaimOracle task (archetypeSubmission task 1) = false := by
    rw [← (claim_pinned_workflow_matches_original_oracle task _).1]; exact hPin1
  have hOr2 : OriginalClaimOracle task (archetypeSubmission task 2) = false := by
    rw [← (claim_pinned_workflow_matches_original_oracle task _).1]; exact hPin2
  have hOr3 : OriginalClaimOracle task (archetypeSubmission task 3) = false := by
    rw [← (claim_pinned_workflow_matches_original_oracle task _).1]; exact hPin3
  have hOr4 : OriginalClaimOracle task (archetypeSubmission task 4) = false := by
    rw [← (claim_pinned_workflow_matches_original_oracle task _).1]; exact hPin4
  have hUnpinned : unpinnedDefectivePassCount task = 2 := rfl
  have hPinned : pinnedDefectivePassCount task = 0 := by
    change (if ClaimPinnedDiagnosticOracle task (archetypeSubmission task 1) then 1 else 0) +
      ((if ClaimPinnedDiagnosticOracle task (archetypeSubmission task 2) then 1 else 0) +
       ((if ClaimPinnedDiagnosticOracle task (archetypeSubmission task 3) then 1 else 0) +
        ((if ClaimPinnedDiagnosticOracle task (archetypeSubmission task 4) then 1 else 0) + 0))) = 0
    rw [hPin1, hPin2, hPin3, hPin4]; rfl
  have hOracle : trueOriginalClaimDefectivePassCount task = 0 := by
    change (if OriginalClaimOracle task (archetypeSubmission task 1) then 1 else 0) +
      ((if OriginalClaimOracle task (archetypeSubmission task 2) then 1 else 0) +
       ((if OriginalClaimOracle task (archetypeSubmission task 3) then 1 else 0) +
        ((if OriginalClaimOracle task (archetypeSubmission task 4) then 1 else 0) + 0))) = 0
    rw [hOr1, hOr2, hOr3, hOr4]; rfl
  refine ⟨hUnpinned, hPinned, hOracle, ?_⟩
  rw [hPinned, hUnpinned]; change 0 < 2; decide

noncomputable def isOriginalClaimValidKind : Nat → Bool
  | 0 => true
  | _ + 1 => false

noncomputable def isUnpinnedAcceptedKind : Nat → Bool
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => true
  | _ + 4 => true

noncomputable def countPopulationOraclePasses (oracle : TaskId → CandidateSubmission → Bool) :
    List TaskId → Nat
  | [] => 0
  | t :: ts =>
    countAcceptedKinds oracle t [0, 1, 2, 3, 4] +
      countPopulationOraclePasses oracle ts

noncomputable def countTaskFalseAcceptances (task : TaskId) : List Nat → Nat
  | [] => 0
  | k :: ks =>
    let sub := archetypeSubmission task k
    (if UnpinnedProofCountOracle task sub && !OriginalClaimOracle task sub then 1 else 0) +
      countTaskFalseAcceptances task ks

noncomputable def countPopulationFalseAcceptances : List TaskId → Nat
  | [] => 0
  | t :: ts =>
    countTaskFalseAcceptances t [0, 1, 2, 3, 4] +
      countPopulationFalseAcceptances ts

theorem complete_population_evaluation_matrix :
    (∀ task : TaskId, ∀ kind : Nat,
      ClaimPinnedDiagnosticOracle task (archetypeSubmission task kind) =
        OriginalClaimOracle task (archetypeSubmission task kind) ∧
      OriginalClaimOracle task (archetypeSubmission task kind) =
        isOriginalClaimValidKind kind ∧
      UnpinnedProofCountOracle task (archetypeSubmission task kind) =
        isUnpinnedAcceptedKind kind) ∧
    countPopulationOraclePasses OriginalClaimOracle [0, 1, 2, 3, 4, 5] = 6 ∧
    countPopulationOraclePasses ClaimPinnedDiagnosticOracle [0, 1, 2, 3, 4, 5] = 6 ∧
    countPopulationOraclePasses UnpinnedProofCountOracle [0, 1, 2, 3, 4, 5] = 18 ∧
    countPopulationFalseAcceptances [0, 1, 2, 3, 4, 5] = 12 := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro task kind
  refine ⟨(claim_pinned_workflow_matches_original_oracle task _).1, ?_, ?_⟩
  · cases kind with
    | zero => exact (verified_repairs_succeed_on_all_six_tasks task).2.1
    | succ k1 =>
      cases k1 with
      | zero =>
        rw [← (claim_pinned_workflow_matches_original_oracle task _).1]
        unfold ClaimPinnedDiagnosticOracle
        rw [(diagnostic_feedback_identifies_exact_defect_class task 0).1]; rfl
      | succ k2 =>
        cases k2 with
        | zero =>
          rw [← (claim_pinned_workflow_matches_original_oracle task _).1]
          unfold ClaimPinnedDiagnosticOracle
          rw [(diagnostic_feedback_identifies_exact_defect_class task 0).2.1]; rfl
        | succ k3 =>
          cases k3 with
          | zero => exact (tempting_contract_weakening_passes_unpinned_checker task).2.2.1
          | succ k4 =>
            rw [← (claim_pinned_workflow_matches_original_oracle task _).1]
            unfold ClaimPinnedDiagnosticOracle
            rw [(diagnostic_feedback_identifies_exact_defect_class task k4).2.2.2.2]; rfl
  · cases kind with
    | zero => rfl
    | succ k1 =>
      cases k1 with
      | zero => rfl
      | succ k2 =>
        cases k2 with
        | zero => rfl
        | succ k3 =>
          cases k3 with
          | zero => rfl
          | succ k4 => rfl

#print axioms tempting_contract_weakening_passes_unpinned_checker
#print axioms theorem_count_metric_rewards_inflated_weak_submission
#print axioms misleading_fix_masks_symptom_but_violates_prefix_noUB
#print axioms stale_binding_submission_rejected_despite_valid_old_proof
#print axioms unmatched_claim_strength_comparison_invalid
#print axioms complete_population_evaluation_matrix

end AnnealResearch.AgentTaskControls
