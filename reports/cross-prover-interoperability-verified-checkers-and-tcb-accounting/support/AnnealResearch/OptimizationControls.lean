import AnnealResearch.OptimizationPreservation
set_option Elab.async false

/-!
# Negative Optimization Controls and Contract-Weakening Challenges (R-ADEV-04)

This module evaluates three seemingly cheaper optimization candidates and an attempted
contract-weakening proof repair against the independently frozen `FrozenUserClaim` defined in
`AnnealResearch.OptimizationPreservation`.
-/

namespace AnnealResearch.OptimizationControls

open AnnealResearch.OptimizationPreservation

/-! ## Control 1: Caller-Frame Footprint Clobber (`footprintClobberOptImpl`) -/

noncomputable def footprintClobberOptImpl : CandidateImpl :=
  ((fun inp => (2, none, inp.1 + inp.2.1, true, 1, 0, [inp.1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.1 + inp.2.1, true, 2, 0, [inp.1, inp.1 + 1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.1 + inp.2.1, true, 2, 0, [inp.1, inp.1 + 1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.1 + inp.2.1, true, 2, 0, [inp.1, inp.1 + 1], false)))

theorem footprintClobber_matches_output_and_noUB_but_violates_footprint :
    functional_exact footprintClobberOptImpl ∧
    all_prefix_noUB footprintClobberOptImpl ∧
    resource_within_frozen_budget footprintClobberOptImpl ∧
    secret_independent_observations footprintClobberOptImpl ∧
    ¬ footprint_preserved footprintClobberOptImpl := by
  refine ⟨?hfunc, ?hnoub, ?hres, ?hobs, ?hnfp⟩
  · intro inp _
    have hr1 : Execution.Reach (CandidateStep footprintClobberOptImpl inp)
        (initState inp) (footprintClobberOptImpl.1 inp) :=
      Execution.Reach.tail (Execution.Reach.refl (initState inp)) (Or.inl ⟨rfl, rfl⟩)
    have hr2 : Execution.Reach (CandidateStep footprintClobberOptImpl inp)
        (initState inp) (footprintClobberOptImpl.2.1 inp) :=
      Execution.Reach.tail hr1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hr3 : Execution.Reach (CandidateStep footprintClobberOptImpl inp)
        (initState inp) (footprintClobberOptImpl.2.2.1 inp) :=
      Execution.Reach.tail hr2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    have hr4 : Execution.Reach (CandidateStep footprintClobberOptImpl inp)
        (initState inp) (footprintClobberOptImpl.2.2.2 inp) :=
      Execution.Reach.tail hr3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    refine ⟨hr4, rfl, rfl, ?_⟩
    intro s hreach
    exact reachable_of_stages footprintClobberOptImpl inp
      (fun st => st.1 = 4 → st.2.1 = some (inp.1 + inp.2.1))
      (fun h => by change 0 = 4 at h; nomatch h)
      (fun h => by change 2 = 4 at h; nomatch h)
      (fun _ => rfl)
      (fun _ => rfl)
      (fun _ => rfl)
      hreach
  · intro inp _
    exact noUB_of_stages footprintClobberOptImpl inp rfl rfl rfl rfl
  · intro inp _ s hreach
    exact reachable_of_stages footprintClobberOptImpl inp
      (fun st => st.2.2.2.2.1 ≤ 4 ∧ st.2.2.2.2.2.1 ≤ 2)
      ⟨Nat.zero_le 4, Nat.zero_le 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_step (Nat.le_refl 1))), Nat.zero_le 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.zero_le 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.zero_le 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.zero_le 2⟩
      hreach
  · intro inp _ s1 s2
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hfp
    have hr1 : Execution.Reach (CandidateStep footprintClobberOptImpl sampleAdmittedInput)
        (initState sampleAdmittedInput) (footprintClobberOptImpl.1 sampleAdmittedInput) :=
      Execution.Reach.tail (Execution.Reach.refl (initState sampleAdmittedInput)) (Or.inl ⟨rfl, rfl⟩)
    have h1 :=
      (hfp sampleAdmittedInput sampleAdmittedInput_admitted
        (footprintClobberOptImpl.1 sampleAdmittedInput) hr1).1
    change 2 = 0 at h1
    nomatch h1

theorem footprintClobber_rejected_by_frozen_claim :
    ¬ FrozenUserClaim footprintClobberOptImpl := by
  intro hclaim
  exact footprintClobber_matches_output_and_noUB_but_violates_footprint.2.2.2.2 hclaim.2.2.1

/-! ## Control 2: Secret-Dependent Fast-Path Observation (`secretBranchOptImpl`) -/

noncomputable def secretBranchOptImpl : CandidateImpl :=
  ((fun inp => (2, none, inp.2.2.2.2.2.1, false, 1, 1, [inp.1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 2, 1,
     (if inp.2.2.1 == 0 then [inp.1] else [inp.1, inp.1 + 1]), false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 2, 1,
     (if inp.2.2.1 == 0 then [inp.1] else [inp.1, inp.1 + 1]), false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 2, 1,
     (if inp.2.2.1 == 0 then [inp.1] else [inp.1, inp.1 + 1]), false)))

theorem secretBranch_violates_observation_policy :
    functional_exact secretBranchOptImpl ∧
    all_prefix_noUB secretBranchOptImpl ∧
    footprint_preserved secretBranchOptImpl ∧
    resource_within_frozen_budget secretBranchOptImpl ∧
    ¬ secret_independent_observations secretBranchOptImpl := by
  refine ⟨?hfunc, ?hnoub, ?hfp, ?hres, ?hnobs⟩
  · intro inp _
    have hr1 : Execution.Reach (CandidateStep secretBranchOptImpl inp)
        (initState inp) (secretBranchOptImpl.1 inp) :=
      Execution.Reach.tail (Execution.Reach.refl (initState inp)) (Or.inl ⟨rfl, rfl⟩)
    have hr2 : Execution.Reach (CandidateStep secretBranchOptImpl inp)
        (initState inp) (secretBranchOptImpl.2.1 inp) :=
      Execution.Reach.tail hr1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hr3 : Execution.Reach (CandidateStep secretBranchOptImpl inp)
        (initState inp) (secretBranchOptImpl.2.2.1 inp) :=
      Execution.Reach.tail hr2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    have hr4 : Execution.Reach (CandidateStep secretBranchOptImpl inp)
        (initState inp) (secretBranchOptImpl.2.2.2 inp) :=
      Execution.Reach.tail hr3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    refine ⟨hr4, rfl, rfl, ?_⟩
    intro s hreach
    exact reachable_of_stages secretBranchOptImpl inp
      (fun st => st.1 = 4 → st.2.1 = some (inp.1 + inp.2.1))
      (fun h => by change 0 = 4 at h; nomatch h)
      (fun h => by change 2 = 4 at h; nomatch h)
      (fun _ => rfl)
      (fun _ => rfl)
      (fun _ => rfl)
      hreach
  · intro inp _
    exact noUB_of_stages secretBranchOptImpl inp rfl rfl rfl rfl
  · intro inp _ s hreach
    exact reachable_of_stages secretBranchOptImpl inp
      (fun st => st.2.2.1 = inp.2.2.2.2.2.1 ∧ (st.1 = 4 → st.2.2.2.1 = true))
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun h => by change 2 = 4 at h; nomatch h⟩
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun _ => rfl⟩
      hreach
  · intro inp _ s hreach
    exact reachable_of_stages secretBranchOptImpl inp
      (fun st => st.2.2.2.2.1 ≤ 4 ∧ st.2.2.2.2.2.1 ≤ 2)
      ⟨Nat.zero_le 4, Nat.zero_le 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_step (Nat.le_refl 1))), Nat.le_step (Nat.le_refl 1)⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.le_step (Nat.le_refl 1)⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.le_step (Nat.le_refl 1)⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.le_step (Nat.le_refl 1)⟩
      hreach
  · intro hobs
    have h2 := (hobs sampleAdmittedInput sampleAdmittedInput_admitted 0 1).2.1
    change [1] = [1, 2] at h2
    nomatch h2

theorem secretBranch_rejected_by_frozen_claim :
    ¬ FrozenUserClaim secretBranchOptImpl := by
  intro hclaim
  exact secretBranch_violates_observation_policy.2.2.2.2 hclaim.2.2.2.2

/-! ## Control 3: Attempted Proof Repair Weakening the Contract (`WeakenedReplacementContract`) -/

def WeakenedReplacementContract (cand : CandidateImpl) : Prop :=
  functional_exact cand ∧
  all_prefix_noUB cand ∧
  resource_within_frozen_budget cand

theorem weakened_repair_admits_rejected_candidates :
    WeakenedReplacementContract footprintClobberOptImpl ∧
    WeakenedReplacementContract secretBranchOptImpl :=
  ⟨⟨footprintClobber_matches_output_and_noUB_but_violates_footprint.1,
    footprintClobber_matches_output_and_noUB_but_violates_footprint.2.1,
    footprintClobber_matches_output_and_noUB_but_violates_footprint.2.2.1⟩,
   ⟨secretBranch_violates_observation_policy.1,
    secretBranch_violates_observation_policy.2.1,
    secretBranch_violates_observation_policy.2.2.2.1⟩⟩

theorem frozen_oracle_rejects_self_selected_contract_repair :
    (WeakenedReplacementContract footprintClobberOptImpl ∧
      ¬ FrozenUserClaim footprintClobberOptImpl) ∧
    (WeakenedReplacementContract secretBranchOptImpl ∧
      ¬ FrozenUserClaim secretBranchOptImpl) :=
  ⟨⟨weakened_repair_admits_rejected_candidates.1, footprintClobber_rejected_by_frozen_claim⟩,
   ⟨weakened_repair_admits_rejected_candidates.2, secretBranch_rejected_by_frozen_claim⟩⟩

/-! ## Control 4: Late-Prefix Cleanup UB (`latePrefixUbOptImpl`) -/

noncomputable def latePrefixUbOptImpl : CandidateImpl :=
  ((fun inp => (2, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, false, 1, 1, [inp.1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 2, 1, [inp.1, inp.1 + 1], true)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 2, 1, [inp.1, inp.1 + 1], true)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 2, 1, [inp.1, inp.1 + 1], true)))

theorem late_prefix_ub_opt_control :
    functional_exact latePrefixUbOptImpl ∧
    ¬ all_prefix_noUB latePrefixUbOptImpl ∧
    ¬ FrozenUserClaim latePrefixUbOptImpl := by
  have hnot_noub : ¬ all_prefix_noUB latePrefixUbOptImpl := by
    intro hnoub
    have hr1 : Execution.Reach (CandidateStep latePrefixUbOptImpl sampleAdmittedInput)
        (initState sampleAdmittedInput) (latePrefixUbOptImpl.1 sampleAdmittedInput) :=
      Execution.Reach.tail (Execution.Reach.refl (initState sampleAdmittedInput)) (Or.inl ⟨rfl, rfl⟩)
    have hr2 : Execution.Reach (CandidateStep latePrefixUbOptImpl sampleAdmittedInput)
        (initState sampleAdmittedInput) (latePrefixUbOptImpl.2.1 sampleAdmittedInput) :=
      Execution.Reach.tail hr1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hbad : BadState (latePrefixUbOptImpl.2.1 sampleAdmittedInput) := rfl
    exact Execution.bad_prefix_not_noUB (Bad := BadState) hr2 hbad
      (hnoub sampleAdmittedInput sampleAdmittedInput_admitted)
  refine ⟨?_, hnot_noub, fun hclaim => hnot_noub hclaim.2.1⟩
  intro inp _
  have hr1 : Execution.Reach (CandidateStep latePrefixUbOptImpl inp)
      (initState inp) (latePrefixUbOptImpl.1 inp) :=
    Execution.Reach.tail (Execution.Reach.refl (initState inp)) (Or.inl ⟨rfl, rfl⟩)
  have hr2 : Execution.Reach (CandidateStep latePrefixUbOptImpl inp)
      (initState inp) (latePrefixUbOptImpl.2.1 inp) :=
    Execution.Reach.tail hr1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hr3 : Execution.Reach (CandidateStep latePrefixUbOptImpl inp)
      (initState inp) (latePrefixUbOptImpl.2.2.1 inp) :=
    Execution.Reach.tail hr2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have hr4 : Execution.Reach (CandidateStep latePrefixUbOptImpl inp)
      (initState inp) (latePrefixUbOptImpl.2.2.2 inp) :=
    Execution.Reach.tail hr3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  refine ⟨hr4, rfl, rfl, ?_⟩
  intro s hreach
  exact reachable_of_stages latePrefixUbOptImpl inp
    (fun st => st.1 = 4 → st.2.1 = some (inp.1 + inp.2.1))
    (fun h => by change 0 = 4 at h; nomatch h)
    (fun h => by change 2 = 4 at h; nomatch h)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)
    hreach

theorem latePrefixUb_rejected_by_frozen_claim :
    ¬ FrozenUserClaim latePrefixUbOptImpl :=
  late_prefix_ub_opt_control.2.2

/-! ## Complete Candidate Classification -/

theorem complete_candidate_classification :
    (FrozenUserClaim baselineImpl ∧
      terminalWork baselineImpl sampleAdmittedInput = 4 ∧
      peakSlots baselineImpl sampleAdmittedInput = 2) ∧
    (FrozenUserClaim fusedValidOptImpl ∧
      terminalWork fusedValidOptImpl sampleAdmittedInput = 3 ∧
      peakSlots fusedValidOptImpl sampleAdmittedInput = 1) ∧
    (¬ FrozenUserClaim footprintClobberOptImpl ∧
      terminalWork footprintClobberOptImpl sampleAdmittedInput = 2 ∧
      peakSlots footprintClobberOptImpl sampleAdmittedInput = 0) ∧
    (¬ FrozenUserClaim secretBranchOptImpl ∧
      terminalWork secretBranchOptImpl sampleAdmittedInput = 2 ∧
      peakSlots secretBranchOptImpl sampleAdmittedInput = 1) ∧
    (¬ FrozenUserClaim latePrefixUbOptImpl ∧
      terminalWork latePrefixUbOptImpl sampleAdmittedInput = 2 ∧
      peakSlots latePrefixUbOptImpl sampleAdmittedInput = 1) :=
  ⟨⟨baseline_satisfies_frozen_claim, rfl, rfl⟩,
   ⟨fusedValidOpt_satisfies_frozen_claim, rfl, rfl⟩,
   ⟨footprintClobber_rejected_by_frozen_claim, rfl, rfl⟩,
   ⟨secretBranch_rejected_by_frozen_claim, rfl, rfl⟩,
   ⟨latePrefixUb_rejected_by_frozen_claim, rfl, rfl⟩⟩

#print axioms footprintClobber_matches_output_and_noUB_but_violates_footprint
#print axioms footprintClobber_rejected_by_frozen_claim
#print axioms secretBranch_violates_observation_policy
#print axioms secretBranch_rejected_by_frozen_claim
#print axioms weakened_repair_admits_rejected_candidates
#print axioms frozen_oracle_rejects_self_selected_contract_repair
#print axioms late_prefix_ub_opt_control
#print axioms latePrefixUb_rejected_by_frozen_claim
#print axioms complete_candidate_classification

end AnnealResearch.OptimizationControls
