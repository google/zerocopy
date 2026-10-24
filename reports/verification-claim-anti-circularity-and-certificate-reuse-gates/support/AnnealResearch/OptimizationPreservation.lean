import AnnealResearch.Execution
set_option Elab.async false

/-!
# Optimization Preservation Under an Independently Frozen User Claim (R-ADEV-04)

This module defines an owned multi-step operational model for a packet-scrub-and-checksum
computation, an independently frozen five-clause user claim (`FrozenUserClaim`), a four-step
baseline implementation (`baselineImpl`), and a three-step fused optimization
(`fusedValidOptImpl`). Both candidates are evaluated against the frozen user claim rather than
candidate-selected replacement contracts.
-/

namespace AnnealResearch.OptimizationPreservation

-- PacketInput: (hdr, payload, secret, scratchCell, callerCell, callerSaved, validBounds)
abbrev PacketInput : Type :=
  Nat × Nat × Nat × Nat × Nat × Nat × Bool

def AdmittedInput (inp : PacketInput) : Prop :=
  inp.2.2.2.1 ≠ inp.2.2.2.2.1 ∧ inp.2.2.2.2.2.2 = true

noncomputable def withSecret (inp : PacketInput) (sec : Nat) : PacketInput :=
  (inp.1, inp.2.1, sec, inp.2.2.2.1, inp.2.2.2.2.1, inp.2.2.2.2.2.1, inp.2.2.2.2.2.2)

noncomputable def sampleAdmittedInput : PacketInput :=
  (1, 1, 1, 0, 1, 0, true)

theorem sampleAdmittedInput_admitted : AdmittedInput sampleAdmittedInput := by
  refine ⟨?_, rfl⟩
  intro h
  change 0 = 1 at h
  nomatch h

theorem admitted_input_nonvacuous : ∃ inp, AdmittedInput inp :=
  ⟨sampleAdmittedInput, sampleAdmittedInput_admitted⟩

-- PacketState: (phase, outputTag, callerCellValue, tempCleared, workSteps, peakScratchSlots, obsAddressTrace, ubFault)
-- Phases: 0 = init, 1 = scrubScratch, 2 = computeTag, 3 = clearTemp, 4 = done
abbrev PacketState : Type :=
  Nat × Option Nat × Nat × Bool × Nat × Nat × List Nat × Bool

noncomputable def initState (inp : PacketInput) : PacketState :=
  (0, none, inp.2.2.2.2.2.1, true, 0, 0, [], false)

def BadState (s : PacketState) : Prop :=
  s.2.2.2.2.2.2.2 = true

-- CandidateImpl: (stage1, stage2, stage3, terminalStage4)
abbrev CandidateImpl : Type :=
  (PacketInput → PacketState) ×
  (PacketInput → PacketState) ×
  (PacketInput → PacketState) ×
  (PacketInput → PacketState)

def CandidateStep (cand : CandidateImpl) (inp : PacketInput)
    (u v : PacketState) : Prop :=
  (u = initState inp ∧ v = cand.1 inp) ∨
  (u = cand.1 inp ∧ v = cand.2.1 inp) ∨
  (u = cand.2.1 inp ∧ v = cand.2.2.1 inp) ∨
  (u = cand.2.2.1 inp ∧ v = cand.2.2.2 inp)

theorem reachable_of_stages (cand : CandidateImpl) (inp : PacketInput)
    (P : PacketState → Prop)
    (h0 : P (initState inp))
    (h1 : P (cand.1 inp))
    (h2 : P (cand.2.1 inp))
    (h3 : P (cand.2.2.1 inp))
    (h4 : P (cand.2.2.2 inp))
    {s : PacketState}
    (hreach : Execution.Reach (CandidateStep cand inp) (initState inp) s) :
    P s := by
  refine Execution.invariant_reachable h0 ?_ hreach
  intro u v _ edge
  cases edge with
  | inl h =>
    cases h with
    | intro _ hv => subst hv; exact h1
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro _ hv => subst hv; exact h2
    | inr h =>
      cases h with
      | inl h =>
        cases h with
        | intro _ hv => subst hv; exact h3
      | inr h =>
        cases h with
        | intro _ hv => subst hv; exact h4

theorem noUB_of_stages (cand : CandidateImpl) (inp : PacketInput)
    (h1 : (cand.1 inp).2.2.2.2.2.2.2 = false)
    (h2 : (cand.2.1 inp).2.2.2.2.2.2.2 = false)
    (h3 : (cand.2.2.1 inp).2.2.2.2.2.2.2 = false)
    (h4 : (cand.2.2.2 inp).2.2.2.2.2.2.2 = false) :
    Execution.NoUB (CandidateStep cand inp) BadState (initState inp) := by
  intro s hreach hbad
  have hfalse : s.2.2.2.2.2.2.2 = false :=
    reachable_of_stages cand inp (fun st => st.2.2.2.2.2.2.2 = false) rfl h1 h2 h3 h4 hreach
  exact Bool.noConfusion (hfalse.symm.trans hbad)

noncomputable def terminalWork (cand : CandidateImpl) (inp : PacketInput) : Nat :=
  (cand.2.2.2 inp).2.2.2.2.1

noncomputable def peakSlots (cand : CandidateImpl) (inp : PacketInput) : Nat :=
  (cand.2.2.2 inp).2.2.2.2.2.1

def functional_exact (cand : CandidateImpl) : Prop :=
  ∀ inp, AdmittedInput inp →
    Execution.Reach (CandidateStep cand inp) (initState inp) (cand.2.2.2 inp) ∧
    (cand.2.2.2 inp).1 = 4 ∧
    (cand.2.2.2 inp).2.1 = some (inp.1 + inp.2.1) ∧
    ∀ s, Execution.Reach (CandidateStep cand inp) (initState inp) s →
      s.1 = 4 → s.2.1 = some (inp.1 + inp.2.1)

def all_prefix_noUB (cand : CandidateImpl) : Prop :=
  ∀ inp, AdmittedInput inp →
    Execution.NoUB (CandidateStep cand inp) BadState (initState inp)

def footprint_preserved (cand : CandidateImpl) : Prop :=
  ∀ inp, AdmittedInput inp →
    ∀ s, Execution.Reach (CandidateStep cand inp) (initState inp) s →
      s.2.2.1 = inp.2.2.2.2.2.1 ∧
      (s.1 = 4 → s.2.2.2.1 = true)

def resource_within_frozen_budget (cand : CandidateImpl) : Prop :=
  ∀ inp, AdmittedInput inp →
    ∀ s, Execution.Reach (CandidateStep cand inp) (initState inp) s →
      s.2.2.2.2.1 ≤ 4 ∧ s.2.2.2.2.2.1 ≤ 2

def secret_independent_observations (cand : CandidateImpl) : Prop :=
  ∀ inp, AdmittedInput inp →
    ∀ s1 s2,
      (cand.1 (withSecret inp s1)).2.2.2.2.2.2.1 =
        (cand.1 (withSecret inp s2)).2.2.2.2.2.2.1 ∧
      (cand.2.1 (withSecret inp s1)).2.2.2.2.2.2.1 =
        (cand.2.1 (withSecret inp s2)).2.2.2.2.2.2.1 ∧
      (cand.2.2.1 (withSecret inp s1)).2.2.2.2.2.2.1 =
        (cand.2.2.1 (withSecret inp s2)).2.2.2.2.2.2.1 ∧
      (cand.2.2.2 (withSecret inp s1)).2.2.2.2.2.2.1 =
        (cand.2.2.2 (withSecret inp s2)).2.2.2.2.2.2.1

/-- Independently frozen user claim that every optimization candidate must preserve. -/
def FrozenUserClaim (cand : CandidateImpl) : Prop :=
  functional_exact cand ∧
  all_prefix_noUB cand ∧
  footprint_preserved cand ∧
  resource_within_frozen_budget cand ∧
  secret_independent_observations cand

/-! ## Baseline 4-Step Implementation (`baselineImpl`) and Valid 3-Step Optimization (`fusedValidOptImpl`) -/

noncomputable def baselineImpl : CandidateImpl :=
  ((fun inp => (1, none, inp.2.2.2.2.2.1, false, 1, 2, [inp.1], false)),
   (fun inp => (2, none, inp.2.2.2.2.2.1, false, 2, 2, [inp.1, inp.1 + 1], false)),
   (fun inp => (3, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 3, 2, [inp.1, inp.1 + 1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 4, 2, [inp.1, inp.1 + 1], false)))

theorem baseline_satisfies_frozen_claim : FrozenUserClaim baselineImpl := by
  refine ⟨?hfunc, ?hnoub, ?hfp, ?hres, ?hobs⟩
  · intro inp _
    have hr1 : Execution.Reach (CandidateStep baselineImpl inp) (initState inp) (baselineImpl.1 inp) :=
      Execution.Reach.tail (Execution.Reach.refl (initState inp)) (Or.inl ⟨rfl, rfl⟩)
    have hr2 : Execution.Reach (CandidateStep baselineImpl inp) (initState inp) (baselineImpl.2.1 inp) :=
      Execution.Reach.tail hr1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hr3 : Execution.Reach (CandidateStep baselineImpl inp) (initState inp) (baselineImpl.2.2.1 inp) :=
      Execution.Reach.tail hr2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    have hr4 : Execution.Reach (CandidateStep baselineImpl inp) (initState inp) (baselineImpl.2.2.2 inp) :=
      Execution.Reach.tail hr3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    refine ⟨hr4, rfl, rfl, ?_⟩
    intro s hreach
    exact reachable_of_stages baselineImpl inp
      (fun st => st.1 = 4 → st.2.1 = some (inp.1 + inp.2.1))
      (fun h => by change 0 = 4 at h; nomatch h)
      (fun h => by change 1 = 4 at h; nomatch h)
      (fun h => by change 2 = 4 at h; nomatch h)
      (fun h => by change 3 = 4 at h; nomatch h)
      (fun _ => rfl)
      hreach
  · intro inp _
    exact noUB_of_stages baselineImpl inp rfl rfl rfl rfl
  · intro inp _ s hreach
    exact reachable_of_stages baselineImpl inp
      (fun st => st.2.2.1 = inp.2.2.2.2.2.1 ∧ (st.1 = 4 → st.2.2.2.1 = true))
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun h => by change 1 = 4 at h; nomatch h⟩
      ⟨rfl, fun h => by change 2 = 4 at h; nomatch h⟩
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun _ => rfl⟩
      hreach
  · intro inp _ s hreach
    exact reachable_of_stages baselineImpl inp
      (fun st => st.2.2.2.2.1 ≤ 4 ∧ st.2.2.2.2.2.1 ≤ 2)
      ⟨Nat.zero_le 4, Nat.zero_le 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_step (Nat.le_refl 1))), Nat.le_refl 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.le_refl 2⟩
      ⟨Nat.le_step (Nat.le_refl 3), Nat.le_refl 2⟩
      ⟨Nat.le_refl 4, Nat.le_refl 2⟩
      hreach
  · intro inp _ s1 s2
    exact ⟨rfl, rfl, rfl, rfl⟩

noncomputable def fusedValidOptImpl : CandidateImpl :=
  ((fun inp => (1, none, inp.2.2.2.2.2.1, false, 1, 1, [inp.1], false)),
   (fun inp => (3, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 2, 1, [inp.1, inp.1 + 1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 3, 1, [inp.1, inp.1 + 1], false)),
   (fun inp => (4, some (inp.1 + inp.2.1), inp.2.2.2.2.2.1, true, 3, 1, [inp.1, inp.1 + 1], false)))

theorem fusedValidOpt_satisfies_frozen_claim : FrozenUserClaim fusedValidOptImpl := by
  refine ⟨?hfunc, ?hnoub, ?hfp, ?hres, ?hobs⟩
  · intro inp _
    have hr1 : Execution.Reach (CandidateStep fusedValidOptImpl inp) (initState inp) (fusedValidOptImpl.1 inp) :=
      Execution.Reach.tail (Execution.Reach.refl (initState inp)) (Or.inl ⟨rfl, rfl⟩)
    have hr2 : Execution.Reach (CandidateStep fusedValidOptImpl inp) (initState inp) (fusedValidOptImpl.2.1 inp) :=
      Execution.Reach.tail hr1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hr3 : Execution.Reach (CandidateStep fusedValidOptImpl inp) (initState inp) (fusedValidOptImpl.2.2.1 inp) :=
      Execution.Reach.tail hr2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    have hr4 : Execution.Reach (CandidateStep fusedValidOptImpl inp) (initState inp) (fusedValidOptImpl.2.2.2 inp) :=
      Execution.Reach.tail hr3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    refine ⟨hr4, rfl, rfl, ?_⟩
    intro s hreach
    exact reachable_of_stages fusedValidOptImpl inp
      (fun st => st.1 = 4 → st.2.1 = some (inp.1 + inp.2.1))
      (fun h => by change 0 = 4 at h; nomatch h)
      (fun h => by change 1 = 4 at h; nomatch h)
      (fun h => by change 3 = 4 at h; nomatch h)
      (fun _ => rfl)
      (fun _ => rfl)
      hreach
  · intro inp _
    exact noUB_of_stages fusedValidOptImpl inp rfl rfl rfl rfl
  · intro inp _ s hreach
    exact reachable_of_stages fusedValidOptImpl inp
      (fun st => st.2.2.1 = inp.2.2.2.2.2.1 ∧ (st.1 = 4 → st.2.2.2.1 = true))
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun h => by change 1 = 4 at h; nomatch h⟩
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun _ => rfl⟩
      ⟨rfl, fun _ => rfl⟩
      hreach
  · intro inp _ s hreach
    exact reachable_of_stages fusedValidOptImpl inp
      (fun st => st.2.2.2.2.1 ≤ 4 ∧ st.2.2.2.2.2.1 ≤ 2)
      ⟨Nat.zero_le 4, Nat.zero_le 2⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_step (Nat.le_refl 1))), Nat.le_step (Nat.le_refl 1)⟩
      ⟨Nat.le_step (Nat.le_step (Nat.le_refl 2)), Nat.le_step (Nat.le_refl 1)⟩
      ⟨Nat.le_step (Nat.le_refl 3), Nat.le_step (Nat.le_refl 1)⟩
      ⟨Nat.le_step (Nat.le_refl 3), Nat.le_step (Nat.le_refl 1)⟩
      hreach
  · intro inp _ s1 s2
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem fusedValidOpt_strictly_reduces_logical_cost :
    ∀ inp, AdmittedInput inp →
      terminalWork fusedValidOptImpl inp = 3 ∧
      terminalWork baselineImpl inp = 4 ∧
      peakSlots fusedValidOptImpl inp = 1 ∧
      peakSlots baselineImpl inp = 2 := by
  intro _ _
  exact ⟨rfl, rfl, rfl, rfl⟩

def StrictlyReducesWork (cand : CandidateImpl) : Prop :=
  ∀ inp, AdmittedInput inp → terminalWork cand inp < 4

theorem logical_improvement_distinct_from_claim_satisfaction :
    (FrozenUserClaim baselineImpl ∧ ¬ StrictlyReducesWork baselineImpl) ∧
    (FrozenUserClaim fusedValidOptImpl ∧ StrictlyReducesWork fusedValidOptImpl) := by
  refine ⟨⟨baseline_satisfies_frozen_claim, ?_⟩, ⟨fusedValidOpt_satisfies_frozen_claim, ?_⟩⟩
  · intro hlt
    have h4 : 4 < 4 := hlt sampleAdmittedInput sampleAdmittedInput_admitted
    exact Nat.lt_irrefl 4 h4
  · intro _ _
    exact Nat.le_refl 4

#print axioms sampleAdmittedInput_admitted
#print axioms admitted_input_nonvacuous
#print axioms reachable_of_stages
#print axioms noUB_of_stages
#print axioms baseline_satisfies_frozen_claim
#print axioms fusedValidOpt_satisfies_frozen_claim
#print axioms fusedValidOpt_strictly_reduces_logical_cost
#print axioms logical_improvement_distinct_from_claim_satisfaction

end AnnealResearch.OptimizationPreservation
