import AnnealResearch.FactReuseValidation

set_option Elab.async false

/-!
R-ADEV-05 Module 2: Negative controls, non-circularity, and invalidation boundaries.
-/

namespace AnnealResearch.FactReuseControls

open AnnealResearch.FactReuseValidation

abbrev VerificationSubject : Type :=
  LayoutSpec × Nat × Bool × Bool × Nat

abbrev ReusableEvidenceBundle : Type :=
  LayoutSpec × Nat × Bool × Bool

def LayoutCertApplicable (bundle : ReusableEvidenceBundle) (subj : VerificationSubject) : Prop :=
  bundle.1 = subj.1

def CodecCertApplicable (bundle : ReusableEvidenceBundle) (subj : VerificationSubject) : Prop :=
  bundle.2.1 = subj.2.1 ∧
  bundle.2.2.1 = subj.2.2.1 ∧
  bundle.2.2.2 = subj.2.2.2.1

def BundleApplicable (bundle : ReusableEvidenceBundle) (subj : VerificationSubject) : Prop :=
  LayoutCertApplicable bundle subj ∧ CodecCertApplicable bundle subj

def CircularTypingToSafety : Prop :=
  ∀ (layout : LayoutSpec) (impl : Nat) (cfg : Bool) (byte : Nat),
    StructuralLayoutCert layout →
    EndpointSafeAndTyped layout impl cfg byte

theorem admitted_invalid_bool_byte2_exposes_ub :
    StructuralLayoutCert boolSlotLayout ∧
    ¬ ValidBoolByte 2 ∧
    ¬ Execution.NoUB (DecodeStep 2 true) DecodeBad (initState boolSlotLayout 2) ∧
    ¬ EndpointSafeAndTyped boolSlotLayout 2 true 2 := by
  have hNotValid : ¬ ValidBoolByte 2 := by
    rintro (h0 | h1)
    · exact Nat.noConfusion h0
    · exact Nat.noConfusion (Nat.succ.inj h1)
  have hInvalid : 2 ≠ 0 ∧ 2 ≠ 1 :=
    ⟨fun h => Nat.noConfusion h, fun h => Nat.noConfusion (Nat.succ.inj h)⟩
  have hReachUB : Execution.Reach (DecodeStep 2 true)
      (initState boolSlotLayout 2) (true, 7, boolSlotLayout, 2, false) := by
    apply Execution.Reach.tail
    · apply Execution.Reach.tail
      · exact Execution.Reach.refl (initState boolSlotLayout 2)
      · exact Or.inl ⟨boolSlotLayout, 2, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨boolSlotLayout, 2, rfl, ⟨hInvalid, Or.inl rfl⟩, rfl⟩))))
  have hNotNoUB : ¬ Execution.NoUB (DecodeStep 2 true) DecodeBad (initState boolSlotLayout 2) :=
    Execution.bad_prefix_not_noUB (Bad := DecodeBad) hReachUB rfl
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, hNotValid, hNotNoUB, fun ⟨hNoUB, _, _⟩ => hNotNoUB hNoUB⟩

theorem discarded_invalid_bool_still_ub :
    Execution.Reach (DecodeStepFull 2 true false)
      (initState boolSlotLayout 2) (true, 7, boolSlotLayout, 2, false) ∧
    ¬ Execution.NoUB (DecodeStepFull 2 true false)
      DecodeBad (initState boolSlotLayout 2) ∧
    Execution.Reach (DecodeStepFull 2 true false)
      (initState boolSlotLayout 1) (false, 4, boolSlotLayout, 1, false) ∧
    Execution.NoUB (DecodeStepFull 2 true false)
      DecodeBad (initState boolSlotLayout 1) := by
  have hInvalid2 : 2 ≠ 0 ∧ 2 ≠ 1 :=
    ⟨fun h => Nat.noConfusion h, fun h => Nat.noConfusion (Nat.succ.inj h)⟩
  have hReachUB2 : Execution.Reach (DecodeStepFull 2 true false)
      (initState boolSlotLayout 2) (true, 7, boolSlotLayout, 2, false) := by
    apply Execution.Reach.tail
    · apply Execution.Reach.tail
      · exact Execution.Reach.refl (initState boolSlotLayout 2)
      · exact Or.inl ⟨boolSlotLayout, 2, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨boolSlotLayout, 2, rfl, ⟨hInvalid2, Or.inl rfl⟩, rfl⟩))))
  have hReachOk1 : Execution.Reach (DecodeStepFull 2 true false)
      (initState boolSlotLayout 1) (false, 4, boolSlotLayout, 1, false) := by
    apply Execution.Reach.tail
    · apply Execution.Reach.tail
      · apply Execution.Reach.tail
        · exact Execution.Reach.refl (initState boolSlotLayout 1)
        · exact Or.inl ⟨boolSlotLayout, 1, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨boolSlotLayout, 1, true, rfl, Or.inr ⟨rfl, rfl⟩, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨boolSlotLayout, 1, true, rfl, rfl, rfl⟩)))))
  have hNoUB1 : Execution.NoUB (DecodeStepFull 2 true false)
      DecodeBad (initState boolSlotLayout 1) := by
    apply Execution.invariant_noUB
      (Invariant := fun s : DecodeState =>
        s.1 = false ∧ s.2.2.1 = boolSlotLayout ∧ s.2.2.2.1 = 1)
    · exact ⟨rfl, rfl, rfl⟩
    · intro s t hs edge
      rcases edge with
        ⟨_, _, hs_eq, _, ht_eq⟩ |
        ⟨l, _, hs_eq, hNotL, _⟩ |
        ⟨_, _, _, hs_eq, _, ht_eq⟩ |
        ⟨_, _, hs_eq, _, ht_eq⟩ |
        ⟨_, b, hs_eq, ⟨⟨_, hNe1⟩, _⟩, _⟩ |
        ⟨_, _, _, hs_eq, _, ht_eq⟩ |
        ⟨_, _, _, hs_eq, _, ht_eq⟩
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq
        have hL : l = boolSlotLayout := hs.2.1
        subst hL
        exact False.elim (hNotL ⟨rfl, rfl, rfl, rfl⟩)
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq
        have hB : b = 1 := hs.2.2
        subst hB
        exact False.elim (hNe1 rfl)
      · subst hs_eq; subst ht_eq; exact hs
      · subst hs_eq; subst ht_eq; exact hs
    · intro _ hs hBad
      exact Bool.noConfusion (hs.1.symm.trans hBad)
  exact ⟨hReachUB2, Execution.bad_prefix_not_noUB (Bad := DecodeBad) hReachUB2 rfl, hReachOk1, hNoUB1⟩

theorem circular_compiler_acceptance_unsound :
    StructuralLayoutCert boolSlotLayout ∧
    (CircularTypingToSafety →
      Execution.NoUB (DecodeStep 2 true) DecodeBad (initState boolSlotLayout 2)) ∧
    ¬ Execution.NoUB (DecodeStep 2 true) DecodeBad (initState boolSlotLayout 2) ∧
    ¬ CircularTypingToSafety := by
  have hNotNoUB := admitted_invalid_bool_byte2_exposes_ub.2.2.1
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, hNotNoUB, ?_⟩
  · intro hCirc
    rcases hCirc boolSlotLayout 2 true 2 ⟨rfl, rfl, rfl, rfl⟩ with ⟨hNoUB, _, _⟩
    exact hNoUB
  · intro hCirc
    rcases hCirc boolSlotLayout 2 true 2 ⟨rfl, rfl, rfl, rfl⟩ with ⟨hNoUB, _, _⟩
    exact hNotNoUB hNoUB

theorem config_or_instance_change_invalidates_codec_cert :
    BundleApplicable (boolSlotLayout, 3, true, false) (boolSlotLayout, 3, true, false, 2) ∧
    EndpointSafeAndTyped boolSlotLayout 3 true 2 ∧
    LayoutCertApplicable (boolSlotLayout, 3, true, false) (boolSlotLayout, 3, false, false, 2) ∧
    ¬ CodecCertApplicable (boolSlotLayout, 3, true, false) (boolSlotLayout, 3, false, false, 2) ∧
    ¬ BundleApplicable (boolSlotLayout, 3, true, false) (boolSlotLayout, 3, false, false, 2) ∧
    ¬ Execution.NoUB (DecodeStep 3 false) DecodeBad (initState boolSlotLayout 2) := by
  have hStrictCodec : CodecSemanticsCert 3 true false := by
    rintro _ _ ⟨_, h2 | ⟨_, hCfg⟩⟩
    · exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h2))
    · exact Bool.noConfusion hCfg
  have hInvalid2 : 2 ≠ 0 ∧ 2 ≠ 1 :=
    ⟨fun h => Nat.noConfusion h, fun h => Nat.noConfusion (Nat.succ.inj h)⟩
  have hReachPermissiveUB : Execution.Reach (DecodeStep 3 false)
      (initState boolSlotLayout 2) (true, 7, boolSlotLayout, 2, false) := by
    apply Execution.Reach.tail
    · apply Execution.Reach.tail
      · exact Execution.Reach.refl (initState boolSlotLayout 2)
      · exact Or.inl ⟨boolSlotLayout, 2, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨boolSlotLayout, 2, rfl, ⟨hInvalid2, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩))))
  refine ⟨⟨rfl, rfl, rfl, rfl⟩,
    modular_fact_reuse_endpoint (byte := 2) ⟨rfl, rfl, rfl, rfl⟩ hStrictCodec (Or.inl rfl),
    rfl,
    fun ⟨_, hCfg, _⟩ => Bool.noConfusion hCfg,
    fun ⟨_, _, hCfg, _⟩ => Bool.noConfusion hCfg,
    Execution.bad_prefix_not_noUB (Bad := DecodeBad) hReachPermissiveUB rfl⟩

theorem premise_strengthening_invalidates_caller_reuse :
    CallerValidityPremise false 2 ∧
    EndpointSafeAndTyped boolSlotLayout 0 true 2 ∧
    ¬ CallerValidityPremise true 2 ∧
    ¬ Execution.NoUB (DecodeStep 2 true) DecodeBad (initState boolSlotLayout 2) := by
  have hNotPrem2 : ¬ CallerValidityPremise true 2 := by
    rintro (hFalse | ⟨_, hValid⟩)
    · exact Bool.noConfusion hFalse
    · exact admitted_invalid_bool_byte2_exposes_ub.2.1 hValid
  exact ⟨Or.inl rfl,
    (checked_decoder_safe_for_all_bytes_via_reuse true 2).2.1,
    hNotPrem2,
    admitted_invalid_bool_byte2_exposes_ub.2.2.1⟩

theorem reuse_applicability_matrix :
    -- Class 1: Client-only edit reuses both layout and codec certificates
    (LayoutCertApplicable (boolSlotLayout, 2, true, true) (boolSlotLayout, 2, true, true, 1) ∧
     CodecCertApplicable (boolSlotLayout, 2, true, true) (boolSlotLayout, 2, true, true, 1) ∧
     BundleApplicable (boolSlotLayout, 2, true, true) (boolSlotLayout, 2, true, true, 1) ∧
     CallerValidityPremise true 1 ∧
     EndpointSafeAndTyped boolSlotLayout 2 true 1) ∧
    -- Class 2: Body optimization reuses layout cert, invalidates old codec cert, succeeds with new codec cert
    (LayoutCertApplicable (boolSlotLayout, 0, true, false) (boolSlotLayout, 1, true, false, 2) ∧
     ¬ CodecCertApplicable (boolSlotLayout, 0, true, false) (boolSlotLayout, 1, true, false, 2) ∧
     ¬ BundleApplicable (boolSlotLayout, 0, true, false) (boolSlotLayout, 1, true, false, 2) ∧
     CallerValidityPremise false 2 ∧
     EndpointSafeAndTyped boolSlotLayout 1 true 2) ∧
    -- Class 3: Configuration/instance switch reuses layout cert, invalidates codec cert, exposes UB on byte = 2
    (LayoutCertApplicable (boolSlotLayout, 3, true, false) (boolSlotLayout, 3, false, false, 2) ∧
     ¬ CodecCertApplicable (boolSlotLayout, 3, true, false) (boolSlotLayout, 3, false, false, 2) ∧
     ¬ BundleApplicable (boolSlotLayout, 3, true, false) (boolSlotLayout, 3, false, false, 2) ∧
     ¬ Execution.NoUB (DecodeStep 3 false) DecodeBad (initState boolSlotLayout 2)) ∧
    -- Class 4: Premise strengthening reuses layout cert, invalidates codec cert and caller premise on byte = 2
    (LayoutCertApplicable (boolSlotLayout, 0, true, false) (boolSlotLayout, 2, true, true, 2) ∧
     ¬ CodecCertApplicable (boolSlotLayout, 0, true, false) (boolSlotLayout, 2, true, true, 2) ∧
     ¬ BundleApplicable (boolSlotLayout, 0, true, false) (boolSlotLayout, 2, true, true, 2) ∧
     ¬ CallerValidityPremise true 2 ∧
     ¬ Execution.NoUB (DecodeStep 2 true) DecodeBad (initState boolSlotLayout 2)) := by
  have hUnchecked1 := unchecked_decoder_safe_under_validBoolByte_via_reuse true 1 (Or.inr rfl)
  have hSwap2 := implementation_swap_reuses_layout_cert (layout := boolSlotLayout) ⟨rfl, rfl, rfl, rfl⟩ true 2
  have hCfgSwitch := config_or_instance_change_invalidates_codec_cert
  have hPremStrength := premise_strengthening_invalidates_caller_reuse
  exact ⟨⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, hUnchecked1.1, hUnchecked1.2⟩,
    ⟨rfl, fun ⟨hImpl, _, _⟩ => Nat.noConfusion hImpl, fun ⟨_, hImpl, _, _⟩ => Nat.noConfusion hImpl, Or.inl rfl, hSwap2.2.1⟩,
    ⟨hCfgSwitch.2.2.1, hCfgSwitch.2.2.2.1, hCfgSwitch.2.2.2.2.1, hCfgSwitch.2.2.2.2.2⟩,
    ⟨rfl, fun ⟨hImpl, _, _⟩ => Nat.noConfusion hImpl, fun ⟨_, hImpl, _, _⟩ => Nat.noConfusion hImpl, hPremStrength.2.2.1, hPremStrength.2.2.2⟩⟩

#print axioms admitted_invalid_bool_byte2_exposes_ub
#print axioms discarded_invalid_bool_still_ub
#print axioms circular_compiler_acceptance_unsound
#print axioms config_or_instance_change_invalidates_codec_cert
#print axioms premise_strengthening_invalidates_caller_reuse
#print axioms reuse_applicability_matrix

end AnnealResearch.FactReuseControls
