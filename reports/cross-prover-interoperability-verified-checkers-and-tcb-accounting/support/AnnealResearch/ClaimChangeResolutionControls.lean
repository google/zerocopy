import AnnealResearch.ClaimChangeResolution

set_option Elab.async false

/-!
Independent expected-difference suite and negative controls for R-ADEV-02
(motivating A-ADEV-04 and E-ADEV-06), resolution scope for the Linux `x86_64`
`-M768` envelope:
- `set_option Elab.async false`
- Zero `inductive` and zero `structure` declarations
- All value definitions marked `noncomputable def` (zero LCNF compilations)
- 19 top-level declarations total
-/

namespace AnnealResearch.ClaimChangeResolutionControls

open AnnealResearch.ClaimChangeResolution

/-- Frozen baseline claim requiring full prefix safety (`2`), demonic/resolved-angelic
    choice coverage (`2`), exact value+alias postcondition (`3`), exact residual/frame (`2`),
    typed-error NoUB outcomes (`2`), kernel-checked trust (`2`), and full microevent trace (`2`). -/
noncomputable def baselineClaim : ClaimDescription :=
  ((101, 202, 1), (((3, 1), 3, 2), (2, 3, 2), (2, 2, 2)), 5001)

/-- Pair 1: Proof-script-only edit (`proofScriptHash` changed to `5002`). -/
noncomputable def proofOnlyEdit : ClaimDescription :=
  ((101, 202, 1), (((3, 1), 3, 2), (2, 3, 2), (2, 2, 2)), 5002)

/-- Pair 2: Predicate rephrasing (`(3, 1) → (3, 2)`) with discharged certificate. -/
noncomputable def dischargedRephraseEdit : ClaimDescription :=
  ((101, 202, 1), (((3, 2), 3, 2), (2, 3, 2), (2, 2, 2)), 5003)

/-- Pair 3: Unproved predicate rephrasing (`(3, 1) → (3, 2)`, `cert = none`). -/
noncomputable def unprovedRephraseEdit : ClaimDescription :=
  ((101, 202, 1), (((3, 2), 3, 2), (2, 3, 2), (2, 2, 2)), 5001)

/-- Pair 4: Reduced input domain (`3 → 2`) and strengthened precondition (`(2, 0)`). -/
noncomputable def reducedDomainAndPreconditionEdit : ClaimDescription :=
  ((101, 202, 1), (((2, 0), 2, 2), (2, 3, 2), (2, 2, 2)), 5004)

/-- Pair 5: Weakened postcondition (`3 → 2`) and relaxed memory effect frame (`2 → 1`). -/
noncomputable def omittedEffectAndPostconditionEdit : ClaimDescription :=
  ((101, 202, 1), (((3, 1), 3, 2), (2, 2, 1), (2, 2, 2)), 5005)

/-- Pair 6: Weakened outcome discipline (`2 → 1`) and expanded trust surface (`2 → 1`). -/
noncomputable def outcomeAndTrustWeakeningEdit : ClaimDescription :=
  ((101, 202, 1), (((3, 1), 3, 2), (2, 3, 2), (1, 1, 2)), 5006)

/-- Pair 7: Weakened observation/leakage policy (`2 → 1`) with unchanged postcondition/outcomes. -/
noncomputable def observationLeakageWeakeningEdit : ClaimDescription :=
  ((101, 202, 1), (((3, 1), 3, 2), (2, 3, 2), (2, 2, 1)), 5007)

/-- Pair 8: Execution coverage weakened from `2` to `0` and choice quantifier weakened to `0`. -/
noncomputable def universalToSingleExecutionEdit : ClaimDescription :=
  ((101, 202, 1), (((3, 1), 3, 0), (0, 3, 2), (2, 2, 2)), 5008)

/-- Independently authored expected difference specification for a claim-edit pair. -/
abbrev ExpectedDiff : Type :=
  Bool ×
  ((Nat × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat)) ×
  (Bool × Bool × Bool × Bool)

/-- Independent oracle checking whether a `ChangeReport` matches an `ExpectedDiff`. -/
noncomputable def matchesExpectedDiff (r : ChangeReport) (e : ExpectedDiff) : Bool :=
  (r.1.2.2 == e.1) &&
  Nat.beq r.2.1.1.1 e.2.1.1.1 &&
  Nat.beq r.2.1.1.2.1 e.2.1.1.2.1 &&
  Nat.beq r.2.1.1.2.2 e.2.1.1.2.2 &&
  Nat.beq r.2.1.2.1.1 e.2.1.2.1.1 &&
  Nat.beq r.2.1.2.1.2.1 e.2.1.2.1.2.1 &&
  Nat.beq r.2.1.2.1.2.2 e.2.1.2.1.2.2 &&
  Nat.beq r.2.1.2.2.1 e.2.1.2.2.1 &&
  Nat.beq r.2.1.2.2.2.1 e.2.1.2.2.2.1 &&
  Nat.beq r.2.1.2.2.2.2 e.2.1.2.2.2.2 &&
  (r.2.2.1 == e.2.2.1) &&
  (r.2.2.2.1 == e.2.2.2.1) &&
  (r.2.2.2.2.1 == e.2.2.2.2.1) &&
  (r.2.2.2.2.2 == e.2.2.2.2.2)

/-- 1. Across all 8 concrete claim-edit pairs, `compareClaims` matches the independently
    authored `ExpectedDiff` specification field-by-field. -/
theorem independent_suite_matches_expected_diffs :
    matchesExpectedDiff
      (compareClaims baselineClaim proofOnlyEdit none)
      (true, ((0, 0, 0), (0, 0, 0), (0, 0, 0)), (true, false, false, true)) = true ∧
    matchesExpectedDiff
      (compareClaims baselineClaim dischargedRephraseEdit (some (true, true)))
      (true, ((0, 0, 0), (0, 0, 0), (0, 0, 0)), (true, false, false, true)) = true ∧
    matchesExpectedDiff
      (compareClaims baselineClaim unprovedRephraseEdit none)
      (true, ((3, 0, 0), (0, 0, 0), (0, 0, 0)), (false, false, true, false)) = true ∧
    matchesExpectedDiff
      (compareClaims baselineClaim reducedDomainAndPreconditionEdit (some (false, true)))
      (true, ((2, 2, 0), (0, 0, 0), (0, 0, 0)), (true, true, false, false)) = true ∧
    matchesExpectedDiff
      (compareClaims baselineClaim omittedEffectAndPostconditionEdit none)
      (true, ((0, 0, 0), (0, 2, 2), (0, 0, 0)), (true, true, false, false)) = true ∧
    matchesExpectedDiff
      (compareClaims baselineClaim outcomeAndTrustWeakeningEdit none)
      (true, ((0, 0, 0), (0, 0, 0), (2, 2, 0)), (true, true, false, false)) = true ∧
    matchesExpectedDiff
      (compareClaims baselineClaim observationLeakageWeakeningEdit none)
      (true, ((0, 0, 0), (0, 0, 0), (0, 0, 2)), (true, true, false, false)) = true ∧
    matchesExpectedDiff
      (compareClaims baselineClaim universalToSingleExecutionEdit none)
      (true, ((0, 0, 2), (2, 0, 0), (0, 0, 0)), (true, true, false, false)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 2. On `universalToSingleExecutionEdit`, the weakened coverage claim (`0`) admits
    `branchingBadAndSafe` while the baseline coverage claim (`2`) rejects it, and
    `compareClaims` flags `coverageRel = 2` and rejects preservation. -/
theorem universal_to_single_execution_admits_unsafe_machine :
    SatisfiesCoverage branchingBadAndSafe 0 universalToSingleExecutionEdit.2.1.1.2.2 ∧
    ¬ SatisfiesCoverage branchingBadAndSafe 0 baselineClaim.2.1.1.2.2 ∧
    (compareClaims baselineClaim universalToSingleExecutionEdit none).2.1.1.2.2 = 2 ∧
    (compareClaims baselineClaim universalToSingleExecutionEdit none).2.1.2.1.1 = 2 ∧
    (compareClaims baselineClaim universalToSingleExecutionEdit none).2.2.2.2.2 = false :=
  ⟨execution_coverage_semantics_bridge.2.1,
    execution_coverage_semantics_bridge.2.2.2.1,
    rfl, rfl, rfl⟩

/-- 3. On `observationLeakageWeakeningEdit`, weakening observation from `2` to `1` is
    flagged as `observationRel = 2` and rejected even though `postcondition` and
    `outcomes` are unchanged (`0`). -/
theorem observation_marginal_weakening_exposed :
    let r := compareClaims baselineClaim observationLeakageWeakeningEdit none
    r.2.1.2.1.2.1 = 0 ∧
    r.2.1.2.2.1 = 0 ∧
    r.2.1.2.2.2.2 = 2 ∧
    r.2.2.2.1 = true ∧
    r.2.2.2.2.2 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Defective change-report generator that inspects only subject, precondition,
    postcondition, and outcomes, silently reporting `0` (`unchanged`) on domain,
    coverage, choice quantifier, effects, trust, and observation. -/
noncomputable def defectiveReportOmittingCoverageAndObs (oldClaim newClaim : ClaimDescription)
    (cert : Option ImplicationCert) : ChangeReport :=
  buildReport
    oldClaim.1 newClaim.1
    (Nat.beq oldClaim.1.1 newClaim.1.1 &&
     Nat.beq oldClaim.1.2.1 newClaim.1.2.1 &&
     Nat.beq oldClaim.1.2.2 newClaim.1.2.2)
    ((comparePrecondition oldClaim.2.1.1.1 newClaim.2.1.1.1 cert, 0, 0),
     (0, compareRank oldClaim.2.1.2.1.2.1 newClaim.2.1.2.1.2.1, 0),
     (compareRank oldClaim.2.1.2.2.1 newClaim.2.1.2.2.1, 0, 0))
    (!Nat.beq oldClaim.2.2 newClaim.2.2)

/-- 4. Negative control: `defectiveReportOmittingCoverageAndObs` falsely reports
    `preservesOrStrengthensClaim = true` on both `observationLeakageWeakeningEdit`
    and `universalToSingleExecutionEdit`, whereas `compareClaims` rejects both. -/
theorem omitted_field_generator_control :
    (defectiveReportOmittingCoverageAndObs
        baselineClaim observationLeakageWeakeningEdit none).2.2.2.2.2 = true ∧
    (defectiveReportOmittingCoverageAndObs
        baselineClaim universalToSingleExecutionEdit none).2.2.2.2.2 = true ∧
    (compareClaims
        baselineClaim observationLeakageWeakeningEdit none).2.2.2.2.2 = false ∧
    (compareClaims
        baselineClaim universalToSingleExecutionEdit none).2.2.2.2.2 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Circular acceptance oracle that derives expected reports from the generator being tested. -/
noncomputable def selfOracle
    (gen : ClaimDescription → ClaimDescription → Option ImplicationCert → ChangeReport)
    (oldClaim newClaim : ClaimDescription) (cert : Option ImplicationCert) : Bool :=
  let r := gen oldClaim newClaim cert
  matchesExpectedDiff r (r.1.2.2, r.2.1, r.2.2)

/-- 5. Circularity control: `defectiveReportOmittingCoverageAndObs` trivially passes its
    own `selfOracle` on all 8 pairs, but fails the independent `ExpectedDiff` oracle on
    pairs 7 (`observationLeakageWeakeningEdit`) and 8 (`universalToSingleExecutionEdit`). -/
theorem self_oracle_circularity_control :
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim proofOnlyEdit none = true ∧
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim dischargedRephraseEdit (some (true, true)) = true ∧
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim unprovedRephraseEdit none = true ∧
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim reducedDomainAndPreconditionEdit (some (false, true)) = true ∧
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim omittedEffectAndPostconditionEdit none = true ∧
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim outcomeAndTrustWeakeningEdit none = true ∧
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim observationLeakageWeakeningEdit none = true ∧
    selfOracle defectiveReportOmittingCoverageAndObs
      baselineClaim universalToSingleExecutionEdit none = true ∧
    matchesExpectedDiff
      (defectiveReportOmittingCoverageAndObs baselineClaim observationLeakageWeakeningEdit none)
      (true, ((0, 0, 0), (0, 0, 0), (0, 0, 2)), (true, true, false, false)) = false ∧
    matchesExpectedDiff
      (defectiveReportOmittingCoverageAndObs baselineClaim universalToSingleExecutionEdit none)
      (true, ((0, 0, 2), (2, 0, 0), (0, 0, 0)), (true, true, false, false)) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 6. Syntax-similarity control: identical `proofScriptHash` and 8 identical semantic fields
    do not mask an unproved predicate change (`unprovedRephraseEdit` is rejected with
    `anyUnknown = true`), whereas a different `proofScriptHash` and different predicate ID
    with a kernel-discharged bidirectional certificate (`dischargedRephraseEdit`) is accepted. -/
theorem syntax_similarity_control :
    let rUnproved := compareClaims baselineClaim unprovedRephraseEdit none
    let rDischarged := compareClaims baselineClaim dischargedRephraseEdit (some (true, true))
    rUnproved.2.2.1 = false ∧
    rUnproved.2.1.1.1 = 3 ∧
    rUnproved.2.2.2.2.1 = true ∧
    rUnproved.2.2.2.2.2 = false ∧
    rDischarged.2.2.1 = true ∧
    rDischarged.2.1.1.1 = 0 ∧
    rDischarged.2.2.2.1 = false ∧
    rDischarged.2.2.2.2.1 = false ∧
    rDischarged.2.2.2.2.2 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms AnnealResearch.ClaimChangeResolutionControls.independent_suite_matches_expected_diffs
#print axioms AnnealResearch.ClaimChangeResolutionControls.universal_to_single_execution_admits_unsafe_machine
#print axioms AnnealResearch.ClaimChangeResolutionControls.observation_marginal_weakening_exposed
#print axioms AnnealResearch.ClaimChangeResolutionControls.omitted_field_generator_control
#print axioms AnnealResearch.ClaimChangeResolutionControls.self_oracle_circularity_control
#print axioms AnnealResearch.ClaimChangeResolutionControls.syntax_similarity_control

end AnnealResearch.ClaimChangeResolutionControls
