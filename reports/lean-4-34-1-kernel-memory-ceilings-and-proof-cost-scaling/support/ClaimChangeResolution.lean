import AnnealResearch.Execution

set_option Elab.async false

/-!
Bounded semantic claim-change report model for R-ADEV-02 (motivating A-ADEV-04
and E-ADEV-06), resolution scope for the Linux `x86_64` `-M768` envelope:
- `set_option Elab.async false`
- Zero `inductive` and zero `structure` declarations
- All value definitions marked `noncomputable def` (zero LCNF compilations)
- Hierarchical `compareFields` / `compareTriple` lemmas avoiding unfolded `Eq.ndrec` chains
-/

namespace AnnealResearch.ClaimChangeResolution

/-- Compilation and claim subject `(programHash, configHash, claimId)`. -/
abbrev SubjectBinding : Type := Nat × Nat × Nat

/-- Precondition `(tag, predId)`: `(0,0)` unrestricted, `(1,0)` closedImage,
    `(2,0)` closedImageAndSorted, `(3,id)` namedPredicate `id`. -/
abbrev PreconditionSpec : Type := Nat × Nat

/-- Optional kernel-checked implication certificate `(forwardDischarged, backwardDischarged)`. -/
abbrev ImplicationCert : Type := Bool × Bool

/-- 3x3 grouping of the 9 semantic claim dimensions:
    `((pre, dom, cov), (choice, post, eff), (out, trust, obs))`. -/
abbrev ClaimFields : Type :=
  (PreconditionSpec × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat)

/-- Complete bounded claim description `(subject, fields, proofScriptHash)`. -/
abbrev ClaimDescription : Type := SubjectBinding × ClaimFields × Nat

/-- Structured claim-change report (`FieldRelation`: `0` unchanged, `1` strengthened,
    `2` weakened, `3` unknownUnproved). -/
abbrev ChangeReport : Type :=
  (SubjectBinding × SubjectBinding × Bool) ×
  ((Nat × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat)) ×
  (Bool × Bool × Bool × Bool)

theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem nat_beq_false_of_ne (a : Nat) : ∀ (b : Nat), a ≠ b → Nat.beq a b = false := by
  induction a with
  | zero =>
    intro b hne
    cases b with
    | zero => exact False.elim (hne rfl)
    | succ _ => rfl
  | succ a ih =>
    intro b hne
    cases b with
    | zero => rfl
    | succ b => exact ih b (fun heq => hne (congrArg Nat.succ heq))

theorem subjectMatched_refl (s : SubjectBinding) :
    (Nat.beq s.1 s.1 && Nat.beq s.2.1 s.2.1 && Nat.beq s.2.2 s.2.2) = true := by
  rw [nat_beq_refl s.1, nat_beq_refl s.2.1, nat_beq_refl s.2.2]
  rfl

noncomputable def compareRank (oldRank newRank : Nat) : Nat :=
  if Nat.beq oldRank newRank then 0
  else if Nat.ble oldRank newRank then 1
  else 2

theorem compareRank_refl (n : Nat) : compareRank n n = 0 := by
  unfold compareRank
  rw [nat_beq_refl n]
  rfl

noncomputable def comparePrecondition (oldPre newPre : PreconditionSpec)
    (cert : Option ImplicationCert := none) : Nat :=
  if Nat.beq oldPre.1 newPre.1 && Nat.beq oldPre.2 newPre.2 then 0
  else if Nat.beq oldPre.1 0 && (Nat.beq newPre.1 1 || Nat.beq newPre.1 2) then 2
  else if Nat.beq oldPre.1 1 && Nat.beq newPre.1 0 then 1
  else if Nat.beq oldPre.1 1 && Nat.beq newPre.1 2 then 2
  else if Nat.beq oldPre.1 2 && (Nat.beq newPre.1 0 || Nat.beq newPre.1 1) then 1
  else
    match cert with
    | none => 3
    | some c =>
        match c.1, c.2 with
        | true, true => 0
        | true, false => 1
        | false, true => 2
        | false, false => 3

theorem comparePrecondition_refl (p : PreconditionSpec) (cert : Option ImplicationCert) :
    comparePrecondition p p cert = 0 := by
  unfold comparePrecondition
  rw [nat_beq_refl p.1, nat_beq_refl p.2]
  rfl

noncomputable def compareTriple (a b : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (compareRank a.1 b.1, compareRank a.2.1 b.2.1, compareRank a.2.2 b.2.2)

theorem compareTriple_refl (t : Nat × Nat × Nat) : compareTriple t t = (0, 0, 0) := by
  unfold compareTriple
  rw [compareRank_refl t.1, compareRank_refl t.2.1, compareRank_refl t.2.2]

noncomputable def compareFields (oldF newF : ClaimFields)
    (cert : Option ImplicationCert := none) :
    (Nat × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat) :=
  ((comparePrecondition oldF.1.1 newF.1.1 cert,
    compareRank oldF.1.2.1 newF.1.2.1,
    compareRank oldF.1.2.2 newF.1.2.2),
   compareTriple oldF.2.1 newF.2.1,
   compareTriple oldF.2.2 newF.2.2)

theorem compareFields_refl (f : ClaimFields) (cert : Option ImplicationCert) :
    compareFields f f cert = ((0, 0, 0), (0, 0, 0), (0, 0, 0)) := by
  unfold compareFields
  rw [comparePrecondition_refl f.1.1 cert,
      compareRank_refl f.1.2.1, compareRank_refl f.1.2.2,
      compareTriple_refl f.2.1, compareTriple_refl f.2.2]

noncomputable def buildReport
    (oldSubj newSubj : SubjectBinding) (subjectMatched : Bool)
    (rels : (Nat × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat))
    (proofScriptChanged : Bool) : ChangeReport :=
  let anyWeakened :=
    Nat.beq rels.1.1 2 || Nat.beq rels.1.2.1 2 || Nat.beq rels.1.2.2 2 ||
    Nat.beq rels.2.1.1 2 || Nat.beq rels.2.1.2.1 2 || Nat.beq rels.2.1.2.2 2 ||
    Nat.beq rels.2.2.1 2 || Nat.beq rels.2.2.2.1 2 || Nat.beq rels.2.2.2.2 2
  let anyUnknown :=
    Nat.beq rels.1.1 3 || Nat.beq rels.1.2.1 3 || Nat.beq rels.1.2.2 3 ||
    Nat.beq rels.2.1.1 3 || Nat.beq rels.2.1.2.1 3 || Nat.beq rels.2.1.2.2 3 ||
    Nat.beq rels.2.2.1 3 || Nat.beq rels.2.2.2.1 3 || Nat.beq rels.2.2.2.2 3
  let preserves := subjectMatched && (!anyWeakened) && (!anyUnknown)
  ((oldSubj, newSubj, subjectMatched), rels,
   (proofScriptChanged, anyWeakened, anyUnknown, preserves))

noncomputable def compareClaims (oldClaim newClaim : ClaimDescription)
    (cert : Option ImplicationCert := none) : ChangeReport :=
  buildReport
    oldClaim.1 newClaim.1
    (Nat.beq oldClaim.1.1 newClaim.1.1 &&
     Nat.beq oldClaim.1.2.1 newClaim.1.2.1 &&
     Nat.beq oldClaim.1.2.2 newClaim.1.2.2)
    (compareFields oldClaim.2.1 newClaim.2.1 cert)
    (!Nat.beq oldClaim.2.2 newClaim.2.2)

/-- 1. Reflexive comparison reports all 9 semantic dimensions unchanged (`0`) and preserves the claim. -/
theorem reflexive_report_unchanged (c : ClaimDescription)
    (cert : Option ImplicationCert := none) :
    compareClaims c c cert =
      ((c.1, c.1, true), ((0, 0, 0), (0, 0, 0), (0, 0, 0)), (false, false, false, true)) := by
  unfold compareClaims
  rw [subjectMatched_refl c.1, compareFields_refl c.2.1 cert, nat_beq_refl c.2.2]
  rfl

/-- 2. A proof-script-only edit sets `proofScriptChanged = true` and preserves the claim. -/
theorem proof_script_only_edit_preserves_claim (c : ClaimDescription) (newProofHash : Nat)
    (hdiff : c.2.2 ≠ newProofHash) (cert : Option ImplicationCert := none) :
    compareClaims c (c.1, c.2.1, newProofHash) cert =
      ((c.1, c.1, true), ((0, 0, 0), (0, 0, 0), (0, 0, 0)), (true, false, false, true)) := by
  unfold compareClaims
  rw [subjectMatched_refl c.1, compareFields_refl c.2.1 cert,
      nat_beq_false_of_ne c.2.2 newProofHash hdiff]
  rfl

/-- 3. Discharged bidirectional equivalence (`some (true, true)`) preserves the claim. -/
theorem discharged_equivalence_preserves_claim (c : ClaimDescription) (id1 id2 : Nat) :
    compareClaims (c.1, (((3, id1), c.2.1.1.2), c.2.1.2), c.2.2)
      (c.1, (((3, id2), c.2.1.1.2), c.2.1.2), c.2.2) (some (true, true)) =
      ((c.1, c.1, true), ((0, 0, 0), (0, 0, 0), (0, 0, 0)), (false, false, false, true)) := by
  have hpre : comparePrecondition (3, id1) (3, id2) (some (true, true)) = 0 := by
    unfold comparePrecondition; cases Nat.beq id1 id2 <;> rfl
  unfold compareClaims compareFields
  rw [subjectMatched_refl c.1, hpre,
      compareRank_refl c.2.1.1.2.1, compareRank_refl c.2.1.1.2.2,
      compareTriple_refl c.2.1.2.1, compareTriple_refl c.2.1.2.2,
      nat_beq_refl c.2.2]
  rfl

/-- 4. Unproved predicate change (`id1 ≠ id2`, `cert = none`) reports `unknownUnproved` (`3`). -/
theorem unproved_predicate_change_reports_unknown (c : ClaimDescription) (id1 id2 : Nat)
    (hne : id1 ≠ id2) :
    compareClaims (c.1, (((3, id1), c.2.1.1.2), c.2.1.2), c.2.2)
      (c.1, (((3, id2), c.2.1.1.2), c.2.1.2), c.2.2) none =
      ((c.1, c.1, true), ((3, 0, 0), (0, 0, 0), (0, 0, 0)), (false, false, true, false)) := by
  have hpre : comparePrecondition (3, id1) (3, id2) none = 3 := by
    unfold comparePrecondition; rw [nat_beq_false_of_ne id1 id2 hne]; rfl
  unfold compareClaims compareFields
  rw [subjectMatched_refl c.1, hpre,
      compareRank_refl c.2.1.1.2.1, compareRank_refl c.2.1.1.2.2,
      compareTriple_refl c.2.1.2.1, compareTriple_refl c.2.1.2.2,
      nat_beq_refl c.2.2]
  rfl

/-- 5. Mismatched subjects (`c.1.1 ≠ newProgHash`) reject claim preservation. -/
theorem subject_mismatch_rejects_preservation (c : ClaimDescription) (newProgHash : Nat)
    (hmismatch : c.1.1 ≠ newProgHash) (cert : Option ImplicationCert := none) :
    compareClaims c ((newProgHash, c.1.2.1, c.1.2.2), c.2.1, c.2.2) cert =
      ((c.1, (newProgHash, c.1.2.1, c.1.2.2), false),
       ((0, 0, 0), (0, 0, 0), (0, 0, 0)), (false, false, false, false)) := by
  unfold compareClaims
  rw [nat_beq_false_of_ne c.1.1 newProgHash hmismatch,
      compareFields_refl c.2.1 cert, nat_beq_refl c.2.2]
  rfl

/-- 6. Weakening any single semantic dimension on the canonical baseline claim sets
    `anyWeakened = true` and `preservesOrStrengthensClaim = false`. -/
theorem single_field_weakening_rejects_preservation :
    let s : SubjectBinding := (101, 202, 1)
    let base : ClaimDescription := (s, (((0, 0), 3, 2), (2, 3, 2), (2, 2, 2)), 5001)
    (compareClaims base (s, (((2, 0), 3, 2), (2, 3, 2), (2, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 2, 2), (2, 3, 2), (2, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 1), (2, 3, 2), (2, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 0), (2, 3, 2), (2, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 2), (0, 3, 2), (2, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 2), (2, 2, 2), (2, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 2), (2, 3, 1), (2, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 2), (2, 3, 2), (1, 2, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 2), (2, 3, 2), (2, 1, 2)), 5001) none).2.2 =
      (false, true, false, false) ∧
    (compareClaims base (s, (((0, 0), 3, 2), (2, 3, 2), (2, 2, 1)), 5001) none).2.2 =
      (false, true, false, false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Semantic interpretation of `ExecutionCoverage` (`2` = allFinitePrefixes,
    `1` = completedRunsOnly, `0` = singleExecutionWitness). -/
def SatisfiesCoverage {State : Type}
    (sys : (State → State → Prop) × (State → Prop)) (init : State) (cov : Nat) : Prop :=
  if Nat.beq cov 2 then
    Execution.NoUB sys.1 sys.2 init
  else if Nat.beq cov 1 then
    ∀ s, Execution.Reach sys.1 init s → (∀ next, ¬ sys.1 s next) → ¬ sys.2 s
  else
    ∃ s, sys.1 init s ∧ ¬ sys.2 s

noncomputable def branchingBadAndSafe : (Nat → Nat → Prop) × (Nat → Prop) :=
  (fun s t => (s = 0 ∧ (t = 1 ∨ t = 2)) ∨ (s = 2 ∧ t = 2),
   fun s => s = 2)

/-- 7. Bridge connecting `ExecutionCoverage` to `AnnealResearch.Execution`. -/
theorem execution_coverage_semantics_bridge :
    (∀ {State : Type} (sys : (State → State → Prop) × (State → Prop)) (init : State),
      SatisfiesCoverage sys init 2 →
      (∃ s, sys.1 init s) →
      SatisfiesCoverage sys init 0) ∧
    SatisfiesCoverage branchingBadAndSafe 0 0 ∧
    SatisfiesCoverage branchingBadAndSafe 0 1 ∧
    ¬ SatisfiesCoverage branchingBadAndSafe 0 2 ∧
    ¬ Execution.NoUB branchingBadAndSafe.1 branchingBadAndSafe.2 0 := by
  have hnotub : ¬ Execution.NoUB branchingBadAndSafe.1 branchingBadAndSafe.2 0 :=
    Execution.bad_prefix_not_noUB
      (Execution.Reach.tail (Execution.Reach.refl 0) (Or.inl ⟨rfl, Or.inr rfl⟩))
      rfl
  refine ⟨?_, ?_, ?_, hnotub, hnotub⟩
  · intro State sys init hsafe henabled
    rcases henabled with ⟨s, hstep⟩
    exact ⟨s, hstep, hsafe s (Execution.Reach.tail (Execution.Reach.refl init) hstep)⟩
  · refine ⟨1, Or.inl ⟨rfl, Or.inl rfl⟩, ?_⟩
    intro h; cases h
  · intro s _ hterm hbad
    exact hterm 2 (Or.inr ⟨hbad, rfl⟩)

#print axioms AnnealResearch.ClaimChangeResolution.reflexive_report_unchanged
#print axioms AnnealResearch.ClaimChangeResolution.proof_script_only_edit_preserves_claim
#print axioms AnnealResearch.ClaimChangeResolution.discharged_equivalence_preserves_claim
#print axioms AnnealResearch.ClaimChangeResolution.unproved_predicate_change_reports_unknown
#print axioms AnnealResearch.ClaimChangeResolution.subject_mismatch_rejects_preservation
#print axioms AnnealResearch.ClaimChangeResolution.single_field_weakening_rejects_preservation
#print axioms AnnealResearch.ClaimChangeResolution.execution_coverage_semantics_bridge

end AnnealResearch.ClaimChangeResolution
