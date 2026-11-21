import ToyTransfer.Disclaimer
import ToyTransfer.Direction
import ToyTransfer.SimCountermodels

/-!
# Definition examples, and non-vacuity and tightness instances for the no-relation results

For each definition: an intended instance it admits and an instance it must reject.
-/

namespace Toy.Transfer

/-! ## Structures, environments, satisfaction -/

/-- The structure with empty carrier (admitted: carriers may be empty). -/
def emptyStr : Str := ⟨Empty, fun _ _ => False, fun _ => False⟩

/-- Universal sentences hold vacuously and existential ones fail in the empty structure. -/
theorem emptyStr_example : SatS emptyStr allP ∧ ¬ SatS emptyStr exP :=
  ⟨fun a => (nomatch a), by
    intro h
    obtain ⟨a, _⟩ := h
    exact nomatch a⟩

/-- `∃x, x = x`. -/
def exSelfEq : Fml 0 := .ex (.eq 0 0)

/-- Because empty carriers are admitted, the classically valid `∃x, x = x` is not valid over
all structures; it is valid over the non-empty ones. -/
theorem exSelfEq_valid_iff_nonempty_carriers :
    ¬ ValidIn (fun _ => True) exSelfEq ∧ ValidIn (fun M => Nonempty M.carrier) exSelfEq :=
  ⟨fun h => (h emptyStr trivial).elim (fun a _ => nomatch a), fun _ ⟨x⟩ => ⟨x, rfl⟩⟩

theorem env_cons_example : Env.cons (5 : Nat) (env1 7) 0 = 5 ∧ Env.cons (5 : Nat) (env1 7) 1 = 7 :=
  ⟨rfl, rfl⟩

theorem sat_pos_example : Sat S2Cyc.toStr allExR Fin.elim0 := by decide
theorem sat_neg_example : ¬ Sat S1N.toStr allExR Fin.elim0 := by decide
theorem satS_pos_example : SatS S1P.toStr allP := by decide
theorem satS_neg_example : ¬ SatS S2PN.toStr allP := by decide

/-! ## Classes -/

/-- `∃x ∀y, R x y`. -/
def exAllR : Fml 0 := .ex (.all (.rel 1 0))

theorem isQF_examples : IsQF notP0 ∧ ¬ IsQF allP ∧ ¬ IsQF exP := by decide
theorem isUniv_examples : IsUniv allRImpEq ∧ ¬ IsUniv exP ∧ ¬ IsUniv allExR := by decide
theorem isExist_examples :
    IsExist exExNeq ∧ ¬ IsExist allP ∧ ¬ IsExist exAllR ∧ ¬ IsExist exPAndExP := by decide
theorem isAE_examples : IsAE allExR ∧ ¬ IsAE exAllR := by decide
theorem isEA_examples : IsEA exAllR ∧ ¬ IsEA allExR := by decide
theorem isPos_examples : IsPos allExR ∧ ¬ IsPos exNotP := by decide
theorem isPosExist_examples :
    IsPosExist exP ∧ IsPosExist exPAndExP ∧ ¬ IsPosExist allP ∧ ¬ IsPosExist exNotP := by decide
theorem cls_test_examples : Cls.test .ae allExR = true ∧ Cls.test .univ allExR = false := by decide

/-- The prenex existential class does not contain every positive existential formula:
`(∃x, P x) ∧ (∃y, P y)` is positive existential but neither existential, `∀∃` nor `∃∀` in
the prenex sense. -/
theorem posExist_not_subset_exist :
    IsPosExist exPAndExP ∧ ¬ IsExist exPAndExP ∧ ¬ IsAE exPAndExP ∧ ¬ IsEA exPAndExP := by
  decide

/-- No positive formula is unsatisfiable: every positive formula holds, under every
environment, in the one-element structure `S1Full` where `R` and `P` hold everywhere. -/
theorem pos_holds_in_full_one_point {n : Nat} {φ : Fml n} (hφ : IsPos φ)
    (e : Fin n → S1Full.toStr.carrier) : Sat S1Full.toStr φ e := by
  induction hφ with
  | rel i j => exact rfl
  | pred i => exact rfl
  | eq i j => exact Subsingleton.elim (α := Fin 1) _ _
  | and _ _ ih1 ih2 => exact ⟨ih1 e, ih2 e⟩
  | or _ _ ih1 _ => exact .inl (ih1 e)
  | all _ ih => exact fun a => ih _
  | ex _ ih => exact ⟨0, ih _⟩

theorem isEqFree_examples : IsEqFree notP0 ∧ IsEqFree allP ∧ ¬ IsEqFree neq01 :=
  ⟨.neg (.pred 0), .all (.pred 0), fun h => by cases h with | neg h => exact nomatch h⟩

/-! ## Map laws and kinds -/

theorem preservesR_examples : PreservesR inclCyc ∧ ¬ PreservesR lowerR := by decide
theorem preservesP_examples : PreservesP raiseP ∧ ¬ PreservesP lowerP := by decide
theorem reflectsR_examples : ReflectsR inclCyc ∧ ¬ ReflectsR raiseR := by decide
theorem reflectsP_examples : ReflectsP inclPN ∧ ¬ ReflectsP raiseP := by decide
theorem isHom_examples : IsHom squashP ∧ ¬ IsHom lowerP := by decide
theorem isStrongHom_examples : IsStrongHom collapse ∧ ¬ IsStrongHom raiseP := by decide
theorem isEmbedding_examples : IsEmbedding inclCyc ∧ ¬ IsEmbedding collapse := by decide
theorem isSurjHom_examples : IsSurjHom squashP ∧ ¬ IsSurjHom inclPN := by decide
theorem isIso_examples :
    IsIso (A := S1P.toStr) (B := S1P.toStr) id ∧ ¬ IsIso raiseP ∧ ¬ IsIso inclPN ∧
    ¬ IsIso collapse := by decide
theorem mapKind_holds_examples : MapKind.Holds .strong collapse ∧ ¬ MapKind.Holds .emb collapse := by
  decide

/-- An injective homomorphism that does not reflect `R` is not an embedding: `raiseR` adds
the loop `R 0 0`. -/
theorem injective_hom_not_embedding_example :
    IsHom raiseR ∧ Function.Injective raiseR ∧ ¬ IsEmbedding raiseR := by decide

/-- `qf_sat_iff_of_strongHom_of_eqFree` applies beyond embeddings: `collapse` is a
non-injective strong homomorphism and `¬ P x₀` is quantifier-free and equality-free. -/
theorem qf_sat_iff_of_strongHom_of_eqFree_nonvacuous :
    IsQF notP0 ∧ IsEqFree notP0 ∧ IsStrongHom collapse ∧ ¬ Function.Injective collapse ∧
    Sat S2E.toStr notP0 (env1 0) :=
  ⟨by decide, .neg (.pred 0), by decide, by decide, by decide⟩

theorem dir_transfer_examples : Dir.Transfer .bwd True False ∧ ¬ Dir.Transfer .fwd True False :=
  ⟨fun h => h.elim, fun h => h trivial⟩

/-! ## Transfer predicate and tables -/

theorem preserves_examples : Preserves .posExist .hom .fwd ∧ ¬ Preserves .univ .emb .fwd :=
  ⟨preserves_posExist_fwd .hom, refute_by_allP_ext (by decide) inclPN_emb⟩

theorem preservesSent_examples : PreservesSent .posExist .hom .fwd ∧ ¬ PreservesSent .univ .emb .fwd :=
  ⟨(preserves_posExist_fwd .hom).toSent, refuteS_by_allP_ext (by decide) inclPN_emb⟩

theorem licensedB_examples : licensedB .univ .emb .bwd = true ∧ licensedB .univ .emb .fwd = false :=
  ⟨rfl, rfl⟩

theorem licensedForB_examples : licensedForB exP .emb .fwd = true ∧ licensedForB allP .emb .fwd = false := by
  decide

theorem bothOutcomesNonIso_examples :
    BothOutcomesNonIso .univ .emb .fwd ∧ ¬ BothOutcomesNonIso .univ .emb .bwd :=
  ⟨(bothOutcomesNonIso_iff_unlicensed _ _ _).2 rfl,
    fun h => absurd ((bothOutcomesNonIso_iff_unlicensed _ _ _).1 h) (by decide)⟩

/-- `∃x, P x ∧ ¬ P x` (unsatisfiable). -/
def contra : Fml 0 := .ex (.and (.pred 0) (.neg (.pred 0)))

theorem contra_unsat : UnsatIn (fun _ => True) contra := by
  intro M _ h
  obtain ⟨_, h1, h2⟩ := h
  exact h2 h1

theorem exclMid_valid : ValidIn (fun _ => True) exclMid :=
  fun M _ a => Classical.em (M.P a)

theorem validIn_examples : ValidIn (fun _ => True) exclMid ∧ ¬ ValidIn (fun _ => True) exP :=
  ⟨exclMid_valid, fun h => absurd (h S1N.toStr trivial) (by decide)⟩

theorem unsatIn_examples : UnsatIn (fun _ => True) contra ∧ ¬ UnsatIn (fun _ => True) exP :=
  ⟨contra_unsat, fun h => h S1P.toStr trivial (by decide)⟩

theorem truthLicensed_examples :
    TruthLicensed .exist .emb .modelToSystem ∧ ¬ TruthLicensed .univ .emb .modelToSystem :=
  ⟨((licences_exact .emb .modelToSystem .exist).1).2 (by decide),
    fun h => absurd (((licences_exact .emb .modelToSystem .univ).1).1 h) (by decide)⟩

theorem falsityLicensed_examples :
    FalsityLicensed .univ .emb .modelToSystem ∧ ¬ FalsityLicensed .exist .emb .modelToSystem :=
  ⟨((licences_exact .emb .modelToSystem .univ).2).2 (by decide),
    fun h => absurd (((licences_exact .emb .modelToSystem .exist).2).1 h) (by decide)⟩

/-! ## No relation: non-vacuity and tightness -/

/-- Non-vacuity of the no-relation characterizations, same class: over all structures,
`∃x, P x` is neither valid nor unsatisfiable, and none of truth transfer, falsity transfer
or refutation is licensed. -/
theorem unrelated_nonvacuous :
    (∃ M, (fun _ => True) M ∧ SatS M exP) ∧ (∃ M, (fun _ => True) M ∧ ¬ SatS M exP) ∧
    ¬ (∀ T R, (fun _ => True) T → (fun _ => True) R → SatS T exP → SatS R exP) ∧
    ¬ (∀ T R, (fun _ => True) T → (fun _ => True) R → ¬ SatS T exP → ¬ SatS R exP) ∧
    ¬ (∀ T R, (fun _ => True) T → (fun _ => True) R → SatS T exP → ¬ SatS R exP) := by
  have h1 : SatS S1P.toStr exP := by decide
  have h2 : ¬ SatS S1N.toStr exP := by decide
  exact ⟨⟨_, trivial, h1⟩, ⟨_, trivial, h2⟩,
    fun h => h2 (h _ _ trivial trivial h1), fun h => h _ _ trivial trivial h2 h1,
    fun h => h _ _ trivial trivial h1 h1⟩

/-- Two different classes: if the systems are the structures with non-empty carrier, then
for every model `T` (of any class) and every such system `R`, truth of `∃x, x = x` in `T`
implies its truth in `R`, because the system class decides it, although the sentence is
not valid over all structures. -/
theorem unrelated_two_class_example :
    (∀ T R, (fun _ => True) T → (fun M : Str => Nonempty M.carrier) R →
      SatS T exSelfEq → SatS R exSelfEq) ∧
    ¬ ValidIn (fun _ => True) exSelfEq ∧ ¬ UnsatIn (fun _ => True) exSelfEq :=
  ⟨(unrelated_truth_transfer_iff _ _ _).2 (.inr exSelfEq_valid_iff_nonempty_carriers.2),
    exSelfEq_valid_iff_nonempty_carriers.1,
    fun h => h S1N.toStr trivial ⟨0, rfl⟩⟩

/-- The narrow-scope readings differ from the statements characterized in
`unrelated_truth_transfer_iff`, `unrelated_falsity_transfer_iff` and
`unrelated_refutation_licensed_iff`. Reading "truth of `φ` in every model of `KM` gives
truth of `φ` in every system of `KS`" as `ValidIn KM φ → ValidIn KS φ` (and similarly
`UnsatIn KM φ → UnsatIn KS φ` for falsity, `ValidIn KM φ → UnsatIn KS φ` for refutation):
for `KM = KS =` all structures and `φ = ∃x, P x`, each narrow-scope implication holds,
while the right-hand side of the corresponding characterization fails. -/
theorem narrow_scope_readings_differ_from_unrelated_transfer :
    ((ValidIn (fun _ => True) exP → ValidIn (fun _ => True) exP) ∧
      ¬ (UnsatIn (fun _ => True) exP ∨ ValidIn (fun _ => True) exP)) ∧
    ((UnsatIn (fun _ => True) exP → UnsatIn (fun _ => True) exP) ∧
      ¬ (ValidIn (fun _ => True) exP ∨ UnsatIn (fun _ => True) exP)) ∧
    ((ValidIn (fun _ => True) exP → UnsatIn (fun _ => True) exP) ∧
      ¬ (UnsatIn (fun _ => True) exP ∨ UnsatIn (fun _ => True) exP)) := by
  have h1 : SatS S1P.toStr exP := by decide
  have h2 : ¬ SatS S1N.toStr exP := by decide
  have hnv : ¬ ValidIn (fun _ => True) exP := fun hv => h2 (hv _ trivial)
  have hnu : ¬ UnsatIn (fun _ => True) exP := fun hu => hu _ trivial h1
  exact ⟨⟨id, fun h => h.elim hnu hnv⟩, ⟨id, fun h => h.elim hnv hnu⟩,
    ⟨fun hv => absurd hv hnv, fun h => h.elim hnu hnu⟩⟩

/-- Tightness of `hsatM` in `unrelated_model_result_consistent_with_both`: with models
`KM := {M | ¬ M ⊨ ∃x, P x}` and systems `KS :=` all structures, the other two hypotheses
hold, `hsatM` fails, and so does the conclusion. -/
theorem consistent_with_both_needs_model_satisfiable :
    ¬ (∃ T, (fun M => ¬ SatS M exP) T ∧ SatS T exP) ∧
    (∃ R, (fun _ => True) R ∧ SatS R exP) ∧ (∃ R, (fun _ => True) R ∧ ¬ SatS R exP) ∧
    ¬ (∃ T, (fun M => ¬ SatS M exP) T ∧ SatS T exP ∧
      (∃ R, (fun _ => True) R ∧ SatS R exP) ∧ (∃ R, (fun _ => True) R ∧ ¬ SatS R exP)) := by
  have h1 : SatS S1P.toStr exP := by decide
  have h2 : ¬ SatS S1N.toStr exP := by decide
  exact ⟨fun ⟨_, hT, hTφ⟩ => hT hTφ, ⟨_, trivial, h1⟩, ⟨_, trivial, h2⟩,
    fun ⟨_, hT, hTφ, _⟩ => hT hTφ⟩

/-- Tightness of `hsatS`: models all structures, systems `KS := {M | ¬ M ⊨ ∃x, P x}`. -/
theorem consistent_with_both_needs_system_satisfiable :
    (∃ T, (fun _ => True) T ∧ SatS T exP) ∧
    ¬ (∃ R, (fun M => ¬ SatS M exP) R ∧ SatS R exP) ∧
    (∃ R, (fun M => ¬ SatS M exP) R ∧ ¬ SatS R exP) ∧
    ¬ (∃ T, (fun _ => True) T ∧ SatS T exP ∧
      (∃ R, (fun M => ¬ SatS M exP) R ∧ SatS R exP) ∧
      (∃ R, (fun M => ¬ SatS M exP) R ∧ ¬ SatS R exP)) := by
  have h1 : SatS S1P.toStr exP := by decide
  have h2 : ¬ SatS S1N.toStr exP := by decide
  exact ⟨⟨_, trivial, h1⟩, fun ⟨_, hR, hRφ⟩ => hR hRφ, ⟨_, h2, h2⟩,
    fun ⟨_, _, _, ⟨_, hR, hRφ⟩, _⟩ => hR hRφ⟩

/-- Tightness of `hnvS`: models all structures, systems `KS := {M | M ⊨ ∃x, P x}`. -/
theorem consistent_with_both_needs_system_not_valid :
    (∃ T, (fun _ => True) T ∧ SatS T exP) ∧
    (∃ R, (fun M => SatS M exP) R ∧ SatS R exP) ∧
    ¬ (∃ R, (fun M => SatS M exP) R ∧ ¬ SatS R exP) ∧
    ¬ (∃ T, (fun _ => True) T ∧ SatS T exP ∧
      (∃ R, (fun M => SatS M exP) R ∧ SatS R exP) ∧
      (∃ R, (fun M => SatS M exP) R ∧ ¬ SatS R exP)) := by
  have h1 : SatS S1P.toStr exP := by decide
  exact ⟨⟨_, trivial, h1⟩, ⟨_, h1, h1⟩, fun ⟨_, hR, hRφ⟩ => hRφ hR,
    fun ⟨_, _, _, _, ⟨_, hR, hRφ⟩⟩ => hRφ hR⟩

/-! ## Transition-system definitions -/

theorem reach_examples : Reach tsTwoStep true ∧ ¬ Reach tsBoolHalt true :=
  ⟨tsTwoStep_reach_true, fun h => Bool.noConfusion ((tsBoolHalt_reach_iff true).1 h)⟩

theorem star_examples : Star tsTwoStep.step false true ∧ ¬ Star tsBoolHalt.step false true := by
  refine ⟨.tail (.refl _) ⟨rfl, rfl⟩, fun h => ?_⟩
  have key : ∀ a b, Star tsBoolHalt.step a b → a = b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | tail _ hbc _ => exact hbc.elim
  exact Bool.noConfusion (key _ _ h)

theorem simInit_examples :
    SimInit tsTwoStep tsTwoStep (fun c a => c = a) ∧ ¬ SimInit tsHalt tsHalt (fun _ _ => False) :=
  ⟨fun c hc => ⟨c, hc, rfl⟩, fun h => (h () trivial).elim fun _ h => h.2⟩

theorem simStepStar_examples :
    SimStepStar tsLoop tsHalt (fun _ _ => True) ∧
    ¬ SimStepStar tsTwoStep tsHalt (fun c _ => c = false) := by
  refine ⟨fun _ _ a _ _ => ⟨a, .refl a, trivial⟩, fun h => ?_⟩
  obtain ⟨_, _, hS⟩ := h false true () ⟨rfl, rfl⟩ rfl
  exact Bool.noConfusion hS

theorem simStepLock_examples :
    SimStepLock tsTwoStep tsTwoStep (fun c a => c = a) ∧
    ¬ SimStepLock tsLoop tsHalt (fun _ _ => True) :=
  ⟨lockstep_nonvacuous.2.1, fun h => (h () () () trivial trivial).elim fun _ h => h.1⟩

theorem simStepStutter_examples :
    SimStepStutter tsLoop tsHalt (fun _ _ => True) ∧
    ¬ SimStepStutter tsTwoStep tsBoolHalt (fun c a => c = a) := by
  refine ⟨stuttering_simulation_does_not_transfer_termination.2.1, fun h => ?_⟩
  rcases h false true false ⟨rfl, rfl⟩ rfl with ⟨_, h, _⟩ | h
  · exact h
  · exact Bool.noConfusion h

theorem simStepWF_examples :
    SimStepWF tsTwoStep tsBoolHalt (fun _ a => a = false) (· < ·)
      (fun (c : Bool) (_ : Bool) => if c then 0 else 1) ∧
    ¬ SimStepWF tsLoop tsHalt (fun _ _ => True) (fun (x y : Nat) => x < y) (fun _ _ => 0) := by
  refine ⟨wf_simulation_nonvacuous.2.1, fun h => ?_⟩
  rcases h () () () trivial trivial with ⟨_, h, _⟩ | ⟨_, h⟩
  · exact h
  · exact Nat.lt_irrefl 0 h

theorem terminates_examples : Terminates tsHalt () ∧ ¬ Terminates tsLoop () :=
  ⟨tsHalt_allRunsFinite () (.init trivial), tsLoop_not_terminates⟩

theorem allRunsFinite_examples : AllRunsFinite tsTwoStep ∧ ¬ AllRunsFinite tsLoop :=
  ⟨tsTwoStep_allRunsFinite, fun h => tsLoop_not_terminates (h () tsLoop_reach)⟩

theorem weaklyTerminates_examples : WeaklyTerminates tsHalt () ∧ ¬ WeaklyTerminates tsLoop () :=
  ⟨⟨(), .refl (), fun _ h => h⟩, fun ⟨_, _, h⟩ => h () trivial⟩

/-- An instance of `strong_pullback_of_functional_simulation`: `S _ a := a = false` from
`tsTwoStep` to `tsBoolHalt` is a functional forward simulation. -/
theorem functional_simulation_example :
    SimInit tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    SimStepStar tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    (∀ (c : Bool) (a a' : Bool), (fun (_ a : Bool) => a = false) c a →
      (fun (_ a : Bool) => a = false) c a' → a = a') ∧
    (∀ a, Reach tsBoolHalt a → a = false) :=
  ⟨forward_simulation_nonvacuous.1, forward_simulation_nonvacuous.2.1,
    fun _ _ _ ha ha' => ha.trans ha'.symm, forward_simulation_nonvacuous.2.2.1⟩

/-- In the universal-pullback countermodel, restricting the total relation to reachable
abstract states repairs the universal pullback (`reach_restricted_simulation_gives_strong_pullback`). -/
theorem reach_restriction_repairs_strong_pullback_countermodel :
    ∀ a, ((fun (_ : Unit) (_ : Bool) => True) () a ∧ Reach tsBoolHalt a) → a = false :=
  (reach_restricted_simulation_gives_strong_pullback
    strong_pullback_fails_with_unreachable_related_state.1
    strong_pullback_fails_with_unreachable_related_state.2.1).2.2 (fun a => a = false)
    strong_pullback_fails_with_unreachable_related_state.2.2.1 () (.init trivial)

/-! ## Non-vacuity of the licensed cells of the transfer matrix -/

/-- Every licensed cell of the matrix has an instance: a formula of the class, a map of
the kind, and the premise of the transfer (source side for `fwd`, target side for
`bwd`) true. Cells in order: `qf/emb/fwd`, `qf/emb/bwd`, `univ/emb/bwd`,
`exist/emb/fwd`, `posExist/hom/fwd`, `posExist/strong/fwd`, `posExist/emb/fwd`,
`posExist/surj/fwd`, `pos/surj/fwd`. -/
theorem licensed_cells_nonvacuous :
    (Cls.Mem .qf notP0 ∧ MapKind.Holds .emb inclNP ∧ Sat S1N.toStr notP0 (env1 0)) ∧
    (Cls.Mem .qf notP0 ∧ MapKind.Holds .emb inclNP ∧ Sat S2NP.toStr notP0 (inclNP ∘ env1 0)) ∧
    (Cls.Mem .univ allNotRxx ∧ MapKind.Holds .emb inclCyc ∧
      Sat S2Cyc.toStr allNotRxx (inclCyc ∘ Fin.elim0)) ∧
    (Cls.Mem .exist exP ∧ MapKind.Holds .emb inclPN ∧ Sat S1P.toStr exP Fin.elim0) ∧
    (Cls.Mem .posExist exP ∧ MapKind.Holds .hom squashP ∧ Sat S2NP.toStr exP Fin.elim0) ∧
    (Cls.Mem .posExist exSelfEq ∧ MapKind.Holds .strong collapse ∧
      Sat S2E.toStr exSelfEq Fin.elim0) ∧
    (Cls.Mem .posExist exP ∧ MapKind.Holds .emb inclPN ∧ Sat S1P.toStr exP Fin.elim0) ∧
    (Cls.Mem .posExist exP ∧ MapKind.Holds .surj squashP ∧ Sat S2NP.toStr exP Fin.elim0) ∧
    (Cls.Mem .pos allExP ∧ MapKind.Holds .surj squashP ∧ Sat S2NP.toStr allExP Fin.elim0) := by
  decide

end Toy.Transfer
