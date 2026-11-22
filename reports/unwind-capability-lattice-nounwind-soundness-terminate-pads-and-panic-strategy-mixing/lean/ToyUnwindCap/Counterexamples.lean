import ToyUnwindCap.Examples

/-!
# Hypothesis counterexamples, non-vacuity witnesses and positive controls

Each `*_fails_without_*` theorem states, in canonical form, that a concrete instance satisfies
every other hypothesis of the named result and that the result's conclusion fails for it.
Each `*_hypotheses_hold_*` theorem states that a concrete instance satisfies every hypothesis.
All theorems here are fully proved.
-/

namespace Toy.UnwindCap

/-! ## `noUB_of_enforced_of_foreignCovered_of_siteAgreement` -/

theorem noUB_hypotheses_hold_progUnwindCatch :
    Enforced stdCanUnwind progUnwindCatch ∧ ForeignCovered stdCanUnwind progUnwindCatch ∧
    SiteAgreement stdCanUnwind progUnwindCatch ∧
    Exec stdCanUnwind progUnwindCatch 0 [.drop 1 7, .caught 0] .ret :=
  ⟨enforced_of_enforcedB _ _ (by decide), foreignCovered_of_foreignCoveredB _ _ (by decide),
    siteAgreement_of_siteAgreementB _ _ (by decide), exec_progUnwindCatch⟩

theorem noUB_hypotheses_hold_progAbortImportPadded :
    Enforced stdCanUnwind progAbortImportPadded ∧
    ForeignCovered stdCanUnwind progAbortImportPadded ∧
    SiteAgreement stdCanUnwind progAbortImportPadded ∧
    Exec stdCanUnwind progAbortImportPadded 0 [] .abort :=
  ⟨enforced_progAbortImportPadded, foreignCovered_progAbortImportPadded,
    siteAgreement_of_siteAgreementB _ _ (by decide), exec_progAbortImportPadded_abort⟩

theorem noUB_fails_without_enforced :
    ForeignCovered stdCanUnwind progPlainCallFromNounwind ∧
    SiteAgreement stdCanUnwind progPlainCallFromNounwind ∧
    Exec stdCanUnwind progPlainCallFromNounwind 0 [] .ub :=
  ⟨foreignCovered_of_foreignCoveredB _ _ (by decide),
    siteAgreement_of_siteAgreementB _ _ (by decide), ⟨3, by decide⟩⟩

theorem noUB_fails_without_foreignCovered :
    Enforced stdCanUnwind progThrowingC ∧ SiteAgreement stdCanUnwind progThrowingC ∧
    Exec stdCanUnwind progThrowingC 0 [] .ub :=
  ⟨enforced_of_enforcedB _ _ (by decide), siteAgreement_of_siteAgreementB _ _ (by decide),
    ⟨1, by decide⟩⟩

theorem noUB_fails_without_siteAgreement :
    Enforced stdCanUnwind progAbortCallsUnwind ∧
    ForeignCovered stdCanUnwind progAbortCallsUnwind ∧
    Exec stdCanUnwind progAbortCallsUnwind 0 [] .ub :=
  ⟨enforced_of_enforcedB _ _ (by decide), foreignCovered_of_foreignCoveredB _ _ (by decide),
    ⟨3, by decide⟩⟩

/-! ## `foreignCovered_std_of_foreignHonest_of_foreignNotGlue` -/

theorem foreignCovered_std_hypotheses_hold_progAbortImportPadded :
    ForeignHonest progAbortImportPadded ∧ ForeignNotGlue progAbortImportPadded :=
  ⟨foreignHonest_progAbortImportPadded, foreignNotGlue_progAbortImportPadded⟩

theorem foreignCovered_std_fails_without_foreignHonest :
    ForeignNotGlue progThrowingC ∧ ¬ ForeignCovered stdCanUnwind progThrowingC :=
  ⟨foreignNotGlue_of_foreignNotGlueB _ (by decide), not_foreignCovered_progThrowingC⟩

theorem foreignCovered_std_fails_without_foreignNotGlue :
    ForeignHonest progForeignGlue ∧ ¬ ForeignCovered stdCanUnwind progForeignGlue := by
  refine ⟨foreignHonest_of_foreignHonestB _ (by decide), fun h => ?_⟩
  exact absurd (h 0 (by decide) (by decide)) (by decide)

/-! ## `precForeignSound_iff` -/

/-- Both sides of `precForeignSound_iff` hold for `stdCanUnwind` and fail for
`abortAllCanUnwind`. -/
theorem precForeignSound_iff_instances :
    (∀ c i, i.foreign = true → i.abi = .cUnwind → i.neverUnwind = false → i.dropGlue = false →
        stdCanUnwind c i = true) ∧
    ¬ (∀ c i, i.foreign = true → i.abi = .cUnwind → i.neverUnwind = false →
        i.dropGlue = false → abortAllCanUnwind c i = true) := by
  refine ⟨stdCanUnwind_foreign_cUnwind, fun h => ?_⟩
  exact absurd (h abortCfg foreignCUnwind rfl rfl rfl rfl) (by decide)

/-! ## Rule order: the mistaken order on a program satisfying every other hypothesis -/

/-- Under `abortAllCanUnwind`, `progAbortImportPlain` satisfies `LinkOK`, `Enforced`,
`SiteAgreement`, `ForeignHonest` and `ForeignNotGlue`, and its function 0 has a run with
outcome `ub`. -/
theorem abortAll_progAbortImportPlain_ub :
    LinkOK progAbortImportPlain ∧ Enforced abortAllCanUnwind progAbortImportPlain ∧
    SiteAgreement abortAllCanUnwind progAbortImportPlain ∧ ForeignHonest progAbortImportPlain ∧
    ForeignNotGlue progAbortImportPlain ∧ Exec abortAllCanUnwind progAbortImportPlain 0 [] .ub :=
  ⟨linkOK_of_notPotentiallyUnwindingB _ (by decide), enforced_of_enforcedB _ _ (by decide),
    siteAgreement_of_siteAgreementB _ _ (by decide), foreignHonest_of_foreignHonestB _ (by decide),
    foreignNotGlue_of_foreignNotGlueB _ (by decide), ⟨2, by decide⟩⟩

/-- Positive control: under `stdCanUnwind`, the toy codegen turns `progAbortImportPlain` into
`progAbortImportPadded`, which has no run with outcome `ub`. -/
theorem std_progAbortImportPlain_padded_noUB :
    insertPads stdCanUnwind progAbortImportPlain = progAbortImportPadded ∧
    ∀ t o, Exec stdCanUnwind progAbortImportPadded 0 t o → o ≠ .ub :=
  ⟨insertPads_progAbortImportPlain, fun t o h =>
    noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
      noUB_hypotheses_hold_progAbortImportPadded.1
      noUB_hypotheses_hold_progAbortImportPadded.2.1
      noUB_hypotheses_hold_progAbortImportPadded.2.2.1 0 t o h⟩

/-! ## `noUB_insertPads_of_foreignCovered_of_siteAgreement` -/

theorem noUB_insertPads_hypotheses_hold_progAbortImportPlain :
    ForeignCovered stdCanUnwind progAbortImportPlain ∧
    SiteAgreement stdCanUnwind progAbortImportPlain :=
  ⟨foreignCovered_of_foreignCoveredB _ _ (by decide),
    siteAgreement_of_siteAgreementB _ _ (by decide)⟩

theorem noUB_insertPads_fails_without_foreignCovered :
    SiteAgreement stdCanUnwind progThrowingC ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progThrowingC) 0 [] .ub := by
  have h : insertPads stdCanUnwind progThrowingC = progThrowingC := by decide
  rw [h]
  exact ⟨siteAgreement_of_siteAgreementB _ _ (by decide), ⟨1, by decide⟩⟩

theorem noUB_insertPads_fails_without_siteAgreement :
    ForeignCovered stdCanUnwind progAbortCallsUnwind ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progAbortCallsUnwind) 0 [] .ub := by
  rw [insertPads_progAbortCallsUnwind]
  exact ⟨foreignCovered_of_foreignCoveredB _ _ (by decide), ⟨3, by decide⟩⟩

/-! ## `ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds` -/

theorem ub_of_unguarded_call_hypotheses_hold_progPlainCallFromNounwind :
    (progPlainCallFromNounwind.fn 0).info.foreign = false ∧
    progPlainCallFromNounwind.selfMay stdCanUnwind 0 = false ∧
    (progPlainCallFromNounwind.fn 0).body = [.call 1 .none] ∧ Action.none.Stops = false ∧
    Exec stdCanUnwind progPlainCallFromNounwind 1 [] .unwind :=
  ⟨by decide, by decide, by decide, rfl, ⟨1, by decide⟩⟩

/-- Without `hgself`: function 1 of `progUnwindCatch` (classified as possibly unwinding) starts
with a cleanup call to function 2, which unwinds; function 1 has no run with outcome `ub`. -/
theorem ub_of_unguarded_call_fails_without_selfNonUnwinding :
    (progUnwindCatch.fn 1).info.foreign = false ∧
    (progUnwindCatch.fn 1).body = [.call 2 (.cleanup [7])] ∧ (Action.cleanup [7]).Stops = false ∧
    Exec stdCanUnwind progUnwindCatch 2 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progUnwindCatch 1 t' .ub := by
  refine ⟨by decide, by decide, rfl, ⟨1, by decide⟩, fun ⟨t', h⟩ => ?_⟩
  exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
    noUB_hypotheses_hold_progUnwindCatch.1 noUB_hypotheses_hold_progUnwindCatch.2.1
    noUB_hypotheses_hold_progUnwindCatch.2.2.1 1 t' _ h rfl

/-- `progPlainCallFromNounwind` with a terminate pad instead of the plain call. -/
def progTerminateFromNounwind : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .terminate], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩

/-- Without `hact`: the same caller with a terminate pad has no run with outcome `ub`. -/
theorem ub_of_unguarded_call_fails_without_nonStopping :
    (progTerminateFromNounwind.fn 0).info.foreign = false ∧
    progTerminateFromNounwind.selfMay stdCanUnwind 0 = false ∧
    (progTerminateFromNounwind.fn 0).body = [.call 1 .terminate] ∧
    Exec stdCanUnwind progTerminateFromNounwind 1 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progTerminateFromNounwind 0 t' .ub := by
  refine ⟨by decide, by decide, by decide, ⟨1, by decide⟩, fun ⟨t', h⟩ => ?_⟩
  exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
    (enforced_of_enforcedB _ _ (by decide)) (foreignCovered_of_foreignCoveredB _ _ (by decide))
    (siteAgreement_of_siteAgreementB _ _ (by decide)) 0 t' _ h rfl

/-- A non-unwinding caller whose callee is also classified as non-unwinding and never panics. -/
def progNounwindCallee : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .none], false⟩, ⟨cFn, 0, [], false⟩], .unwind⟩

/-- Without `hf`: a plain call from a non-unwinding function to a callee with no unwinding run
causes no `ub`. -/
theorem ub_of_unguarded_call_fails_without_calleeUnwinds :
    (progNounwindCallee.fn 0).info.foreign = false ∧
    progNounwindCallee.selfMay stdCanUnwind 0 = false ∧
    (progNounwindCallee.fn 0).body = [.call 1 .none] ∧ Action.none.Stops = false ∧
    ¬ ∃ t', Exec stdCanUnwind progNounwindCallee 0 t' .ub := by
  refine ⟨by decide, by decide, by decide, rfl, fun ⟨t', h⟩ => ?_⟩
  exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
    (enforced_of_enforcedB _ _ (by decide)) (foreignCovered_of_foreignCoveredB _ _ (by decide))
    (siteAgreement_of_siteAgreementB _ _ (by decide)) 0 t' _ h rfl

/-- A foreign `"C"` import whose (ignored) body field starts with a plain call. -/
def progForeignWithBody : Prog :=
  ⟨[unwindCfg], [⟨foreignC, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩

/-- Without `hg`: for a foreign function the body field is not executed. -/
theorem ub_of_unguarded_call_fails_without_nonForeign :
    progForeignWithBody.selfMay stdCanUnwind 0 = false ∧
    (progForeignWithBody.fn 0).body = [.call 1 .none] ∧ Action.none.Stops = false ∧
    Exec stdCanUnwind progForeignWithBody 1 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progForeignWithBody 0 t' .ub := by
  refine ⟨by decide, by decide, rfl, ⟨1, by decide⟩, fun ⟨t', h⟩ => ?_⟩
  exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
    (enforced_of_enforcedB _ _ (by decide)) (foreignCovered_of_foreignCoveredB _ _ (by decide))
    (siteAgreement_of_siteAgreementB _ _ (by decide)) 0 t' _ h rfl

/-- A non-unwinding caller whose unguarded call follows a panic point with a terminate pad. -/
def progUnreachableCall : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.raise .terminate, .call 1 .none], false⟩,
    ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩

/-- Without `hbody` (the call is in the body but not first): the call is never reached and
there is no run with outcome `ub`. -/
theorem ub_of_unguarded_call_fails_without_callFirst :
    (progUnreachableCall.fn 0).info.foreign = false ∧
    progUnreachableCall.selfMay stdCanUnwind 0 = false ∧
    Stmt.call 1 .none ∈ (progUnreachableCall.fn 0).body ∧ Action.none.Stops = false ∧
    Exec stdCanUnwind progUnreachableCall 1 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progUnreachableCall 0 t' .ub := by
  refine ⟨by decide, by decide, by decide, rfl, ⟨1, by decide⟩, fun ⟨t', n, h⟩ => ?_⟩
  cases n with
  | zero => simp [runFn] at h
  | succ n =>
    have hf : progUnreachableCall.fn 0 = ⟨cFn, 0, [.raise .terminate, .call 1 .none], false⟩ :=
      rfl
    have hh : progUnreachableCall.handler = .unwind := rfl
    simp [runFn, hf, hh, execBody, onUnwind, boundary, cFn] at h

/-! ## `noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement` -/

/-- `progMixedLinkOK` satisfies every hypothesis of the mixed-strategy theorem, violates
`SiteAgreement stdCanUnwind` (its `abort` crate classifies function 3 as non-unwinding, function
3's `unwind` crate does not), and its function 1 has a run that aborts. -/
theorem noUB_std_of_linkOK_hypotheses_hold_progMixedLinkOK :
    LinkOK progMixedLinkOK ∧ Enforced stdCanUnwind progMixedLinkOK ∧
    ForeignHonest progMixedLinkOK ∧ ForeignNotGlue progMixedLinkOK ∧
    (PotentiallyUnwinding progMixedLinkOK → GlueAgreement progMixedLinkOK) ∧
    ¬ SiteAgreement stdCanUnwind progMixedLinkOK ∧
    Exec stdCanUnwind progMixedLinkOK 1 [] .abort := by
  refine ⟨linkOK_progMixedLinkOK, enforced_of_enforcedB _ _ (by decide),
    foreignHonest_of_foreignHonestB _ (by decide), foreignNotGlue_of_foreignNotGlueB _ (by decide),
    fun _ => glueAgreement_of_glueAgreementB _ (by decide), fun h => ?_, ⟨3, by decide⟩⟩
  exact absurd (h 0 3 .none (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem noUB_std_of_linkOK_hypotheses_hold_progUnwindCatch :
    LinkOK progUnwindCatch ∧ Enforced stdCanUnwind progUnwindCatch ∧
    ForeignHonest progUnwindCatch ∧ ForeignNotGlue progUnwindCatch ∧
    (PotentiallyUnwinding progUnwindCatch → GlueAgreement progUnwindCatch) :=
  ⟨linkOK_of_allUnwindB _ (by decide), enforced_of_enforcedB _ _ (by decide),
    foreignHonest_of_foreignHonestB _ (by decide), foreignNotGlue_of_foreignNotGlueB _ (by decide),
    fun _ => glueAgreement_of_glueAgreementB _ (by decide)⟩

/-- A crate with both the panic strategy and the panic-in-drop setting `abort`. -/
def abortBothCfg : CrateCfg := ⟨.abort, .abort⟩

/-- Mixed strategies with drop glue: crate 0 (`abortBothCfg`) holds function 0 (Rust), which calls
function 1, a drop-glue instance compiled in crate 1 (`unwindCfg`) that panics, with a plain call.
Panic handler `abort`. -/
def progMixedAbortBothCallsGlue : Prog :=
  ⟨[abortBothCfg, unwindCfg],
    [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨glueInfo, 1, [.raise .none], false⟩], .abort⟩

/-- `progMixedAbortBothCallsGlue` satisfies every hypothesis of the mixed-strategy theorem (it is
not potentially unwinding, so the drop-glue hypothesis holds vacuously) although
`GlueAgreement` itself fails for it. -/
theorem noUB_std_hypotheses_hold_progMixedAbortBothCallsGlue :
    LinkOK progMixedAbortBothCallsGlue ∧ Enforced stdCanUnwind progMixedAbortBothCallsGlue ∧
    ForeignHonest progMixedAbortBothCallsGlue ∧ ForeignNotGlue progMixedAbortBothCallsGlue ∧
    (PotentiallyUnwinding progMixedAbortBothCallsGlue →
      GlueAgreement progMixedAbortBothCallsGlue) ∧
    ¬ GlueAgreement progMixedAbortBothCallsGlue ∧
    Exec stdCanUnwind progMixedAbortBothCallsGlue 0 [] .abort := by
  refine ⟨linkOK_of_notPotentiallyUnwindingB _ (by decide), enforced_of_enforcedB _ _ (by decide),
    foreignHonest_of_foreignHonestB _ (by decide), foreignNotGlue_of_foreignNotGlueB _ (by decide),
    fun h => absurd h (not_potentiallyUnwinding_of_B _ (by decide)), fun h => ?_, ⟨3, by decide⟩⟩
  exact absurd (h 0 1 .none (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide)

/-- `progAbortHandlerRaisePlain` (a panic point without a landing pad under the `abort` handler)
satisfies every hypothesis of the mixed-strategy theorem; its function 0 aborts. -/
theorem noUB_std_hypotheses_hold_progAbortHandlerRaisePlain :
    LinkOK progAbortHandlerRaisePlain ∧ Enforced stdCanUnwind progAbortHandlerRaisePlain ∧
    ForeignHonest progAbortHandlerRaisePlain ∧ ForeignNotGlue progAbortHandlerRaisePlain ∧
    (PotentiallyUnwinding progAbortHandlerRaisePlain →
      GlueAgreement progAbortHandlerRaisePlain) ∧
    Exec stdCanUnwind progAbortHandlerRaisePlain 0 [] .abort :=
  ⟨linkOK_of_notPotentiallyUnwindingB _ (by decide), enforced_handler_examples.1,
    foreignHonest_of_foreignHonestB _ (by decide), foreignNotGlue_of_foreignNotGlueB _ (by decide),
    fun _ => glueAgreement_of_glueAgreementB _ (by decide), ⟨1, by decide⟩⟩

theorem noUB_std_fails_without_linkOK :
    Enforced stdCanUnwind progAbortCallsUnwind ∧ ForeignHonest progAbortCallsUnwind ∧
    ForeignNotGlue progAbortCallsUnwind ∧
    (PotentiallyUnwinding progAbortCallsUnwind → GlueAgreement progAbortCallsUnwind) ∧
    Exec stdCanUnwind progAbortCallsUnwind 0 [] .ub :=
  ⟨enforced_of_enforcedB _ _ (by decide), foreignHonest_of_foreignHonestB _ (by decide),
    foreignNotGlue_of_foreignNotGlueB _ (by decide),
    fun _ => glueAgreement_of_glueAgreementB _ (by decide),
    ⟨3, by decide⟩⟩

theorem noUB_std_fails_without_enforced :
    LinkOK progPlainCallFromNounwind ∧ ForeignHonest progPlainCallFromNounwind ∧
    ForeignNotGlue progPlainCallFromNounwind ∧
    (PotentiallyUnwinding progPlainCallFromNounwind → GlueAgreement progPlainCallFromNounwind) ∧
    Exec stdCanUnwind progPlainCallFromNounwind 0 [] .ub :=
  ⟨linkOK_of_allUnwindB _ (by decide), foreignHonest_of_foreignHonestB _ (by decide),
    foreignNotGlue_of_foreignNotGlueB _ (by decide),
    fun _ => glueAgreement_of_glueAgreementB _ (by decide),
    ⟨3, by decide⟩⟩

theorem noUB_std_fails_without_foreignHonest :
    LinkOK progThrowingC ∧ Enforced stdCanUnwind progThrowingC ∧ ForeignNotGlue progThrowingC ∧
    (PotentiallyUnwinding progThrowingC → GlueAgreement progThrowingC) ∧
    Exec stdCanUnwind progThrowingC 0 [] .ub :=
  ⟨linkOK_of_allUnwindB _ (by decide), enforced_of_enforcedB _ _ (by decide),
    foreignNotGlue_of_foreignNotGlueB _ (by decide),
    fun _ => glueAgreement_of_glueAgreementB _ (by decide),
    ⟨1, by decide⟩⟩

theorem noUB_std_fails_without_foreignNotGlue :
    LinkOK progForeignGlue ∧ Enforced stdCanUnwind progForeignGlue ∧
    ForeignHonest progForeignGlue ∧
    (PotentiallyUnwinding progForeignGlue → GlueAgreement progForeignGlue) ∧
    Exec stdCanUnwind progForeignGlue 0 [] .ub :=
  ⟨linkOK_of_allUnwindB _ (by decide), enforced_of_enforcedB _ _ (by decide),
    foreignHonest_of_foreignHonestB _ (by decide),
    fun _ => glueAgreement_of_glueAgreementB _ (by decide),
    ⟨1, by decide⟩⟩

theorem noUB_std_fails_without_glueAgreement :
    LinkOK progGlueMismatch ∧ Enforced stdCanUnwind progGlueMismatch ∧
    ForeignHonest progGlueMismatch ∧ ForeignNotGlue progGlueMismatch ∧
    Exec stdCanUnwind progGlueMismatch 0 [] .ub :=
  ⟨linkOK_of_allUnwindB _ (by decide), enforced_of_enforcedB _ _ (by decide),
    foreignHonest_of_foreignHonestB _ (by decide), foreignNotGlue_of_foreignNotGlueB _ (by decide),
    ⟨3, by decide⟩⟩

/-! ## `glueSiteSound_iff` and `glueSiteSound_iff_panicInDrop` -/

/-- Instances of both sides of `glueSiteSound_iff`: the mismatch configuration (right side false)
and a matching configuration (right side true). -/
theorem glueSiteSound_iff_instances :
    ¬ (stdCanUnwind pidAbortCfg glueInfo = false →
        stdCanUnwind unwindCfg glueInfo = false ∨ Action.none.Stops = true) ∧
    (stdCanUnwind pidAbortCfg glueInfo = false →
        stdCanUnwind pidAbortCfg glueInfo = false ∨ Action.none.Stops = true) := by
  decide

theorem glueSiteSound_iff_panicInDrop_hypotheses_hold :
    (pidAbortCfg.panic = .abort ∨ pidAbortCfg.panicInDrop = .abort) ∧
    unwindCfg.panic = .unwind ∧ pidAbortCfg.panic = .unwind := by decide

/-- Without `hview`: a caller crate with strategy and panic-in-drop `unwind` treats glue as
possibly unwinding, so the site is sound although neither right-hand disjunct holds. -/
theorem glueSiteSound_iff_panicInDrop_fails_without_view :
    unwindCfg.panic = .unwind ∧ GlueSiteSound unwindCfg unwindCfg .none ∧
    ¬ (unwindCfg.panicInDrop = .abort ∨ Action.none.Stops = true) := by
  refine ⟨rfl, (glueSiteSound_iff _ _ _).2 (fun h => absurd h (by decide)), by decide⟩

/-- Without `hcg`: a glue instance compiled in an `abort`-strategy crate is non-unwinding by
the strategy rule, so the site is sound although the glue crate's panic-in-drop is `unwind`. -/
theorem glueSiteSound_iff_panicInDrop_fails_without_glueCrateUnwind :
    (pidAbortCfg.panic = .abort ∨ pidAbortCfg.panicInDrop = .abort) ∧
    GlueSiteSound pidAbortCfg abortCfg .none ∧
    ¬ (abortCfg.panicInDrop = .abort ∨ Action.none.Stops = true) := by
  refine ⟨Or.inr rfl, (glueSiteSound_iff _ _ _).2 (fun _ => Or.inl (by decide)), by decide⟩

/-- The drop-glue family with the panic handler changed to `abort`: for all settings, actions and
glue bodies, no finite run of any function has outcome `ub` (panic points abort instead of
unwinding). -/
theorem glueProg_abort_handler_noUB (cc cg : CrateCfg) (act : Action) (body : List Stmt) :
    ∀ f t o, Exec stdCanUnwind { glueProg cc cg act body with handler := .abort } f t o →
      o ≠ .ub := by
  let q := { glueProg cc cg act body with handler := .abort }
  have hno : ∀ n f, ∀ r ∈ runFn stdCanUnwind q n f, r.2 ≠ .ub ∧ r.2 ≠ .unwind := by
    intro n
    induction n with
    | zero => intro f r hr; simp [runFn] at hr
    | succ n ih =>
      have hbody : ∀ g l, ∀ r ∈ execBody stdCanUnwind q (runFn stdCanUnwind q n) g l,
          r.2 ≠ .ub ∧ r.2 ≠ .unwind := by
        intro g l
        induction l with
        | nil =>
          intro r hr; simp [execBody] at hr; subst hr; exact ⟨by decide, by decide⟩
        | cons s rest ihl =>
          intro r hr
          cases s with
          | raise a =>
            have hh : q.handler = .abort := rfl
            simp [execBody, hh] at hr; subst hr; exact ⟨by decide, by decide⟩
          | call k a =>
            simp only [execBody, List.mem_flatMap] at hr
            obtain ⟨⟨t0, o0⟩, h0, hr⟩ := hr
            have hc := ih k _ h0
            cases o0 with
            | ret =>
              obtain ⟨r', hr', rfl⟩ := mem_prependRuns hr
              exact ihl r' hr'
            | unwind => exact absurd rfl hc.2
            | abort => simp at hr; subst hr; exact ⟨by simp, by simp⟩
            | ub => exact absurd rfl hc.1
      intro f r hr
      have hfor : (q.fn f).info.foreign = false := by
        match f with
        | 0 => rfl
        | 1 => rfl
        | _ + 2 => rfl
      unfold runFn at hr
      rw [hfor] at hr
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map] at hr
      obtain ⟨⟨t', o'⟩, hmem, rfl⟩ := hr
      have hb := hbody f (q.fn f).body _ hmem
      cases o' with
      | ret => exact ⟨by simp [boundary], by simp [boundary]⟩
      | abort => exact ⟨by simp [boundary], by simp [boundary]⟩
      | unwind => exact absurd rfl hb.2
      | ub => exact absurd rfl hb.1
  intro f t o ⟨n, hn⟩
  exact (hno n f _ hn).1

/-! ## `compRet_eq_specRet_of_conforms` -/

theorem compRet_hypotheses_hold :
    idCodec.Lawful ∧ Conforms idCodec idCodec ∧
    (∀ fr ∈ [(⟨idCodec, (· + 1)⟩ : RetFrame), ⟨idCodec, (· * 2)⟩], Conforms fr.backend idCodec) ∧
    compRet idCodec [⟨idCodec, (· + 1)⟩, ⟨idCodec, (· * 2)⟩] 3 = 8 := by
  refine ⟨fun _ => rfl, ⟨rfl, rfl⟩, ?_, rfl⟩
  intro fr hfr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfr
  rcases hfr with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem compRet_fails_without_lawful :
    Conforms truncCodec truncCodec ∧
    (∀ fr ∈ [(⟨truncCodec, id⟩ : RetFrame)], Conforms fr.backend truncCodec) ∧
    compRet truncCodec [⟨truncCodec, id⟩] 300 ≠ specRet [⟨truncCodec, id⟩] 300 := by
  refine ⟨⟨rfl, rfl⟩, ?_, by decide⟩
  intro fr hfr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfr
  subst hfr; exact ⟨rfl, rfl⟩

/-- Without `h0`: the innermost callee's backend `shiftCodec` is lawful on its own but does not
conform to the platform ABI `idCodec`. -/
theorem compRet_fails_without_calleeConforms :
    idCodec.Lawful ∧ shiftCodec.Lawful ∧
    (∀ fr ∈ [(⟨idCodec, id⟩ : RetFrame)], Conforms fr.backend idCodec) ∧
    compRet shiftCodec [⟨idCodec, id⟩] 5 ≠ specRet [⟨idCodec, id⟩] 5 := by
  refine ⟨fun _ => rfl, lawful_examples.2.1, ?_, by decide⟩
  intro fr hfr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfr
  subst hfr; exact ⟨rfl, rfl⟩

/-- Without `hfrs`: the caller's backend `shiftCodec` is lawful on its own but does not conform;
decoding uses truncated subtraction. -/
theorem compRet_fails_without_framesConform :
    idCodec.Lawful ∧ Conforms idCodec idCodec ∧ shiftCodec.Lawful ∧
    compRet idCodec [⟨shiftCodec, id⟩] 5 ≠ specRet [⟨shiftCodec, id⟩] 5 :=
  ⟨fun _ => rfl, ⟨rfl, rfl⟩, lawful_examples.2.1, by decide⟩

/-! ## `compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate` -/

/-- Three instances satisfying the hypothesis: one where both sides hold, one where both fail, and
one (a `pads = none` terminate frame after a catch frame) where both sides hold. -/
theorem compUnwind_iff_hypotheses_hold :
    NoReachedNoneTerminate [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] ∧
    compUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] =
      specUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] ∧
    NoReachedNoneTerminate [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ∧
    compUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ≠
      specUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ∧
    NoReachedNoneTerminate [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    compUnwind [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] =
      specUnwind [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] := by
  refine ⟨?_, by decide, ?_, by decide, noReachedNoneTerminate_examples.1, by decide⟩ <;>
    simp [NoReachedNoneTerminate, Action.Stops]

/-- The chain `[⟨full, catchPad⟩, ⟨none, terminate⟩]` satisfies `ObligationsFull` (so the
sufficiency theorem applies to it) and has a `pads = none` terminate frame that the unwind does
not reach. -/
theorem compUnwind_eq_specUnwind_of_obligationsFull_hypotheses_hold :
    ObligationsFull [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    ¬ (∀ fr ∈ [(⟨.full, .catchPad⟩ : UFrame), ⟨.none, .terminate⟩],
      fr.pads = .none → fr.act ≠ .terminate) := by
  refine ⟨by simp [ObligationsFull, Action.obligation, Action.Stops], fun h => ?_⟩
  exact h ⟨.none, .terminate⟩ (by simp) rfl rfl

/-- Without `hterm`: a `pads = none` terminate frame followed by a `pads = full` terminate frame
gives equal compiled and specified unwinds, although `ObligationsFull` fails. -/
theorem compUnwind_iff_fails_without_noReachedNoneTerminate :
    compUnwind [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] =
      specUnwind [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] ∧
    ¬ ObligationsFull [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] := by
  refine ⟨by decide, ?_⟩
  simp [ObligationsFull, Action.obligation]

/-- Without `h : ObligationsFull c` (in `compUnwind_eq_specUnwind_of_obligationsFull`): for the chain
`[⟨none, cleanup [1]⟩, ⟨full, catchPad⟩]` the compiled and specified unwinds differ. -/
theorem compUnwind_of_obligationsFull_fails_without_obligationsFull :
    ¬ ObligationsFull [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ∧
    compUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ≠
      specUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] :=
  ⟨obligationsFull_examples.2, by decide⟩

/-! ## `robust_iff_shielded` and `robust_of_terminateShielded` -/

/-- A chain that is `Shielded` by a catch pad but not `TerminateShielded`: abort shielding is
sufficient, not necessary, for robust agreement. -/
theorem shielded_not_terminateShielded :
    Shielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] ∧
    ¬ TerminateShielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] ∧
    ∀ c', SameShape [⟨.full, .catchPad⟩, ⟨.none, .none⟩] c' → compUnwind c' = specUnwind c' :=
  ⟨shielded_examples.1, shielded_examples.2.2.2,
    (robust_iff_shielded _).2 shielded_examples.1⟩

theorem robust_of_terminateShielded_hypotheses_hold :
    TerminateShielded [⟨.full, .none⟩, ⟨.full, .terminate⟩, ⟨.none, .none⟩] :=
  shielded_examples.2.2.1

/-- Without `TerminateShielded`: for the chain `[⟨none, cleanup [1]⟩]` the compiled and
specified unwinds differ on the chain itself. -/
theorem robust_fails_without_terminateShielded :
    SameShape [⟨.none, .cleanup [1]⟩] [⟨.none, .cleanup [1]⟩] ∧
    compUnwind [⟨.none, .cleanup [1]⟩] ≠ specUnwind [⟨.none, .cleanup [1]⟩] :=
  ⟨sameShape_refl _, by decide⟩

/-! ## `withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt` -/

/-- Function 0 (a Rust-defined `extern "C"` function, non-unwinding, compiled with
`pads = none`) calls function 1 (also `extern "C"`), which calls function 2 (Rust, which
panics) through a terminate pad; function 1 is compiled with `pads = full`. -/
def progPadsNonvac : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 (.cleanup [3])], false⟩, ⟨cFn, 0, [.call 2 .terminate], false⟩,
    ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩

theorem withPads_hypotheses_hold_progPadsNonvac :
    (∀ g, g < progPadsNonvac.fns.length → padsNoneAt0 g = .none →
      (progPadsNonvac.fn g).info.foreign = false → progPadsNonvac.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsNonvac.withPads padsNoneAt0) g) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsNonvac.withPads padsNoneAt0) g) ∧
    Exec stdCanUnwind (progPadsNonvac.withPads padsNoneAt0) 0 [] .abort ∧
    Exec stdCanUnwind progPadsNonvac 0 [] .abort := by
  refine ⟨fun g _ hp _ => ?_, fun g _ => enforced_of_enforcedB _ _ (by decide) g,
    fun g _ => siteAgreement_of_siteAgreementB _ _ (by decide) g, ⟨4, by decide⟩,
    ⟨4, by decide⟩⟩
  cases g with
  | zero => decide
  | succ g => simp [padsNoneAt0] at hp

/-- Function 0 (`extern "C"`, non-unwinding, `pads = none`) calls function 1 (`extern "C"`,
`pads = full`) with a cleanup pad; function 1 contains a panic point without a landing pad
(violating `Enforced` at a `pads = full` function); function 2 (crate 1, `abort` strategy,
`pads = full`) calls function 3 (crate 0, Rust, which panics) with a plain call (violating
`SiteAgreement` at a `pads = full` function). Panic handler `unwind`. -/
def progPadsFullUnenforced : Prog :=
  ⟨[unwindCfg, abortCfg],
    [⟨cFn, 0, [.call 1 (.cleanup [3])], false⟩, ⟨cFn, 0, [.raise .none], false⟩,
     ⟨rustInfo, 1, [.call 3 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩

/-- `progPadsFullUnenforced` satisfies every hypothesis of the program-level theorem although the
compiled program violates `Enforced` and `SiteAgreement` (at `pads = full` functions). -/
theorem withPads_hypotheses_hold_progPadsFullUnenforced :
    (∀ g, g < progPadsFullUnenforced.fns.length → padsNoneAt0 g = .none →
      (progPadsFullUnenforced.fn g).info.foreign = false →
        progPadsFullUnenforced.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) g) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) g) ∧
    ¬ Enforced stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) ∧
    ¬ SiteAgreement stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) := by
  refine ⟨fun g _ hp _ => ?_, fun g hp => ?_, fun g hp => ?_, fun h => ?_, fun h => ?_⟩
  · cases g with
    | zero => decide
    | succ g => simp [padsNoneAt0] at hp
  · cases g with
    | zero => exact enforcedAt_of_enforcedAtB _ _ _ (by decide)
    | succ g => simp [padsNoneAt0] at hp
  · cases g with
    | zero => exact siteAgreementAt_of_siteAgreementAtB _ _ _ (by decide)
    | succ g => simp [padsNoneAt0] at hp
  · exact absurd ((h 1 (by decide) (by decide)).1 rfl .none (by decide)) (by decide)
  · exact absurd (h 2 3 .none (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- Function 0 (Rust, possibly unwinding, compiled with `pads = none`) calls function 1 (Rust,
which panics) with a cleanup pad dropping local 0. -/
def progPadsMayUnwind : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.call 1 (.cleanup [0])], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩

/-- In the compiled program, function 0 of `progPadsMayUnwind` has no run that drops local 0. -/
theorem not_exec_progPadsMayUnwind_withPads :
    ¬ Exec stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) 0 [.drop 0 0] .unwind := by
  rintro ⟨n, h⟩
  have hf0 : (progPadsMayUnwind.withPads padsNoneAt0).fn 0 =
      ⟨rustInfo, 0, [.call 1 .none], false⟩ := by decide
  have hf1 : (progPadsMayUnwind.withPads padsNoneAt0).fn 1 =
      ⟨rustInfo, 0, [.raise .none], false⟩ := by decide
  have hh : (progPadsMayUnwind.withPads padsNoneAt0).handler = .unwind := rfl
  match n with
  | 0 => simp [runFn] at h
  | 1 => simp [runFn, hf0, execBody, rustInfo] at h
  | n + 2 =>
    have hs0 : (progPadsMayUnwind.withPads padsNoneAt0).selfMay stdCanUnwind 0 = true := by decide
    have hs1 : (progPadsMayUnwind.withPads padsNoneAt0).selfMay stdCanUnwind 1 = true := by decide
    have hv : (progPadsMayUnwind.withPads padsNoneAt0).viewMay stdCanUnwind 0 1 = true := by decide
    simp [runFn, hf0, hf1, hh, hs0, hs1, hv, execBody, onUnwind, boundary, prependRuns,
      rustInfo] at h

/-- Without `hnone`: dropping the cleanup pad of a possibly-unwinding `pads = none` function
loses its destructor event. -/
theorem withPads_fails_without_padsNoneNonUnwinding :
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) g) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) g) ∧
    Exec stdCanUnwind progPadsMayUnwind 0 [.drop 0 0] .unwind ∧
    ¬ Exec stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) 0 [.drop 0 0] .unwind :=
  ⟨fun g _ => enforced_of_enforcedB _ _ (by decide) g,
    fun g _ => siteAgreement_of_siteAgreementB _ _ (by decide) g, ⟨3, by decide⟩,
    not_exec_progPadsMayUnwind_withPads⟩

/-- Function 0 (a Rust-defined `extern "C"` function, non-unwinding, compiled with
`pads = none`) calls function 1 (Rust, which panics) through a terminate pad. -/
def progPadsTerminate : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .terminate], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩

/-- Without `henf` on the compiled program (here it holds on the source program, even in the
program-wide form `Enforced`): the terminate pad is lost and the compiled program has a run with
outcome `ub` that the source program lacks. -/
theorem withPads_fails_without_enforcedCompiled :
    (∀ g, g < progPadsTerminate.fns.length → padsNoneAt0 g = .none →
      (progPadsTerminate.fn g).info.foreign = false →
        progPadsTerminate.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsTerminate.withPads padsNoneAt0) g) ∧
    Enforced stdCanUnwind progPadsTerminate ∧
    Exec stdCanUnwind (progPadsTerminate.withPads padsNoneAt0) 0 [] .ub ∧
    ¬ Exec stdCanUnwind progPadsTerminate 0 [] .ub := by
  refine ⟨fun g _ hp _ => ?_, fun g _ => siteAgreement_of_siteAgreementB _ _ (by decide) g,
    enforced_of_enforcedB _ _ (by decide), ⟨3, by decide⟩, fun h => ?_⟩
  · cases g with
    | zero => decide
    | succ g => simp [padsNoneAt0] at hp
  · exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
      (enforced_of_enforcedB _ _ (by decide)) (foreignCovered_of_foreignCoveredB _ _ (by decide))
      (siteAgreement_of_siteAgreementB _ _ (by decide)) 0 [] _ h rfl

/-- Crate 0 uses `abort`, crate 1 uses `unwind`. Function 0 (crate 0, Rust, non-unwinding,
compiled with `pads = none`) calls function 1 (crate 1, Rust, which panics) through a terminate
pad. -/
def progPadsAgree : Prog :=
  ⟨[abortCfg, unwindCfg], [⟨rustInfo, 0, [.call 1 .terminate], false⟩,
    ⟨rustInfo, 1, [.raise .none], false⟩], .unwind⟩

/-- Without `hsa` on the compiled program (here it holds on the source program, even in the
program-wide form `SiteAgreement`): removing the terminate pad exposes a call site whose caller's
crate classifies the callee as non-unwinding. -/
theorem withPads_fails_without_siteAgreementCompiled :
    (∀ g, g < progPadsAgree.fns.length → padsNoneAt0 g = .none →
      (progPadsAgree.fn g).info.foreign = false → progPadsAgree.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsAgree.withPads padsNoneAt0) g) ∧
    SiteAgreement stdCanUnwind progPadsAgree ∧
    Exec stdCanUnwind (progPadsAgree.withPads padsNoneAt0) 0 [] .ub ∧
    ¬ Exec stdCanUnwind progPadsAgree 0 [] .ub := by
  refine ⟨fun g _ hp _ => ?_, fun g _ => enforced_of_enforcedB _ _ (by decide) g,
    siteAgreement_of_siteAgreementB _ _ (by decide), ⟨3, by decide⟩, fun h => ?_⟩
  · cases g with
    | zero => decide
    | succ g => simp [padsNoneAt0] at hp
  · exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
      (enforced_of_enforcedB _ _ (by decide)) (foreignCovered_of_foreignCoveredB _ _ (by decide))
      (siteAgreement_of_siteAgreementB _ _ (by decide)) 0 [] _ h rfl

/-! ## `withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding` -/

/-- `progPadsNonvac` satisfies both hypotheses of the local theorem. -/
theorem withPads_local_hypotheses_hold_progPadsNonvac :
    (∀ g, g < progPadsNonvac.fns.length → padsNoneAt0 g = .none →
      (progPadsNonvac.fn g).info.foreign = false → progPadsNonvac.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsNonvac.fn g).body → a.obligation = false) ∧
    (∀ g, g < progPadsNonvac.fns.length → padsNoneAt0 g = .none →
      (progPadsNonvac.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsNonvac.fn g).body → a.obligation = true →
          progPadsNonvac.selfMay stdCanUnwind f = false) := by
  refine ⟨fun g _ hp _ _ a ha => ?_, fun g _ hp _ f a ha _ => ?_⟩
  · cases g with
    | zero => simp [progPadsNonvac, Prog.fn] at ha
    | succ g => simp [padsNoneAt0] at hp
  · cases g with
    | zero =>
      simp only [progPadsNonvac, Prog.fn, List.getD_cons_zero, List.mem_singleton,
        Stmt.call.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      decide
    | succ g => simp [padsNoneAt0] at hp

/-- Under the `abort` panic handler, a `pads = none` function with a panic point. -/
def progAbortPadsRaise : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.raise .terminate], false⟩], .abort⟩

/-- `progAbortPadsRaise` satisfies both hypotheses of the local theorem (its panic point is not
constrained because the handler is `abort`). -/
theorem withPads_local_hypotheses_hold_progAbortPadsRaise :
    (∀ g, g < progAbortPadsRaise.fns.length → padsNoneAt0 g = .none →
      (progAbortPadsRaise.fn g).info.foreign = false → progAbortPadsRaise.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progAbortPadsRaise.fn g).body → a.obligation = false) ∧
    (∀ g, g < progAbortPadsRaise.fns.length → padsNoneAt0 g = .none →
      (progAbortPadsRaise.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progAbortPadsRaise.fn g).body → a.obligation = true →
          progAbortPadsRaise.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind (progAbortPadsRaise.withPads padsNoneAt0) 0 [] .abort := by
  refine ⟨fun g _ _ _ hh => absurd hh (by decide), fun g hlt _ _ f a ha _ => ?_, ⟨1, by decide⟩⟩
  cases g with
  | zero => simp [progAbortPadsRaise, Prog.fn] at ha
  | succ g => simp [progAbortPadsRaise] at hlt

/-- One `unwind` crate: function 0 (Rust, possibly unwinding, compiled with `pads = none`) calls
function 1 (Rust, which panics) with a plain call, which has no obligation. -/
def progPadsPlainUnwindThrough : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩

/-- `progPadsPlainUnwindThrough` satisfies both hypotheses of the local theorem, and the unwind
from function 1 passes through the `pads = none` function 0 in the compiled program; the
classification hypothesis of the program-level theorem fails for it (function 0 is classified as
possibly unwinding). -/
theorem withPads_local_hypotheses_hold_progPadsPlainUnwindThrough :
    (∀ g, g < progPadsPlainUnwindThrough.fns.length → padsNoneAt0 g = .none →
      (progPadsPlainUnwindThrough.fn g).info.foreign = false →
        progPadsPlainUnwindThrough.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsPlainUnwindThrough.fn g).body → a.obligation = false) ∧
    (∀ g, g < progPadsPlainUnwindThrough.fns.length → padsNoneAt0 g = .none →
      (progPadsPlainUnwindThrough.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsPlainUnwindThrough.fn g).body → a.obligation = true →
          progPadsPlainUnwindThrough.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind (progPadsPlainUnwindThrough.withPads padsNoneAt0) 0 [] .unwind ∧
    progPadsPlainUnwindThrough.selfMay stdCanUnwind 0 = true := by
  refine ⟨fun g _ hp _ _ a ha => ?_, fun g _ hp _ f a ha hobl => ?_, ⟨3, by decide⟩, by decide⟩
  · cases g with
    | zero => simp [progPadsPlainUnwindThrough, Prog.fn] at ha
    | succ g => simp [padsNoneAt0] at hp
  · cases g with
    | zero =>
      simp only [progPadsPlainUnwindThrough, Prog.fn, List.getD_cons_zero, List.mem_singleton,
        Stmt.call.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      simp [Action.obligation] at hobl
    | succ g => simp [padsNoneAt0] at hp

/-- One `unwind` crate whose single function (compiled with `pads = none`) is a panic point
without a landing pad. -/
def progPadsRaisePlain : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩

/-- `progPadsRaisePlain` satisfies both hypotheses of the local theorem under the `unwind`
handler (its panic point has no obligation), and its function 0 unwinds in the compiled
program. -/
theorem withPads_local_hypotheses_hold_progPadsRaisePlain :
    (∀ g, g < progPadsRaisePlain.fns.length → padsNoneAt0 g = .none →
      (progPadsRaisePlain.fn g).info.foreign = false → progPadsRaisePlain.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsRaisePlain.fn g).body → a.obligation = false) ∧
    (∀ g, g < progPadsRaisePlain.fns.length → padsNoneAt0 g = .none →
      (progPadsRaisePlain.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsRaisePlain.fn g).body → a.obligation = true →
          progPadsRaisePlain.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind (progPadsRaisePlain.withPads padsNoneAt0) 0 [] .unwind := by
  refine ⟨fun g hlt _ _ _ a ha => ?_, fun g hlt _ _ f a ha _ => ?_, ⟨1, by decide⟩⟩
  · cases g with
    | zero =>
      simp only [progPadsRaisePlain, Prog.fn, List.getD_cons_zero, List.mem_singleton,
        Stmt.raise.injEq] at ha
      subst ha; rfl
    | succ g => simp [progPadsRaisePlain] at hlt
  · cases g with
    | zero => simp [progPadsRaisePlain, Prog.fn] at ha
    | succ g => simp [progPadsRaisePlain] at hlt

/-- A single `pads = none` Rust function whose panic point has a cleanup pad dropping local 0;
panic handler `unwind`. -/
def progPadsRaiseCleanup : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.raise (.cleanup [0])], false⟩], .unwind⟩

/-- Without `hraise`: the compiled `pads = none` function loses the drop of local 0. -/
theorem withPads_local_fails_without_obligationFreeRaises :
    (∀ g, g < progPadsRaiseCleanup.fns.length → padsNoneAt0 g = .none →
      (progPadsRaiseCleanup.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsRaiseCleanup.fn g).body → a.obligation = true →
          progPadsRaiseCleanup.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind progPadsRaiseCleanup 0 [.drop 0 0] .unwind ∧
    ¬ Exec stdCanUnwind (progPadsRaiseCleanup.withPads padsNoneAt0) 0 [.drop 0 0] .unwind := by
  refine ⟨fun g hlt _ _ f a ha _ => ?_, ⟨1, by decide⟩, fun ⟨n, h⟩ => ?_⟩
  · cases g with
    | zero => simp [progPadsRaiseCleanup, Prog.fn] at ha
    | succ g => simp [progPadsRaiseCleanup] at hlt
  · have hf0 : (progPadsRaiseCleanup.withPads padsNoneAt0).fn 0 =
        ⟨rustInfo, 0, [.raise .none], false⟩ := by decide
    have hh : (progPadsRaiseCleanup.withPads padsNoneAt0).handler = .unwind := rfl
    have hs0 : (progPadsRaiseCleanup.withPads padsNoneAt0).selfMay stdCanUnwind 0 = true := by
      decide
    cases n with
    | zero => simp [runFn] at h
    | succ n => simp [runFn, hf0, hh, hs0, execBody, onUnwind, boundary, rustInfo] at h

/-- Without `hcall`: `progPadsMayUnwind` (no panic point in its `pads = none` function, which calls
a possibly-unwinding callee through a cleanup pad) loses a destructor event. -/
theorem withPads_local_fails_without_obligationCalleesNonUnwinding :
    (∀ g, g < progPadsMayUnwind.fns.length → padsNoneAt0 g = .none →
      (progPadsMayUnwind.fn g).info.foreign = false → progPadsMayUnwind.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsMayUnwind.fn g).body → a.obligation = false) ∧
    Exec stdCanUnwind progPadsMayUnwind 0 [.drop 0 0] .unwind ∧
    ¬ Exec stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) 0 [.drop 0 0] .unwind := by
  refine ⟨fun g _ hp _ _ a ha => ?_, ⟨3, by decide⟩, not_exec_progPadsMayUnwind_withPads⟩
  cases g with
  | zero => simp [progPadsMayUnwind, Prog.fn] at ha
  | succ g => simp [padsNoneAt0] at hp

/-! ## The toy codegen: preservation lemmas, non-`ub` runs, refuted readings -/

/-- `insertPads_foreignCovered` without its hypothesis: `progThrowingC` is unchanged by the pass
and is not `ForeignCovered`. -/
theorem insertPads_foreignCovered_fails_without_foreignCovered :
    ¬ ForeignCovered stdCanUnwind (insertPads stdCanUnwind progThrowingC) := by
  have h : insertPads stdCanUnwind progThrowingC = progThrowingC := by decide
  rw [h]; exact not_foreignCovered_progThrowingC

/-- `insertPads_siteAgreement` without its hypothesis: `progAbortCallsUnwind` is unchanged by the
pass and violates `SiteAgreement`. -/
theorem insertPads_siteAgreement_fails_without_siteAgreement :
    ¬ SiteAgreement stdCanUnwind (insertPads stdCanUnwind progAbortCallsUnwind) := by
  rw [insertPads_progAbortCallsUnwind]; exact not_siteAgreement_progAbortCallsUnwind

/-- `exec_insertPads_of_exec_of_ne_ub` without `o ≠ ub`: function 0 of `progAbortImportPlain` has
a run with outcome `ub`, which `insertPads` removes. -/
theorem exec_insertPads_fails_without_ne_ub :
    Exec stdCanUnwind progAbortImportPlain 0 [] .ub ∧
    ¬ Exec stdCanUnwind (insertPads stdCanUnwind progAbortImportPlain) 0 [] .ub := by
  refine ⟨exec_progAbortImportPlain_ub, fun h => ?_⟩
  rw [insertPads_progAbortImportPlain] at h
  exact noUB_of_enforced_of_foreignCovered_of_siteAgreement _ _
    noUB_hypotheses_hold_progAbortImportPadded.1
    noUB_hypotheses_hold_progAbortImportPadded.2.1
    noUB_hypotheses_hold_progAbortImportPadded.2.2.1 0 [] _ h rfl

/-- Instances for the codegen lemmas: `progAbortImportPlain` satisfies `ForeignCovered` and
`SiteAgreement` under `stdCanUnwind`, and the non-`ub` run of `progUnwindCatch` is kept by the
pass. -/
theorem insertPads_hypotheses_hold :
    ForeignCovered stdCanUnwind progAbortImportPlain ∧
    SiteAgreement stdCanUnwind progAbortImportPlain ∧
    Outcome.ret ≠ Outcome.ub ∧ Exec stdCanUnwind progUnwindCatch 0 [.drop 1 7, .caught 0] .ret ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progUnwindCatch) 0 [.drop 1 7, .caught 0] .ret :=
  ⟨noUB_insertPads_hypotheses_hold_progAbortImportPlain.1,
    noUB_insertPads_hypotheses_hold_progAbortImportPlain.2, by decide, exec_progUnwindCatch,
    exec_insertPads_of_exec_of_ne_ub _ _ _ _ _ (by decide) exec_progUnwindCatch⟩

/-- **Refuted reading.** The statement "`insertPads` changes the bodies of exactly those functions
that are non-foreign and classified as non-unwinding by their own crate" is false: function 0 of
`progAbortCallsUnwind` is non-foreign and classified as non-unwinding, and its body is unchanged.
The corrected statement is `insertPads_body_ne_iff`. -/
theorem refuted_insertPads_changes_exactly_nonunwinding_bodies :
    ¬ ∀ (cu : Prec) (p : Prog) (g : Nat),
      ((insertPads cu p).fn g).body ≠ (p.fn g).body ↔
        ((p.fn g).info.foreign = false ∧ p.selfMay cu g = false) := by
  intro h
  exact (h stdCanUnwind progAbortCallsUnwind 0).2 ⟨by decide, by decide⟩ (by decide)

/-- **Refuted reading.** The statement "`padStmt` gives a call site a terminate pad exactly when
the caller's crate classifies the callee as possibly unwinding and the site has no stopping pad"
is false: a call site that already has a terminate pad keeps it. The corrected statements are
`padStmt_call` and `padStmt_call_ne_iff`. -/
theorem refuted_padStmt_call_terminate_exactly :
    ¬ ∀ (cu : Prec) (p : Prog) (g f : Nat) (act : Action),
      padStmt cu p g (.call f act) = .call f .terminate ↔
        (p.viewMay cu g f = true ∧ act.Stops = false) := by
  intro h
  exact absurd ((h stdCanUnwind progAbortCallsUnwind 0 1 .terminate).1 (by decide)).2
    (by decide)

/-- **Refuted reading.** The statement "`padStmt` gives a panic point a terminate pad exactly when
it has no stopping pad" is false: a panic point that already has a terminate pad keeps it. The
corrected statements are `padStmt_raise` and `padStmt_raise_ne_iff`. -/
theorem refuted_padStmt_raise_terminate_exactly :
    ¬ ∀ (cu : Prec) (p : Prog) (g : Nat) (act : Action),
      padStmt cu p g (.raise act) = .raise .terminate ↔ act.Stops = false := by
  intro h
  exact absurd ((h stdCanUnwind progPlainCallFromNounwind 0 .terminate).1 (by decide))
    (by decide)

/-- Function 0 (`extern "C"`, non-unwinding) calls function 2 (Rust, which panics) with a cleanup
pad dropping local 7; function 1 (`extern "C"`, non-unwinding) has a panic point with a cleanup pad
dropping local 7. Panic handler `unwind`. -/
def progCleanupOverwritten : Prog :=
  ⟨[unwindCfg],
    [⟨cFn, 0, [.call 2 (.cleanup [7])], false⟩, ⟨cFn, 0, [.raise (.cleanup [7])], false⟩,
     ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩

/-- **Refuted reading.** The statement "the pass keeps existing cleanup pads" is false: in
`progCleanupOverwritten` the pass replaces the cleanup pad of a possibly-unwinding call site and of
a panic point, inside non-unwinding functions, by terminate pads (losing the drop list). -/
theorem refuted_insertPads_keeps_cleanup_pads :
    (¬ ∀ (cu : Prec) (p : Prog) (g f : Nat) (ds : List Nat),
      Stmt.call f (.cleanup ds) ∈ (p.fn g).body →
        Stmt.call f (.cleanup ds) ∈ ((insertPads cu p).fn g).body) ∧
    (¬ ∀ (cu : Prec) (p : Prog) (g : Nat) (ds : List Nat),
      Stmt.raise (.cleanup ds) ∈ (p.fn g).body →
        Stmt.raise (.cleanup ds) ∈ ((insertPads cu p).fn g).body) ∧
    ((insertPads stdCanUnwind progCleanupOverwritten).fn 0).body = [.call 2 .terminate] ∧
    ((insertPads stdCanUnwind progCleanupOverwritten).fn 1).body = [.raise .terminate] := by
  have h0 : ((insertPads stdCanUnwind progCleanupOverwritten).fn 0).body = [.call 2 .terminate] := by
    decide
  have h1 : ((insertPads stdCanUnwind progCleanupOverwritten).fn 1).body = [.raise .terminate] := by
    decide
  refine ⟨fun h => ?_, fun h => ?_, h0, h1⟩
  · have := h stdCanUnwind progCleanupOverwritten 0 2 [7] (by decide)
    rw [h0] at this
    simp at this
  · have := h stdCanUnwind progCleanupOverwritten 1 [7] (by decide)
    rw [h1] at this
    simp at this

/-- A non-unwinding caller (`extern "C"`) calling a Rust function in an `unwind` crate whose body
is empty: the caller's crate classifies the callee as possibly unwinding. -/
def progCalmCallee : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [], false⟩], .unwind⟩

/-- `insertPads` inserts a terminate pad at the call site of `progCalmCallee` although the callee
has no unwinding run: the pass follows classifications, not behaviour. -/
theorem insertPads_pad_without_unwinding_callee :
    progCalmCallee.viewMay stdCanUnwind 0 1 = true ∧
    ((insertPads stdCanUnwind progCalmCallee).fn 0).body = [.call 1 .terminate] ∧
    ¬ (∃ t, Exec stdCanUnwind progCalmCallee 1 t .unwind) := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨t, n, hn⟩
  cases n with
  | zero => simp [runFn] at hn
  | succ n =>
    have hf1 : progCalmCallee.fn 1 = ⟨rustInfo, 0, [], false⟩ := rfl
    simp [runFn, hf1, execBody, boundary, rustInfo] at hn

/-! ## Rule order: the ABI-first order and `insertPads` -/

/-- One `abort` crate: function 0 (a Rust-defined `extern "C-unwind"` function) calls function 1,
a foreign `"C-unwind"` import that may unwind, with a plain call; panic handler `abort`. -/
def progAbortCUnwindExport : Prog :=
  ⟨[abortCfg], [⟨rustDefinedCUnwind, 0, [.call 1 .none], false⟩, ⟨foreignCUnwind, 0, [], true⟩],
    .abort⟩

/-- Under `abiFirstCanUnwind`, `insertPads` leaves `progAbortCUnwindExport` unchanged and the
foreign unwind leaves function 0 (defined in an `abort` crate); under `stdCanUnwind`, `insertPads`
inserts a terminate pad and the same unwind aborts. -/
theorem abiFirst_insertPads_lets_foreign_unwind_leave_abort_crate :
    insertPads abiFirstCanUnwind progAbortCUnwindExport = progAbortCUnwindExport ∧
    Exec abiFirstCanUnwind progAbortCUnwindExport 0 [] .unwind ∧
    ((insertPads stdCanUnwind progAbortCUnwindExport).fn 0).body = [.call 1 .terminate] ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progAbortCUnwindExport) 0 [] .abort := by
  refine ⟨by decide, ⟨2, by decide⟩, by decide, ⟨2, by decide⟩⟩

/-! ## Degenerate edges -/

/-- Degenerate edges: on the empty chain, `compRet b0 [] v = specRet [] v = v` whatever the
backend `b0`; and a program with no crates satisfies `LinkOK` (every crate index is out of range
and denotes `CrateCfg.dflt`, which uses the `unwind` strategy). -/
theorem compRet_nil_and_linkOK_of_no_crates (b0 : AbiCodec) (v : Nat) (fns : List FnDef)
    (h : Strategy) :
    compRet b0 [] v = v ∧ specRet [] v = v ∧ LinkOK ⟨[], fns, h⟩ :=
  ⟨rfl, rfl, fun _ _ hc => by cases hc⟩

end Toy.UnwindCap
