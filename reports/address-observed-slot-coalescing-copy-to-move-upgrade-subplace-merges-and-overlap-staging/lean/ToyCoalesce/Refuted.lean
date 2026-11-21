import ToyCoalesce.CexExtra

/-!
# Earlier formulations that are false (reference points, not results)

Earlier formulations of several statements of this package used weaker definitions. Each
theorem below proves, with a concrete program, that one earlier formulation is false. The
definitions in this module reproduce the earlier forms under new names; no result of the package
uses them.
-/

namespace Toy.Coalesce

/-- The earlier well-formedness condition: `ForestWF` without its `CallsInBounds` clause. -/
def ForestWFNoCallCheck (P : Prog) (μ : Forest) : Prop :=
  (μ.map Edge.child).Nodup ∧
  (∀ e ∈ μ, e.child < P.nloc ∧ e.parent < P.nloc ∧ e.child ≠ e.parent ∧
    e.off + P.size e.child ≤ P.size e.parent) ∧
  (∀ x, x < P.nloc → μ.parentOf (μ.root x) = none) ∧
  (∀ c ∈ P.fns, μ.inClass c.prm = false)

set_option synthInstance.maxSize 1024 in
instance (P : Prog) (μ : Forest) : Decidable (ForestWFNoCallCheck P μ) := by
  unfold ForestWFNoCallCheck; infer_instance

/-- The earlier licensing condition: as `Licensed`, but for `MoveSem.inPlaceCall` the last
conjunct is `CalleeNoParamAddr P fn` (the callee body never takes its parameter's address)
instead of `¬ AddrTaken P (P.fn fn).prm`. -/
def LicensedNoParamAddr (ms : MoveSem) (P : Prog) (O : ObsMask) (k : Nat) (q : Place) : Prop :=
  match ms with
  | .asCopy => True
  | .deinit =>
    O (k + 1) q.base = false ∧
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      (P.fn fn).body.any (Stmt.mayReadNoCall P q.base) = false
  | .inPlaceCall =>
    ∀ fn, P.body[k]? = some (.call fn (.copy q)) →
      O (k + 1) q.base = false ∧
      (P.fn fn).body.any (fun st => st.operands.any (Operand.readsName q.base) ||
        (match st with
         | .store p _ => p.base == q.base
         | .assign lhs _ => lhs.base == q.base
         | _ => false)) = false ∧
      (decide (AddrTaken P q.base) && (P.fn fn).body.any (fun st =>
        st.operands.any Operand.isLoad || (match st with | .store _ _ => true | _ => false)))
        = false ∧
      CalleeNoParamAddr P fn

/-- The earlier access points: as `AccessPt`, but a call contributes the by-name reads of its
callee body to the read half only and the by-name writes to the write half only. -/
def AccessPtHalf (P : Prog) (u p : Nat) : Bool :=
  if p % 2 = 0 then (P.code.getD (p / 2) .nop).readsByName P u
  else (P.code.getD (p / 2) .nop).writesByName P u

/-- Interval membership with the earlier access points. -/
def InIvHalf (nt : Notion) (P : Prog) (u p : Nat) : Bool :=
  match nt with
  | .lexical => LexLiveAt P u (p / 2)
  | .precise =>
    (List.range (p + 1)).any (AccessPtHalf P u) &&
    ((List.range (2 * P.code.length + 2)).filter (p ≤ ·)).any (AccessPtHalf P u)

/-- Interval overlap with the earlier access points. -/
def IvOverlapHalf (nu nv : Notion) (P : Prog) (u v : Nat) : Prop :=
  ∃ p, p < 2 * P.code.length + 2 ∧ InIvHalf nu P u p = true ∧ InIvHalf nv P v p = true

instance (nu nv : Notion) (P : Prog) (u v : Nat) : Decidable (IvOverlapHalf nu nv P u v) := by
  unfold IvOverlapHalf; infer_instance

/-- The earlier policy check (with `AccessPtHalf`). -/
def PolicyCheckHalf (pol : Policy) (P : Prog) (μ : Forest) : Prop :=
  ∀ u, u < P.nloc → ∀ v, v < P.nloc → u ≠ v → μ.sameClass u v = true →
    μ.windowsOverlap P u v = true →
    ¬ IvOverlapHalf (pol (decide (AddrTaken P u))) (pol (decide (AddrTaken P v))) P u v

instance (pol : Policy) (P : Prog) (μ : Forest) : Decidable (PolicyCheckHalf pol P μ) := by
  unfold PolicyCheckHalf; infer_instance

/-- Policy soundness relative to a well-formedness condition and a policy check. -/
def PolicySoundWith (wf : Prog → Forest → Prop) (chk : Policy → Prog → Forest → Prop)
    (pol : Policy) : Prop :=
  ∀ (ms : MoveSem) (P : Prog) (μ : Forest), wf P μ → chk pol P μ →
    Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P

/-- The earlier staging condition: callee assignments checked syntactically, ignoring in-place
binding of the callee parameter. -/
def NoStagingNeededSyn (P : Prog) : Prop :=
  (stmtsNoStaging P.code && P.fns.all (fun c => stmtsNoStaging c.body)) = true

instance (P : Prog) : Decidable (NoStagingNeededSyn P) := by
  unfold NoStagingNeededSyn; infer_instance

/-- The earlier callee staging condition (syntactic). -/
def CalleesNoStagingSyn (P : Prog) : Prop := P.fns.all (fun c => stmtsNoStaging c.body) = true

instance (P : Prog) : Decidable (CalleesNoStagingSyn P) := by
  unfold CalleesNoStagingSyn; infer_instance

/-! ## Copy-to-move upgrades under `MoveSem.inPlaceCall` -/

theorem pPrmEscaped_outcome (am : AssignMode) (A : Layout) :
    outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A = .done [.vals [.int 7]] ∨
    outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A = .badLayout := by
  cases am <;> simp only [pPrmEscaped] <;> run_eval

/-- `pPrmEscaped` satisfies every hypothesis of the earlier in-place theorem and of the earlier
licensed form (with `CalleeNoParamAddr`), but its callee parameter local is address-taken in the
caller; the upgraded program has undefined behaviour on `A0` (the callee loads through a pointer
to the parameter local, which in-place passing never allocates), so the upgrade is not a
refinement. -/
theorem cex_inPlaceCall_param_addrTaken_in_caller (am : AssignMode) :
    CallSite pPrmEscaped 6 0 qx ∧ UpgradeSite pPrmEscaped 6 qx ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ pPrmEscaped A).log 6 false qx) ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmEscaped A ≠ .badLayout →
      CalleeAvoids (run ⟨.inPlaceCall, am⟩ pPrmEscaped A).log 6 qx) ∧
    CalleeNoParamAddr pPrmEscaped 0 ∧ AddrTaken pPrmEscaped (pPrmEscaped.fn 0).prm ∧
    ObsCert pPrmEscaped (obsAnalysis pPrmEscaped) ∧
    LicensedNoParamAddr .inPlaceCall pPrmEscaped (obsAnalysis pPrmEscaped) 6 qx ∧
    outcome ⟨.inPlaceCall, am⟩ (pPrmEscaped.upgradeAt 6) A0 = .ub ∧
    ¬ Refines ⟨.inPlaceCall, am⟩ (pPrmEscaped.upgradeAt 6) ⟨.inPlaceCall, am⟩ pPrmEscaped := by
  refine ⟨⟨by decide, by decide⟩, Or.inr (Or.inl ⟨0, by decide, by decide⟩), ?_, ?_, by decide,
    by decide, ?_, ?_, ?_, ?_⟩
  · intro A _ _; cases am <;> simp only [pPrmEscaped, qx] <;> log_eval
  · intro A _ _; cases am <;> simp only [pPrmEscaped, qx] <;> log_eval
  · unfold ObsCert; decide
  · refine fun fn h => ?_
    have hfn : fn = 0 := by simp [pPrmEscaped, qx] at h; omega
    subst hfn
    exact ⟨by decide, by decide, by decide, by decide⟩
  · cases am <;> decide
  · exact not_refines_of_witness A0 _ (pPrmEscaped_outcome am) (by cases am <;> decide)
      (by cases am <;> decide)

theorem pPrmConflict_outcome (am : AssignMode) (A : Layout) :
    outcome ⟨.inPlaceCall, am⟩ pPrmConflict A = .done [.cmp false] ∨
    outcome ⟨.inPlaceCall, am⟩ pPrmConflict A = .badLayout := by
  cases am <;> simp only [pPrmConflict] <;> run_eval

/-- `pPrmConflict` satisfies every hypothesis of the earlier in-place theorem (with
`CalleeNoParamAddr`) and has no pointer to the parameter local before the call; copy passing
allocates the parameter local while `z` is allocated, so every non-excluded source run prints
`cmp false`, while the upgraded program prints `cmp true` on `A_eq03`. -/
theorem cex_inPlaceCall_param_conflict (am : AssignMode) :
    CallSite pPrmConflict 5 0 ⟨2, 0, 1⟩ ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ pPrmConflict A).log 5 false ⟨2, 0, 1⟩) ∧
    (∀ A, outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .ub →
      outcome ⟨.inPlaceCall, am⟩ pPrmConflict A ≠ .badLayout →
      CalleeAvoids (run ⟨.inPlaceCall, am⟩ pPrmConflict A).log 5 ⟨2, 0, 1⟩) ∧
    CalleeNoParamAddr pPrmConflict 0 ∧ AddrTaken pPrmConflict (pPrmConflict.fn 0).prm ∧
    ¬ Refines ⟨.inPlaceCall, am⟩ (pPrmConflict.upgradeAt 5) ⟨.inPlaceCall, am⟩ pPrmConflict := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_, by decide, by decide, ?_⟩
  · intro A _ _; cases am <;> simp only [pPrmConflict] <;> log_eval
  · intro A _ _; cases am <;> simp only [pPrmConflict] <;> log_eval
  · exact not_refines_of_witness A_eq03 _ (pPrmConflict_outcome am) (by cases am <;> decide)
      (by cases am <;> decide)

/-- Refuted earlier statement: the in-place upgrade theorem with `CalleeNoParamAddr P fn` in
place of `¬ AddrTaken P (P.fn fn).prm`. -/
theorem refuted_upgrade_moveInPlaceCall_refines_of_noReadAfterCall_calleeAvoids_noParamAddr :
    ¬ ∀ (am : AssignMode) (P : Prog) (k fn : Nat) (q : Place), CallSite P k fn q →
      (∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
        outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
        NoReadBeforeReinit (run ⟨.inPlaceCall, am⟩ P A).log k false q) →
      (∀ A, outcome ⟨.inPlaceCall, am⟩ P A ≠ .ub →
        outcome ⟨.inPlaceCall, am⟩ P A ≠ .badLayout →
        CalleeAvoids (run ⟨.inPlaceCall, am⟩ P A).log k q) →
      CalleeNoParamAddr P fn →
      Refines ⟨.inPlaceCall, am⟩ (P.upgradeAt k) ⟨.inPlaceCall, am⟩ P := by
  intro h
  have c := cex_inPlaceCall_param_addrTaken_in_caller .atomic
  exact c.2.2.2.2.2.2.2.2.2 (h .atomic pPrmEscaped 6 0 qx c.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1)

/-- Refuted earlier statement: certificate-licensed upgrades with the earlier licensing condition
`LicensedNoParamAddr` are refinements. -/
theorem refuted_upgrade_refines_of_obsCert_licensed_noParamAddr :
    ¬ ∀ (sem : Sem) (P : Prog) (O : ObsMask) (k : Nat) (q : Place), UpgradeSite P k q →
      ObsCert P O → LicensedNoParamAddr sem.move P O k q → Refines sem (P.upgradeAt k) sem P := by
  intro h
  have c := cex_inPlaceCall_param_addrTaken_in_caller .atomic
  exact c.2.2.2.2.2.2.2.2.2 (h semI pPrmEscaped _ 6 qx c.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1)

/-! ## Coalescing, policies and transfer without `CallsInBounds` -/

/-- Refuted earlier statement: the single-merge theorem with `ForestWFNoCallCheck`. -/
theorem refuted_coalesce_single_refines_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (x y f : Nat), ForestWFNoCallCheck P (single x y f) →
      NoValueClobberStmt ms (single x y f) P →
      (AddrTaken P x → AddrTaken P y → ¬ LexOverlap P x y) →
      Refines ⟨ms, .atomic⟩ (coalesce (single x y f) P) ⟨ms, .atomic⟩ P := by
  intro h
  have c := cex_coalesce_needs_callsInBounds .deinit
  exact c.2.2.2.2.2.2.2.2.2.2.2.2.1 (h .deinit pOobCall 1 0 0 (by decide) c.2.2.1 c.2.2.2.1)

/-- Refuted earlier statement: the forest theorem with `ForestWFNoCallCheck`. -/
theorem refuted_coalesce_refines_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ →
      Refines ⟨ms, .atomic⟩ (coalesce μ P) ⟨ms, .atomic⟩ P := by
  intro h
  have c := cex_coalesce_needs_callsInBounds .deinit
  exact c.2.2.2.2.2.2.2.2.2.2.2.2.1 (h .deinit pOobCall _ (by decide) c.2.2.1 c.2.2.2.2.1)

/-- Refuted earlier statement: with `ForestWFNoCallCheck` and `AccessPtHalf`, every policy that
uses lexical intervals for address-taken locals is sound (refuted already for the
lexical-everywhere policy, by the absent callee of `pOobCall`). -/
theorem refuted_policySound_of_lexical_noCallCheck_halfPoints :
    ¬ ∀ pol : Policy, pol true = .lexical → PolicySoundWith ForestWFNoCallCheck PolicyCheckHalf pol := by
  intro h
  have c := cex_coalesce_needs_callsInBounds .deinit
  refine c.2.2.2.2.2.2.2.2.2.2.2.2.1
    (h (fun _ => .lexical) rfl .deinit pOobCall (single 1 0 0) (by decide) ?_)
  have hpc := c.2.2.2.2.2.1 (fun _ => .lexical)
  intro u hu v hv hne hs hw hex
  exact hpc u hu v hv hne hs hw hex

/-- Refuted earlier statement: the policy characterization with `ForestWFNoCallCheck` and
`AccessPtHalf`. -/
theorem refuted_policySound_iff_noCallCheck_halfPoints :
    ¬ ∀ pol : Policy, PolicySoundWith ForestWFNoCallCheck PolicyCheckHalf pol ↔ pol true = .lexical :=
  fun h => refuted_policySound_of_lexical_noCallCheck_halfPoints fun pol hp => (h pol).2 hp

/-- Refuted earlier statement, independently of absent callees: with the half-statement access
points `AccessPtHalf`, the mixed policy (lexical for address-taken locals, precise otherwise) is
not sound even over forests satisfying `ForestWF` (`pCalleeReorder`, whose callee writes `y`
before reading `x`). -/
theorem refuted_policySound_mixed_halfPoints :
    ¬ PolicySoundWith ForestWF PolicyCheckHalf (fun b => if b then .lexical else .precise) := by
  intro h
  have c := cex_callee_reorder_rejected_by_policy .deinit
  exact c.2.2.2.2.2.2 (h .deinit pCalleeReorder (single 0 1 0) c.1 (by decide))

/-- Refuted earlier statement: address-free forward transfer with `ForestWFNoCallCheck`. -/
theorem refuted_vc_forward_addrFree_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ∀ Post : List Event → Prop, AddrFree Post →
      Valid ⟨ms, .atomic⟩ P Post → Valid ⟨ms, .atomic⟩ (coalesce μ P) Post := by
  intro h
  have c := cex_coalesce_needs_callsInBounds .deinit
  exact c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (h .deinit pOobCall _ (by decide) c.2.2.1 _ (fun _ _ _ => Iff.rfl) c.2.2.2.2.2.2.2.2.2.2.1)

/-- Refuted earlier statement: forward transfer of arbitrary postconditions with
`ForestWFNoCallCheck`. -/
theorem refuted_vc_forward_of_classAddrDisjoint_noCallCheck :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ → ∀ Post : List Event → Prop,
      Valid ⟨ms, .atomic⟩ P Post → Valid ⟨ms, .atomic⟩ (coalesce μ P) Post := by
  intro h
  have c := cex_coalesce_needs_callsInBounds .deinit
  exact c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (h .deinit pOobCall _ (by decide) c.2.2.1 c.2.2.2.2.1 _ c.2.2.2.2.2.2.2.2.2.2.1)

/-! ## Staging with syntactic callee checks -/

theorem pAliasSwap_atomic_outcome (A : Layout) :
    outcome ⟨.inPlaceCall, .atomic⟩ pAliasSwap A = .done [.vals [.int 2, .int 1]] ∨
    outcome ⟨.inPlaceCall, .atomic⟩ pAliasSwap A = .badLayout := by
  simp only [pAliasSwap]; run_eval

/-- In-place aliasing defeats syntactic callee staging checks: `pAliasSwap` satisfies
`NoStagingNeededSyn`, `CalleesNoStagingSyn`, `LocalsInRange` and `ParamsInRange`, staging leaves
it unchanged, and under `MoveSem.inPlaceCall` its in-order and atomic outcomes on `A0` differ, so
staging under in-order writes neither refines nor has the behaviours of the atomic source. The
alias-aware check `CalleesNoStaging` rejects it. -/
theorem cex_staging_inPlaceCall_alias :
    NoStagingNeededSyn pAliasSwap ∧ CalleesNoStagingSyn pAliasSwap ∧ LocalsInRange pAliasSwap ∧
    ParamsInRange pAliasSwap ∧ ¬ CalleesNoStaging pAliasSwap ∧
    outcome ⟨.inPlaceCall, .inOrder⟩ pAliasSwap A0 ≠ outcome ⟨.inPlaceCall, .atomic⟩ pAliasSwap A0 ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage pAliasSwap) ⟨.inPlaceCall, .atomic⟩ pAliasSwap ∧
    ¬ BehEq ⟨.inPlaceCall, .inOrder⟩ (stage pAliasSwap) ⟨.inPlaceCall, .atomic⟩ pAliasSwap := by
  have hnr : ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage pAliasSwap) ⟨.inPlaceCall, .atomic⟩
      pAliasSwap :=
    not_refines_of_witness A0 _ pAliasSwap_atomic_outcome (by decide) (by decide)
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, hnr,
    fun hb => hnr fun o ho => Or.inr ((hb o).1 ho)⟩

/-- Refuted earlier statement: in-order and atomic outcomes agree under `NoStagingNeededSyn`. -/
theorem refuted_outcome_inOrder_eq_atomic_synStaging :
    ¬ ∀ (ms : MoveSem) (P : Prog), NoStagingNeededSyn P → ∀ A : Layout,
      outcome ⟨ms, .inOrder⟩ P A = outcome ⟨ms, .atomic⟩ P A :=
  fun h => cex_staging_inPlaceCall_alias.2.2.2.2.2.1
    (h .inPlaceCall pAliasSwap cex_staging_inPlaceCall_alias.1 A0)

/-- Refuted earlier statement: staging refines under `CalleesNoStagingSyn` alone. -/
theorem refuted_stage_inOrder_refines_atomic_synStaging :
    ¬ ∀ (ms : MoveSem) (Q : Prog), CalleesNoStagingSyn Q →
      Refines ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q :=
  fun h => cex_staging_inPlaceCall_alias.2.2.2.2.2.2.1
    (h .inPlaceCall pAliasSwap cex_staging_inPlaceCall_alias.2.1)

/-- Refuted earlier statement: the behavioural-equivalence form under `CalleesNoStagingSyn` and
`LocalsInRange`. -/
theorem refuted_stage_inOrder_behEq_atomic_synStaging :
    ¬ ∀ (ms : MoveSem) (Q : Prog), CalleesNoStagingSyn Q → LocalsInRange Q →
      BehEq ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q :=
  fun h => cex_staging_inPlaceCall_alias.2.2.2.2.2.2.2
    (h .inPlaceCall pAliasSwap cex_staging_inPlaceCall_alias.2.1 cex_staging_inPlaceCall_alias.2.2.1)

theorem pAliasCoalSwap_outcome (am : AssignMode) (A : Layout) :
    outcome ⟨.inPlaceCall, am⟩ pAliasCoalSwap A = .done [.vals [.int 2, .int 1]] ∨
    outcome ⟨.inPlaceCall, am⟩ pAliasCoalSwap A = .badLayout := by
  cases am <;> simp only [pAliasCoalSwap] <;> run_eval

/-- In-place aliasing defeats syntactic callee checks in the pipeline (`pAliasCoalSwap`, merge
`x ↦ y.0`, `MoveSem.inPlaceCall`): the forest satisfies `ForestWF`, `NoValueClobberStmt` and
`ClassAddrDisjoint` hold, the syntactic staging conditions hold for the source and the coalesced
program, every callee parameter exists, and neither the staged nor the unstaged coalesced program
refines the source under in-order writes. The alias-aware conditions reject it. -/
theorem cex_pipeline_inPlaceCall_alias :
    ForestWF pAliasCoalSwap (single 0 1 0) ∧
    NoValueClobberStmt .inPlaceCall (single 0 1 0) pAliasCoalSwap ∧
    ClassAddrDisjoint pAliasCoalSwap (single 0 1 0) ∧ NoStagingNeededSyn pAliasCoalSwap ∧
    NoStagingNeededSyn (coalesce (single 0 1 0) pAliasCoalSwap) ∧
    CalleesNoStagingSyn (coalesce (single 0 1 0) pAliasCoalSwap) ∧ ParamsInRange pAliasCoalSwap ∧
    ¬ CalleesNoStaging (coalesce (single 0 1 0) pAliasCoalSwap) ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (stage (coalesce (single 0 1 0) pAliasCoalSwap))
      ⟨.inPlaceCall, .inOrder⟩ pAliasCoalSwap ∧
    ¬ Refines ⟨.inPlaceCall, .inOrder⟩ (coalesce (single 0 1 0) pAliasCoalSwap)
      ⟨.inPlaceCall, .inOrder⟩ pAliasCoalSwap := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro A _ _; simp only [pAliasCoalSwap]; log_eval
  · exact not_refines_of_witness A0 _ (pAliasCoalSwap_outcome .inOrder) (by decide) (by decide)
  · exact not_refines_of_witness A0 _ (pAliasCoalSwap_outcome .inOrder) (by decide) (by decide)

/-- Refuted earlier statement: the staged pipeline with `ForestWFNoCallCheck` and the syntactic
staging conditions (refuted by the absent callee of `pOobCall`; the aliasing witness
`cex_pipeline_inPlaceCall_alias` refutes it even with `ForestWF`). -/
theorem refuted_stage_coalesce_refines_inOrder_noCallCheck_synStaging :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ → NoStagingNeededSyn P →
      CalleesNoStagingSyn (coalesce μ P) →
      Refines ⟨ms, .inOrder⟩ (stage (coalesce μ P)) ⟨ms, .inOrder⟩ P := by
  intro h
  have c := cex_pipeline_inPlaceCall_alias
  exact c.2.2.2.2.2.2.2.2.1 (h .inPlaceCall pAliasCoalSwap _ (by decide) c.2.1 c.2.2.1 c.2.2.2.1
    c.2.2.2.2.2.1)

/-- Refuted earlier statement: the non-staging pipeline with `ForestWFNoCallCheck` and the
syntactic staging conditions. -/
theorem refuted_coalesce_refines_inOrder_noCallCheck_synStaging :
    ¬ ∀ (ms : MoveSem) (P : Prog) (μ : Forest), ForestWFNoCallCheck P μ →
      NoValueClobberStmt ms μ P → ClassAddrDisjoint P μ → NoStagingNeededSyn P →
      NoStagingNeededSyn (coalesce μ P) →
      Refines ⟨ms, .inOrder⟩ (coalesce μ P) ⟨ms, .inOrder⟩ P := by
  intro h
  have c := cex_pipeline_inPlaceCall_alias
  exact c.2.2.2.2.2.2.2.2.2 (h .inPlaceCall pAliasCoalSwap _ (by decide) c.2.1 c.2.2.1 c.2.2.2.1
    c.2.2.2.2.1)

/-- Refuted earlier statement: staging refines under `CalleesNoStaging` without `ParamsInRange`
(`pStageOobPrm`). -/
theorem refuted_stage_inOrder_refines_atomic_noParamsInRange :
    ¬ ∀ (ms : MoveSem) (Q : Prog), CalleesNoStaging Q →
      Refines ⟨ms, .inOrder⟩ (stage Q) ⟨ms, .atomic⟩ Q :=
  fun h => cex_stage_refines_needs_paramsInRange.2.2.2
    (h .inPlaceCall pStageOobPrm cex_stage_refines_needs_paramsInRange.1)

end Toy.Coalesce
