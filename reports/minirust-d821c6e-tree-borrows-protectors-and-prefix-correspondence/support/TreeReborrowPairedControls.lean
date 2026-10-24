import AnnealResearch.TreeReborrowAgreement
import AnnealResearch.TreeReborrowStateControls
import AnnealResearch.TreeMemoryPairing

/-!
The actual factored reborrow is challenged using a directly supplied F memory,
not by executing the reference through reify or extracting a successful state
with a default. Checked full correspondence transfers independently stated R
outcomes into exact outcome/full-reified-state observations of actual F execution.
The Disabled-root specimen remains shape-only. Pointer fragments, source settings
computation, Rust reachability and prefix-client extension remain unclaimed.
-/
namespace AnnealResearch.TreeReborrowPairedControls

open TreePermissions

def before : TreeFactoredMemory.State :=
  TreeMemoryPairing.single (TreeMemoryControls.block 2)
    (TreeFactoredMemory.reborrowChild [.unprot .unique, .unprot .disabled] .no) [(42, [3])]

theorem before_reifies : TreeFactoredMemory.reify before = TreeReborrowStateControls.before := by
  unfold before TreeMemoryPairing.single TreeFactoredMemory.reify TreeReborrowStateControls.before
    TreeMemory.setTree TreeMemoryControls.initial
  congr 1
  funext id
  by_cases zero : id = 0
  · subst id
    simp only [↓reduceIte, Option.map_some, TreeFactoredReborrow.child_reify, TreeReborrowStateControls.rootTree]
  · simp [zero]

theorem before_sized : TreeFactoredMemory.WellSized before := by
  apply TreeMemoryPairing.single_sized
  apply TreeFactoredReborrow.child_uniform
  rfl

/-- Full reification includes raw memory, every optional tree and the ordered
frame. The factored operation itself executes insertion and initial accesses. -/
theorem actual_factored_partial_failure :
    TreeFactoredMemory.translate
      (TreeFactoredMemory.reborrow before TreeMemoryControls.root TreeReborrowStateControls.reads) =
      .ub (.tree .unprotectedLocalReadDisabled) TreeReborrowStateControls.partialState := by
  rw [← TreeReborrowAgreement.reborrow_agrees before TreeMemoryControls.root TreeReborrowStateControls.reads before_sized,
    before_reifies]
  exact TreeReborrowStateControls.actual_partial_initial_failure

theorem actual_factored_cell_success :
    TreeFactoredMemory.translate
      (TreeFactoredMemory.reborrow before TreeMemoryControls.root TreeReborrowStateControls.cells) =
      .ok TreeReborrowStateControls.childPointer TreeReborrowStateControls.cellState := by
  rw [← TreeReborrowAgreement.reborrow_agrees before TreeMemoryControls.root TreeReborrowStateControls.cells before_sized,
    before_reifies]
  exact TreeReborrowStateControls.actual_cell_birth_skips_initial_access

theorem actual_factored_settings_order :
    TreeFactoredMemory.translate
      (TreeFactoredMemory.reborrow before ⟨16, some (0, [99])⟩
        ⟨[.unprot .reserved], .unprot .reserved, .strong⟩) =
      .unsupported .settings TreeReborrowStateControls.before := by
  rw [← TreeReborrowAgreement.reborrow_agrees before ⟨16, some (0, [99])⟩
    ⟨[.unprot .reserved], .unprot .reserved, .strong⟩ before_sized, before_reifies]
  exact TreeReborrowStateControls.settings_rejected_before_missing_parent

/-- An actual UB result exists and retains the prior frame, raw state and exact
represented partial tree. No error is converted into a continuing configuration. -/
theorem actual_partial_result_witness :
    ∃ changed, TreeFactoredMemory.reborrow before TreeMemoryControls.root TreeReborrowStateControls.reads =
      .ub (.tree .unprotectedLocalReadDisabled) changed ∧
      TreeFactoredMemory.reify changed = TreeReborrowStateControls.partialState ∧
      changed.raw = before.raw ∧ changed.currentFrame = [(42, [3])] := by
  have observed := actual_factored_partial_failure
  cases actual : TreeFactoredMemory.reborrow before TreeMemoryControls.root TreeReborrowStateControls.reads with
  | ok value changed => simp only [actual, TreeFactoredMemory.translate] at observed; cases observed
  | unsupported reason changed =>
    simp only [actual, TreeFactoredMemory.translate] at observed; cases observed
  | noChoice changed => simp only [actual, TreeFactoredMemory.translate] at observed; cases observed
  | ub fault changed =>
    simp only [actual, TreeFactoredMemory.translate] at observed
    obtain ⟨sameFault, sameState⟩ := TreeMemory.Result.ub.inj observed
    subst fault
    refine ⟨changed, rfl, sameState, ?_, ?_⟩
    · exact congrArg TreeMemory.State.raw sameState
    · exact congrArg TreeMemory.State.currentFrame sameState

#print axioms before_reifies
#print axioms before_sized
#print axioms actual_factored_partial_failure
#print axioms actual_factored_cell_success
#print axioms actual_factored_settings_order
#print axioms actual_partial_result_witness

end AnnealResearch.TreeReborrowPairedControls
