import AnnealResearch.TreeMemoryAgreement
import AnnealResearch.TreeUnprotectWidths

/-!
Exact full-state protector-release agreement under the fixed WellSized domain.
The allocation record and optional tree are looked up at the actual provenance
ID. Unprotect is total over paths and returns all owned failures. Only after
actual success are converted-array width and returned-list length derived, so
the live traversal correspondence needs no path, scalar-success or NoUB premise.

Dead release commits the converted tree without traversal. Live release commits
conversion and the traversal's returned residual on success, UB or unsupported.
This is the frozen outer-mutation policy, not copied-trial rollback. It does not
prove frame consumption, full exit, source-helper adequacy or Rust semantics.
-/

namespace AnnealResearch.TreeMemoryReleaseAgreement

open TreeFactoredMemory (State Provenance)

/-- Missing allocations/trees/paths, conversion failure, dead conversion, and
live partial traversal all preserve their full owned status and residual state.
Uniform arrays at actual allocation sizes are the sole admission condition. -/
theorem release_agrees (state : State) (provenance : Provenance)
    (sized : TreeFactoredMemory.WellSized state) :
    TreeMemory.release (TreeFactoredMemory.reify state) provenance =
      TreeFactoredMemory.translate (TreeFactoredMemory.release state provenance) := by
  rcases provenance with ⟨id, path⟩
  cases allocationFound : state.raw.allocations id with
  | none =>
      simp only [TreeMemory.release, TreeFactoredMemory.release,
        TreeFactoredMemory.reify, allocationFound, TreeFactoredMemory.translate]
  | some allocation =>
      cases treeFound : state.trees id with
      | none =>
          simp only [TreeMemory.release, TreeFactoredMemory.release,
            TreeFactoredMemory.reify, allocationFound, treeFound, Option.map_none,
            TreeFactoredMemory.translate]
      | some tree =>
          have uniform := sized id allocation tree allocationFound treeFound
          simp only [TreeMemory.release, TreeFactoredMemory.release,
            TreeFactoredMemory.reify, allocationFound, treeFound, Option.map_some]
          rw [TreeUnprotectTotal.unprotectAt_eq_translate tree path]
          cases converted : TreeFactored.unprotectAt tree path with
          | ub fault changed =>
              simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
                TreeFactoredMemory.reify_setTree]
              rfl
          | unsupported reason changed =>
              simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
                TreeFactoredMemory.reify_setTree]
              rfl
          | ok accesses convertedTree =>
              have convertedUniform := TreeUnprotectWidths.unprotectAt_success_uniform
                tree path allocation.size accesses convertedTree uniform converted
              have accessLength := TreeUnprotectWidths.unprotectAt_success_access_length
                tree path allocation.size accesses convertedTree uniform converted
              simp only [TreeAgreement.translate]
              cases live : allocation.live with
              | false =>
                  simp only [Bool.not_false, ↓reduceIte, TreeFactoredMemory.translate,
                    TreeFactoredMemory.reify_setTree]
                  rfl
              | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  rw [TreeValidated.releaseTraverse_at_width convertedTree path accesses
                    allocation.size convertedUniform accessLength]
                  cases TreeFactored.releaseTraverse convertedTree path accesses with
                  | ok value changed =>
                      cases value
                      simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
                        TreeFactoredMemory.reify_setTree]
                      rfl
                  | ub fault changed =>
                      simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
                        TreeFactoredMemory.reify_setTree]
                      rfl
                  | unsupported reason changed =>
                      simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
                        TreeFactoredMemory.reify_setTree]
                      rfl

theorem related_release (reference : TreeMemory.State) (state : State)
    (provenance : Provenance) (related : TreeFactoredMemory.Related reference state)
    (sized : TreeFactoredMemory.WellSized state) :
    TreeMemory.release reference provenance =
      TreeFactoredMemory.translate (TreeFactoredMemory.release state provenance) := by
  rw [related]
  exact release_agrees state provenance sized

#print axioms release_agrees
#print axioms related_release

end AnnealResearch.TreeMemoryReleaseAgreement
