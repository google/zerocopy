import AnnealResearch.TreeMemoryDomain
import AnnealResearch.TreeTraversalGeometryPublic
import AnnealResearch.TreeMemoryAgreement

/-!
Closure of the existing WellSized domain under every actual returned outcome
of the four frozen factored-memory primitives. The domain imposes only array
width at actual paired raw/tree records, including dead records. No StateWF,
liveness, valid path, scalar-success, byte restriction, kind matching or NoUB
premise is added. Release's committed error residuals are included explicitly.
-/

namespace AnnealResearch.TreeMemoryPreservation

open TreePermissions
open TreeFactoredMemory (State Pointer Path Tree Provenance)
open TreeMemoryDomain (ResultWellSized)

/-- Shared proof of the existing load/store hook commit cases, not a runner.
Every tree result is retained: success commits; failure rolls back. -/
theorem access_commit_preserves (state : State) (id : Nat) (path : Path) (tree : Tree)
    (raw : MiniRustReference.State) (value : A) (kind : AccessKind) (offset size : Nat)
    (sized : TreeFactoredMemory.WellSized state) (present : state.trees id = some tree)
    (rawSizes : TreeRawGeometry.SameSizeMap state.raw raw) :
    ResultWellSized
      (match TreeFactored.access tree path kind offset size with
      | .ok () changed => TreeFactoredMemory.Result.ok value
          { TreeFactoredMemory.setTree state id changed with raw }
      | .ub fault _ => .ub (.tree fault) state
      | .unsupported reason _ => .unsupported
          (.tree (TreeCorrespondence.structuralToReference reason)) state) := by
  have geometry := TreeTraversalGeometry.access_geometry tree path kind offset size
  cases acted : TreeFactored.access tree path kind offset size with
  | ok result changed =>
    cases result
    have same : TreeMemoryDomain.SameTreeGeometry tree changed := by
      simpa only [acted, TreeFactored.Result.residual,
        TreeTraversalGeometry.Geometry, TreeTraversalGeometry.SameLengths,
        TreeMemoryDomain.SameTreeGeometry] using geometry
    exact TreeMemoryDomain.wellSized_commit state id tree changed raw sized present same rawSizes
  | ub fault changed => exact sized
  | unsupported reason changed => exact sized

theorem load_preserves (state : State) (pointer : Pointer) (size align : Nat)
    (sized : TreeFactoredMemory.WellSized state) :
    ResultWellSized (TreeFactoredMemory.load state pointer size align) := by
  unfold TreeMemoryDomain.ResultWellSized TreeFactoredMemory.load
  cases loaded : MiniRustReference.load state.raw pointer.basic size align with
  | ub fault => exact sized
  | unsupported => exact sized
  | noChoice => exact sized
  | ok proposed =>
    rcases proposed with ⟨bytes, raw⟩
    have rawSizes := TreeRawGeometry.load_preserves_sizeMap loaded
    by_cases zero : size = 0
    · simp only [ite_eq_left zero, TreeFactoredMemory.Result.residual]
      exact TreeMemoryDomain.wellSized_with_raw state raw sized rawSizes
    · simp only [ite_eq_right zero]
      cases checked : MiniRustReference.checkPtr state.raw pointer.basic size with
      | ub fault => exact sized
      | unsupported => exact sized
      | noChoice => exact sized
      | ok maybeSpan =>
        cases maybeSpan with
        | none => exact sized
        | some span =>
          cases target : TreeFactoredMemory.hookTarget state pointer with
          | none => exact sized
          | some selected =>
            rcases selected with ⟨id, path, tree⟩
            have present := (TreeMemoryAgreement.hookTarget_fields state pointer id path tree target).2
            exact access_commit_preserves state id path tree raw bytes .read span.offset size
              sized present rawSizes

theorem store_preserves (state : State) (pointer : Pointer) (bytes : List MiniRustReference.Byte)
    (align : Nat) (sized : TreeFactoredMemory.WellSized state) :
    ResultWellSized (TreeFactoredMemory.store state pointer bytes align) := by
  unfold TreeMemoryDomain.ResultWellSized TreeFactoredMemory.store
  cases proposed : MiniRustReference.store state.raw pointer.basic bytes align with
  | ub fault => exact sized
  | unsupported => exact sized
  | noChoice => exact sized
  | ok raw =>
    have rawSizes := TreeRawGeometry.store_preserves_sizeMap proposed
    by_cases zero : bytes.length = 0
    · simp only [ite_eq_left zero, TreeFactoredMemory.Result.residual]
      exact TreeMemoryDomain.wellSized_with_raw state raw sized rawSizes
    · simp only [ite_eq_right zero]
      cases checked : MiniRustReference.checkPtr state.raw pointer.basic bytes.length with
      | ub fault => exact sized
      | unsupported => exact sized
      | noChoice => exact sized
      | ok maybeSpan =>
        cases maybeSpan with
        | none => exact sized
        | some span =>
          cases target : TreeFactoredMemory.hookTarget state pointer with
          | none => exact sized
          | some selected =>
            rcases selected with ⟨id, path, tree⟩
            have present := (TreeMemoryAgreement.hookTarget_fields state pointer id path tree target).2
            exact access_commit_preserves state id path tree raw () .write span.offset bytes.length
              sized present rawSizes

theorem deallocate_preserves (state : State) (pointer : Pointer) (kind : MiniRustReference.Kind)
    (size align : Nat) (sized : TreeFactoredMemory.WellSized state) :
    ResultWellSized (TreeFactoredMemory.deallocate state pointer kind size align) := by
  unfold TreeMemoryDomain.ResultWellSized TreeFactoredMemory.deallocate
  cases freed : MiniRustReference.free state.raw pointer.basic kind size align with
  | ub fault => exact sized
  | unsupported => exact sized
  | noChoice => exact sized
  | ok raw =>
    have rawSizes := TreeRawGeometry.free_preserves_sizeMap freed
    cases target : TreeFactoredMemory.hookTarget state pointer with
    | none => exact sized
    | some selected =>
      rcases selected with ⟨id, path, tree⟩
      dsimp only
      have present := (TreeMemoryAgreement.hookTarget_fields state pointer id path tree target).2
      have geometry := TreeTraversalGeometry.access_geometry tree path .write 0 size
      cases acted : TreeFactored.access tree path .write 0 size with
      | ub fault changed => exact sized
      | unsupported reason changed => exact sized
      | ok result changed =>
        cases result
        dsimp only
        have same : TreeMemoryDomain.SameTreeGeometry tree changed := by
          simpa only [acted, TreeFactored.Result.residual,
            TreeTraversalGeometry.Geometry, TreeTraversalGeometry.SameLengths,
            TreeMemoryDomain.SameTreeGeometry] using geometry
        cases TreeFactored.containsStrong changed with
        | false =>
          exact TreeMemoryDomain.wellSized_commit state id tree changed raw sized present same rawSizes
        | true => exact sized

/-- Release uses outer mutation, so every changed conversion/traversal residual
must satisfy the domain. This proof does not replace errors by their input state. -/
theorem release_preserves (state : State) (provenance : Provenance)
    (sized : TreeFactoredMemory.WellSized state) :
    ResultWellSized (TreeFactoredMemory.release state provenance) := by
  rcases provenance with ⟨id, path⟩
  unfold TreeMemoryDomain.ResultWellSized TreeFactoredMemory.release
  dsimp only
  cases rawFound : state.raw.allocations id with
  | none => exact sized
  | some allocation =>
    cases present : state.trees id with
    | none => exact sized
    | some tree =>
      dsimp only
      have geometry := TreeUnprotectWidths.unprotectAt_geometry tree path
      cases converted : TreeFactored.unprotectAt tree path with
      | ub fault changed =>
        have same : TreeMemoryDomain.SameTreeGeometry tree changed := by
          simpa only [converted, TreeFactored.Result.residual,
            TreeMemoryDomain.SameTreeGeometry] using geometry
        exact TreeMemoryDomain.wellSized_replace_tree state id tree changed sized present same
      | unsupported reason changed =>
        have same : TreeMemoryDomain.SameTreeGeometry tree changed := by
          simpa only [converted, TreeFactored.Result.residual,
            TreeMemoryDomain.SameTreeGeometry] using geometry
        exact TreeMemoryDomain.wellSized_replace_tree state id tree changed sized present same
      | ok accesses convertedTree =>
        dsimp only
        have firstGeometry : TreeMemoryDomain.SameTreeGeometry tree convertedTree := by
          simpa only [converted, TreeFactored.Result.residual,
            TreeMemoryDomain.SameTreeGeometry] using geometry
        cases live : allocation.live with
        | false =>
          simp only [Bool.not_false, ↓reduceIte, TreeFactoredMemory.Result.residual]
          exact TreeMemoryDomain.wellSized_replace_tree state id tree convertedTree sized present
            firstGeometry
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have lastGeometry := TreeTraversalGeometry.releaseTraverse_geometry convertedTree path accesses
          cases traversed : TreeFactored.releaseTraverse convertedTree path accesses with
          | ok result changed =>
            cases result
            have secondGeometry : TreeTraversalGeometry.Geometry convertedTree changed := by
              simpa only [traversed, TreeFactored.Result.residual] using lastGeometry
            have combined : TreeMemoryDomain.SameTreeGeometry tree changed :=
              TreeTraversalGeometry.geometry_trans tree convertedTree changed firstGeometry secondGeometry
            exact TreeMemoryDomain.wellSized_replace_tree state id tree changed sized present combined
          | ub fault changed =>
            have secondGeometry : TreeTraversalGeometry.Geometry convertedTree changed := by
              simpa only [traversed, TreeFactored.Result.residual] using lastGeometry
            have combined : TreeMemoryDomain.SameTreeGeometry tree changed :=
              TreeTraversalGeometry.geometry_trans tree convertedTree changed firstGeometry secondGeometry
            exact TreeMemoryDomain.wellSized_replace_tree state id tree changed sized present combined
          | unsupported reason changed =>
            have secondGeometry : TreeTraversalGeometry.Geometry convertedTree changed := by
              simpa only [traversed, TreeFactored.Result.residual] using lastGeometry
            have combined : TreeMemoryDomain.SameTreeGeometry tree changed :=
              TreeTraversalGeometry.geometry_trans tree convertedTree changed firstGeometry secondGeometry
            exact TreeMemoryDomain.wellSized_replace_tree state id tree changed sized present combined

#print axioms access_commit_preserves
#print axioms load_preserves
#print axioms store_preserves
#print axioms deallocate_preserves
#print axioms release_preserves

end AnnealResearch.TreeMemoryPreservation
