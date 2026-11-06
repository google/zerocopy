import AnnealResearch.TreeUnprotectTotal
import AnnealResearch.TreeValidated

/-!
Unconditional geometry/array-width preservation for all owned unprotect
outcomes, followed by output-list accounting on an actual success equation.
Uniform width is structural allocation geometry, not permission-kind matching,
scalar access success or NoUB. Missing paths and failed complete-list conversion
are retained as actual unsupported outcomes and satisfy the same preservation.
-/

namespace AnnealResearch.TreeUnprotectWidths

open TreePermissions
open TreeFactored (Path Topology Forest Entry Store State)

mutual
  theorem arrayLengthsTree_congr_lengths (topology : Topology) (here : Path)
      (first second : Store) (width : Nat)
      (lengths : ∀ query, (first query).permissions.length = (second query).permissions.length) :
      TreeFactored.arrayLengthsTree topology here first width =
        TreeFactored.arrayLengthsTree topology here second width := by
    cases topology with
    | node children =>
        simp only [TreeFactored.arrayLengthsTree]
        rw [lengths here, arrayLengthsForest_congr_lengths children here 0 first second width lengths]
  termination_by structural topology

  theorem arrayLengthsForest_congr_lengths (children : Forest) (parent : Path) (index : Nat)
      (first second : Store) (width : Nat)
      (lengths : ∀ query, (first query).permissions.length = (second query).permissions.length) :
      TreeFactored.arrayLengthsForest children parent index first width =
        TreeFactored.arrayLengthsForest children parent index second width := by
    cases children with
    | nil => simp only [TreeFactored.arrayLengthsForest]
    | cons child rest =>
        simp only [TreeFactored.arrayLengthsForest]
        rw [arrayLengthsTree_congr_lengths child (parent ++ [index]) first second width lengths,
          arrayLengthsForest_congr_lengths rest parent (index + 1) first second width lengths]
  termination_by structural children
end

/-- Every outcome preserves topology and every store cell's permission-list
length. This includes the unchanged states on missing-path/flag/map failures. -/
theorem unprotectAt_geometry (state : State) (path : Path) :
    (TreeFactored.unprotectAt state path).residual.topology = state.topology ∧
      ∀ query,
        ((TreeFactored.unprotectAt state path).residual.store query).permissions.length =
          (state.store query).permissions.length := by
  unfold TreeFactored.unprotectAt
  cases TreeFactored.findTopology state.topology path with
  | none => exact ⟨rfl, fun _ => rfl⟩
  | some selected =>
      cases flag : (state.store path).protection.yes with
      | false => exact ⟨rfl, fun _ => rfl⟩
      | true =>
          cases converted : TreeFactored.unprotectPermissions (state.store path).permissions with
          | none => exact ⟨rfl, fun _ => rfl⟩
          | some pair =>
              rcases pair with ⟨permissions, accesses⟩
              have lengths := TreeUnprotect.unprotectPermissions_lengths
                (state.store path).permissions permissions accesses converted
              refine ⟨rfl, ?_⟩
              intro query
              by_cases same : query = path
              · subst query
                change (TreeFactored.setPermissions state.store path permissions path).permissions.length =
                  (state.store path).permissions.length
                rw [(TreeOperations.setPermissions_here state.store path permissions).1]
                exact lengths.1
              · change (TreeFactored.setPermissions state.store path permissions query).permissions.length =
                  (state.store query).permissions.length
                rw [TreeOperations.setPermissions_other state.store path query permissions same]

/-- Stronger than a true-to-true invariant: every width query keeps its value,
even for an initially malformed array domain and an unsupported operation. -/
theorem unprotectAt_arrayLengths (state : State) (path : Path) (width : Nat) :
    TreeFactored.arrayLengthsTree (TreeFactored.unprotectAt state path).residual.topology []
        (TreeFactored.unprotectAt state path).residual.store width =
      TreeFactored.arrayLengthsTree state.topology [] state.store width := by
  obtain ⟨sameTopology, lengths⟩ := unprotectAt_geometry state path
  rw [sameTopology]
  exact arrayLengthsTree_congr_lengths state.topology []
    (TreeFactored.unprotectAt state path).residual.store state.store width lengths

theorem unprotectAt_preserves_uniform (state : State) (path : Path) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeFactored.arrayLengthsTree (TreeFactored.unprotectAt state path).residual.topology []
      (TreeFactored.unprotectAt state path).residual.store width = true := by
  rw [unprotectAt_arrayLengths]
  exact uniform

theorem uniform_forest_get (children : Forest) (parent : Path) (start : Nat)
    (store : Store) (width relative : Nat) (child : Topology)
    (uniform : TreeFactored.arrayLengthsForest children parent start store width = true)
    (found : children.get? relative = some child) :
    TreeFactored.arrayLengthsTree child (parent ++ [start + relative]) store width = true := by
  induction relative generalizing children start with
  | zero =>
      cases children with
      | nil => cases found
      | cons first rest =>
          have same : first = child := by
            simpa only [TreeFactored.Forest.get?, Option.some.injEq] using found
          subst child
          have parts :
              TreeFactored.arrayLengthsTree first (parent ++ [start]) store width = true ∧
                TreeFactored.arrayLengthsForest rest parent (start + 1) store width = true := by
            simpa [TreeFactored.arrayLengthsForest] using uniform
          simpa only [Nat.add_zero] using parts.1
  | succ relative ih =>
      cases children with
      | nil => cases found
      | cons first rest =>
          have parts :
              TreeFactored.arrayLengthsTree first (parent ++ [start]) store width = true ∧
                TreeFactored.arrayLengthsForest rest parent (start + 1) store width = true := by
            simpa [TreeFactored.arrayLengthsForest] using uniform
          have below : rest.get? relative = some child := by
            simpa only [TreeFactored.Forest.get?] using found
          have increment : start + 1 + relative = start + (relative + 1) := by omega
          simpa only [increment] using ih rest (start + 1) parts.2 below

theorem uniform_find_entry_width (topology : Topology) (here : Path) (store : Store)
    (width : Nat) (path : Path) (selected : Topology)
    (uniform : TreeFactored.arrayLengthsTree topology here store width = true)
    (found : TreeFactored.findTopology topology path = some selected) :
    (store (here ++ path)).permissions.length = width := by
  induction path generalizing topology here with
  | nil =>
      simpa only [List.append_nil] using
        TreeValidated.uniform_root_width topology here store width uniform
  | cons index rest ih =>
      cases topology with
      | node children =>
          cases childFound : children.get? index with
          | none =>
              simp only [TreeFactored.findTopology, childFound] at found
              cases found
          | some child =>
              have parts : (store here).permissions.length = width ∧
                  TreeFactored.arrayLengthsForest children here 0 store width = true := by
                simpa [TreeFactored.arrayLengthsTree] using uniform
              have childUniform :
                  TreeFactored.arrayLengthsTree child (here ++ [index]) store width = true := by
                simpa only [Nat.zero_add] using
                  uniform_forest_get children here 0 store width index child parts.2 childFound
              have below : TreeFactored.findTopology child rest = some selected := by
                simpa only [TreeFactored.findTopology, childFound] using found
              simpa only [List.append_assoc, List.singleton_append] using
                ih child (here ++ [index]) childUniform below

/-- The success equation is an output observation, used only to recover the
actual returned list's length. It does not admit or filter the correspondence. -/
theorem unprotectAt_success_access_length (state : State) (path : Path) (width : Nat)
    (accesses : List (Option AccessKind)) (changed : State)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (success : TreeFactored.unprotectAt state path = .ok accesses changed) :
    accesses.length = width := by
  cases found : TreeFactored.findTopology state.topology path with
  | none =>
      simp only [TreeFactored.unprotectAt, found] at success
      cases success
  | some selected =>
      have selectedWidth : (state.store path).permissions.length = width := by
        simpa only [List.nil_append] using
          uniform_find_entry_width state.topology [] state.store width path selected uniform found
      cases flag : (state.store path).protection.yes with
      | false =>
          simp only [TreeFactored.unprotectAt, found, flag, Bool.false_eq_true, ↓reduceIte] at success
          cases success
      | true =>
          cases converted : TreeFactored.unprotectPermissions (state.store path).permissions with
          | none =>
              simp only [TreeFactored.unprotectAt, found, flag, ↓reduceIte, converted] at success
              cases success
          | some pair =>
              rcases pair with ⟨permissions, returned⟩
              have values : returned = accesses ∧
                  { state with store := TreeFactored.setPermissions state.store path permissions } =
                    changed := by
                simpa only [TreeFactored.unprotectAt, found, flag, ↓reduceIte, converted,
                  TreeFactored.Result.ok.injEq] using success
              rw [← values.1]
              exact (TreeUnprotect.unprotectPermissions_lengths (state.store path).permissions
                permissions returned converted).2.trans selectedWidth

theorem unprotectAt_success_uniform (state : State) (path : Path) (width : Nat)
    (accesses : List (Option AccessKind)) (changed : State)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (success : TreeFactored.unprotectAt state path = .ok accesses changed) :
    TreeFactored.arrayLengthsTree changed.topology [] changed.store width = true := by
  have preserved := unprotectAt_preserves_uniform state path width uniform
  rw [success] at preserved
  exact preserved

#print axioms arrayLengthsTree_congr_lengths
#print axioms arrayLengthsForest_congr_lengths
#print axioms unprotectAt_geometry
#print axioms unprotectAt_arrayLengths
#print axioms unprotectAt_preserves_uniform
#print axioms uniform_forest_get
#print axioms uniform_find_entry_width
#print axioms unprotectAt_success_access_length
#print axioms unprotectAt_success_uniform

end AnnealResearch.TreeUnprotectWidths
