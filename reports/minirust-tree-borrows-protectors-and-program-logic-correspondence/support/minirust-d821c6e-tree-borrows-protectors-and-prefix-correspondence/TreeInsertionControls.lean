import AnnealResearch.TreeInitialAgreement

/-!
Concrete nested insertion challenges complete overwrite and ordered framing.
Old total-store cells below the fresh path are deliberately malformed and
nondefault. The new subtree includes a descendant, so copying only its root
would fail these observations. This is a structural fixture, not a claim of
Rust program reachability or a full memory reborrow execution.
-/
namespace AnnealResearch.TreeInsertionControls

open TreePermissions
open TreeFactored

def leaf : Topology := .node .nil

def oldStore : Store
  | [] => ⟨[.unprot .unique], .no⟩
  | [0] => ⟨[.unprot .reserved], .no⟩
  | [1] => ⟨[.unprot .frozen], .no⟩
  | _ => ⟨[.prot .disabled, .prot .disabled], .strong⟩

def before : State := ⟨.node (.cons leaf (.cons leaf .nil)), oldStore⟩

def childStore : Store
  | [] => ⟨[.prot .cell], .strong⟩
  | [0] => ⟨[.unprot .unique], .no⟩
  | _ => ⟨[], .weak⟩

def child : State := ⟨.node (.cons leaf .nil), childStore⟩

def after : State :=
  ⟨.node (.cons (.node (.cons child.topology .nil)) (.cons leaf .nil)),
    fun selected => match stripPrefix [0, 0] selected with
      | none => before.store selected
      | some rest => child.store rest⟩

theorem nested_add_actual : addNode before [0] child = .ok [0, 0] after := by rfl

theorem parent_and_child_uniform :
    arrayLengthsTree before.topology [] before.store 1 = true ∧
      arrayLengthsTree child.topology [] child.store 1 = true := by
  simp [before, child, oldStore, childStore, leaf,
    arrayLengthsTree, arrayLengthsForest]

theorem poisoned_cells_were_absent :
    findTopology before.topology [0, 0] = none ∧
    findTopology before.topology [0, 0, 0] = none ∧
    (before.store [0, 0]).permissions.length = 2 ∧
    (before.store [0, 0, 0]).permissions.length = 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem complete_child_overwrites_poison :
    findTopology after.topology [0, 0] = some child.topology ∧
    findTopology after.topology [0, 0, 0] = some leaf ∧
    after.store [0, 0] = child.store [] ∧
    after.store [0, 0, 0] = child.store [0] ∧
    (after.store [0, 0]).permissions.length = 1 ∧
    (after.store [0, 0, 0]).permissions.length = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ancestors_and_siblings_retained :
    after.store [] = before.store [] ∧
    after.store [0] = before.store [0] ∧
    after.store [1] = before.store [1] ∧
    findTopology after.topology [1] = some leaf := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem nested_exact_reference_equation :
    TreeReference.addNode (TreeCorrespondence.reify before) [0]
        (TreeCorrespondence.reify child) =
      .ok [0, 0] (TreeCorrespondence.reify after) := by
  rw [TreeInsertionAgreement.addNode_agrees before child [0] 1
    parent_and_child_uniform.1 parent_and_child_uniform.2, nested_add_actual]
  rfl

theorem nested_uniform_after : arrayLengthsTree after.topology [] after.store 1 = true := by
  have preserved := TreeInsertionWidths.addNode_preserves_uniform before child [0] 1
    parent_and_child_uniform.1 parent_and_child_uniform.2
  simpa only [nested_add_actual, Result.residual] using preserved

/-- Path rejection remains an ordinary unsupported result under the common
width domain, rather than a valid-path admission premise. -/
theorem missing_parent_actual :
    addNode before [7] child = .unsupported .invalidPath before ∧
    TreeReference.addNode (TreeCorrespondence.reify before) [7]
        (TreeCorrespondence.reify child) =
      .unsupported .invalidPath (TreeCorrespondence.reify before) := by
  refine ⟨rfl, ?_⟩
  rw [TreeInsertionAgreement.addNode_agrees before child [7] 1
    parent_and_child_uniform.1 parent_and_child_uniform.2]
  rfl

#print axioms nested_add_actual
#print axioms parent_and_child_uniform
#print axioms poisoned_cells_were_absent
#print axioms complete_child_overwrites_poison
#print axioms ancestors_and_siblings_retained
#print axioms nested_exact_reference_equation
#print axioms nested_uniform_after
#print axioms missing_parent_actual

end AnnealResearch.TreeInsertionControls
