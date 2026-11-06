import AnnealResearch.HelperNestedMutation

/-!
Actual normal/error executions and fixed value-based alternatives for the
selected helper heap. Ordinary callback errors are data, not lookup failure.
The dangling-image control is mathematical, without a claimed source history.
Private index differences alone do not supply either mutation discriminator.
-/

namespace AnnealResearch.HelperValueControls

open HelperValueHeap HelperNestedMutation

/-- Separately written initial store, with inert numeric/handle payloads. -/
def fixture (value : Nat) : Heap :=
  { next := 2, cells := fun index =>
    if index = 1 then some (.parent 0)
    else if index = 0 then some (.leaf value) else none }

/-- An actual fresh-allocation construction from empty, with returned handles. -/
def seed (value : Nat) : Nat × Heap :=
  let (leaf, afterLeaf) := allocate empty (.leaf value)
  allocate afterLeaf (.parent leaf)

theorem seed_eq (value : Nat) : seed value = (1, fixture value) := rfl

theorem fixture_image (value : Nat) : RootImage (fixture value) 1 value := by
  refine ⟨0, ?_, ?_, ?_, ?_⟩
  · change 1 < 2
    decide
  · change 0 < 2
    decide
  · simp [fixture]
  · simp [fixture]

theorem fixture_frontier_empty (value : Nat) : FrontierEmpty (fixture value) := by
  intro index outside
  change 2 ≤ index at outside
  have nonzero : index ≠ 0 := by omega
  have notOne : index ≠ 1 := by omega
  simp [fixture, notOne, nonzero]

def normalCallback (value : Nat) : Nat × Except Nat Nat := (value + 1, .ok 7)
def errorCallback (value : Nat) : Nat × Except Nat Nat := (value + 1, .error 42)

theorem actual_normal (value : Nat) :
    nested (fixture value) 1 normalCallback =
      some (expected (fixture value) (value + 1) (Except.ok 7 : Except Nat Nat)) := by
  exact nested_exact (fixture value) 1 value normalCallback (fixture_image value)

theorem actual_error (value : Nat) :
    nested (fixture value) 1 errorCallback =
      some (expected (fixture value) (value + 1) (Except.error 42 : Except Nat Nat)) := by
  exact nested_exact (fixture value) 1 value errorCallback (fixture_image value)

/-- On Ok the alternative actually performs both allocations; Err rolls back
both commits and keeps the original active receiver and heap. -/
def commitOnlyOnOk {E A : Type} (heap : Heap) (root : Nat)
    (callback : Nat → Nat × Except E A) : Option (Outcome (Except E A)) :=
  match readParent heap root with
  | none => none
  | some value =>
      let (changed, output) := callback value
      match output with
      | .error fault => some ⟨.error fault, root, heap⟩
      | .ok result =>
          let (leaf, afterLeaf) := allocate heap (.leaf changed)
          let (parent, afterParent) := allocate afterLeaf (.parent leaf)
          some ⟨.ok result, parent, afterParent⟩

def overwriteLeaf (heap : Heap) (child changed : Nat) : Heap :=
  { next := heap.next, cells := fun index =>
    if index = child then some (.leaf changed) else heap.cells index }

/-- This alternative mutates the historical leaf, retaining the old handles. -/
def overwriteInPlace {A : Type} (heap : Heap) (root : Nat)
    (callback : Nat → Nat × A) : Option (Outcome A) :=
  match readCell heap root with
  | some (.parent child) =>
      match readLeaf heap child with
      | none => none
      | some value =>
          let (changed, output) := callback value
          some ⟨output, root, overwriteLeaf heap child changed⟩
  | _ => none

/-- Independent explicit endpoint for the in-place fixture execution. -/
def overwrittenFixture (value : Nat) : Heap :=
  { next := 2, cells := fun index =>
    if index = 0 then some (.leaf (value + 1)) else (fixture value).cells index }

theorem rollback_normal (value : Nat) :
    commitOnlyOnOk (fixture value) 1 normalCallback =
      some (expected (fixture value) (value + 1) (Except.ok 7 : Except Nat Nat)) := by
  rfl

theorem rollback_error (value : Nat) :
    commitOnlyOnOk (fixture value) 1 errorCallback =
      some (Outcome.mk (Except.error 42 : Except Nat Nat) 1 (fixture value)) := by
  simp [commitOnlyOnOk, readParent, readLeaf, readCell, fixture, errorCallback]

theorem overwrite_error (value : Nat) :
    overwriteInPlace (fixture value) 1 errorCallback =
      some (Outcome.mk (Except.error 42 : Except Nat Nat) 1 (overwrittenFixture value)) := by
  rfl

theorem rollback_discriminator (value : Nat) :
    ∃ actual alternative : Outcome (Except Nat Nat),
      nested (fixture value) 1 errorCallback = some actual ∧
      commitOnlyOnOk (fixture value) 1 errorCallback = some alternative ∧
      actual.output = alternative.output ∧
      readParent actual.heap actual.receiver = some (value + 1) ∧
      readParent alternative.heap alternative.receiver = some value ∧
      readParent actual.heap actual.receiver ≠
        readParent alternative.heap alternative.receiver := by
  refine ⟨expected (fixture value) (value + 1) (.error 42),
    ⟨.error 42, 1, fixture value⟩, actual_error value, rollback_error value,
    rfl, ?_, ?_, ?_⟩
  · simp [expected, expectedHeap, fixture, readParent, readLeaf, readCell]
  · simp [fixture, readParent, readLeaf, readCell]
  · simp [expected, expectedHeap, fixture, readParent, readLeaf, readCell]

theorem overwrite_discriminator (value : Nat) :
    ∃ actual alternative : Outcome (Except Nat Nat),
      nested (fixture value) 1 errorCallback = some actual ∧
      overwriteInPlace (fixture value) 1 errorCallback = some alternative ∧
      actual.output = alternative.output ∧
      readParent actual.heap actual.receiver =
        readParent alternative.heap alternative.receiver ∧
      readParent actual.heap 1 = some value ∧
      readParent alternative.heap 1 = some (value + 1) ∧
      readLeaf actual.heap 0 = some value ∧
      readLeaf alternative.heap 0 = some (value + 1) ∧
      readParent actual.heap 1 ≠ readParent alternative.heap 1 := by
  refine ⟨expected (fixture value) (value + 1) (.error 42),
    ⟨.error 42, 1, overwrittenFixture value⟩, actual_error value, overwrite_error value,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [expected, expectedHeap, fixture, overwrittenFixture,
    readParent, readLeaf, readCell]

/-- Frontier shape without a closed typed parent image. -/
def dangling : Heap :=
  { next := 1, cells := fun index => if index = 0 then some (.parent 1) else none }

theorem dangling_frontier_empty : FrontierEmpty dangling := by
  intro index outside
  change 1 ≤ index at outside
  have nonzero : index ≠ 0 := by omega
  simp [dangling, nonzero]

theorem dangling_not_image (value : Nat) : ¬ RootImage dangling 0 value := by
  intro image
  rcases image with ⟨child, _, inside, parentStored, _⟩
  have childEq : 1 = child := by simpa [dangling] using parentStored
  change child < 1 at inside
  omega

theorem dangling_boundary (value : Nat) :
    readParent dangling 0 = none ∧
    readParent (allocate dangling (.leaf value)).2 0 = some value ∧
    (allocate dangling (.leaf value)).2.cells 0 = dangling.cells 0 := by
  simp [readParent, readLeaf, readCell, allocate, dangling]

#print axioms seed_eq
#print axioms fixture_image
#print axioms fixture_frontier_empty
#print axioms actual_normal
#print axioms actual_error
#print axioms rollback_normal
#print axioms rollback_error
#print axioms overwrite_error
#print axioms rollback_discriminator
#print axioms overwrite_discriminator
#print axioms dangling_frontier_empty
#print axioms dangling_not_image
#print axioms dangling_boundary

end AnnealResearch.HelperValueControls
