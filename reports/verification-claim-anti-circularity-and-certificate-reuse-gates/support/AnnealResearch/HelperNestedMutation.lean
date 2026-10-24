import AnnealResearch.HelperValueHeap

/-!
Selected two-level clone/callback/allocate/install mutation. The leaf callback
is a pure Nat -> Nat × α function; α is opaque and is never inspected. An
ordinary error-valued α still passes through both installations. Option none
is a separate invalid selected lookup/body boundary, not callback Err or Rust UB.

Allocation/lookups and their image facts are shared with HelperValueHeap.
The expected heap is a direct independent record expression. Old alias laws
apply only to closed typed images; arbitrary dangling parent observations can
change under extension. No Rust/helper/GC/generated-code adequacy, arbitrary
Clone/callback effects, collection/reuse/failure, or physical cost is claimed.
-/

namespace AnnealResearch.HelperNestedMutation

open HelperValueHeap

structure Outcome (α : Type) where
  output : α
  receiver : Nat
  heap : Heap

def mutateLeaf (heap : Heap) (handle : Nat) (callback : Nat → Nat × α) :
    Option (Outcome α) :=
  match readLeaf heap handle with
  | none => none
  | some value =>
      let returned := callback value
      let fresh := allocate heap (.leaf returned.1)
      some { output := returned.2, receiver := fresh.1, heap := fresh.2 }

/-- The body runs on the actual child and heap; installation uses its actual
returned heap and receiver even if its opaque output is an ordinary error.
An arbitrary body need not preserve old cells: only nested's pure leaf body
has the closed-image preservation theorems below. -/
def mutateParent (heap : Heap) (root : Nat)
    (body : Heap → Nat → Option (Outcome α)) : Option (Outcome α) :=
  match readCell heap root with
  | some (.parent child) =>
      match body heap child with
      | none => none
      | some actual =>
          let fresh := allocate actual.heap (.parent actual.receiver)
          some { output := actual.output, receiver := fresh.1, heap := fresh.2 }
  | _ => none

def nested (heap : Heap) (root : Nat) (callback : Nat → Nat × α) :
    Option (Outcome α) :=
  mutateParent heap root (fun current child => mutateLeaf current child callback)

/-- Written directly, without invoking either mutation or allocation. Only the
two newly represented cells differ from the input total store. -/
def expectedHeap (heap : Heap) (changed : Nat) : Heap :=
  { next := heap.next + 2
    cells := fun index =>
      if index = heap.next + 1 then some (.parent heap.next)
      else if index = heap.next then some (.leaf changed)
      else heap.cells index }

def expected (heap : Heap) (changed : Nat) (output : α) : Outcome α :=
  { output, receiver := heap.next + 1, heap := expectedHeap heap changed }

theorem expectedHeap_eq_allocations (heap : Heap) (changed : Nat) :
    expectedHeap heap changed =
      (allocate (allocate heap (.leaf changed)).2 (.parent heap.next)).2 := rfl

theorem expectedHeap_frontier (heap : Heap) (changed : Nat) :
    (expectedHeap heap changed).next = heap.next + 2 := rfl

theorem expectedHeap_old_cell (heap : Heap) (changed index : Nat)
    (inside : index < heap.next) :
    (expectedHeap heap changed).cells index = heap.cells index := by
  have notParent : index ≠ heap.next + 1 := by omega
  have notLeaf : index ≠ heap.next := by omega
  simp only [expectedHeap, notParent, notLeaf, ite_false]

theorem expected_root_image (heap : Heap) (changed : Nat) :
    RootImage (expectedHeap heap changed) (heap.next + 1) changed := by
  refine ⟨heap.next, ?_, ?_, ?_, ?_⟩
  · change heap.next + 1 < heap.next + 2
    omega
  · change heap.next < heap.next + 2
    omega
  · simp [expectedHeap]
  · simp [expectedHeap]

theorem expected_active_value (heap : Heap) (changed : Nat) :
    readParent (expectedHeap heap changed) (heap.next + 1) = some changed :=
  root_image_read _ _ _ (expected_root_image heap changed)

theorem expected_preserves_leaf_image (heap : Heap) (changed index value : Nat)
    (image : LeafImage heap index value) :
    LeafImage (expectedHeap heap changed) index value := by
  rw [expectedHeap_eq_allocations]
  exact allocate_preserves_leaf_image _ (.parent heap.next) index value
    (allocate_preserves_leaf_image heap (.leaf changed) index value image)

theorem expected_preserves_root_image (heap : Heap) (changed root value : Nat)
    (image : RootImage heap root value) :
    RootImage (expectedHeap heap changed) root value := by
  rw [expectedHeap_eq_allocations]
  exact allocate_preserves_root_image _ (.parent heap.next) root value
    (allocate_preserves_root_image heap (.leaf changed) root value image)

theorem expected_preserves_leaf_value (heap : Heap) (changed index value : Nat)
    (image : LeafImage heap index value) :
    readLeaf (expectedHeap heap changed) index = some value :=
  leaf_image_read _ _ _ (expected_preserves_leaf_image heap changed index value image)

theorem expected_preserves_root_value (heap : Heap) (changed root value : Nat)
    (image : RootImage heap root value) :
    readParent (expectedHeap heap changed) root = some value :=
  root_image_read _ _ _ (expected_preserves_root_image heap changed root value image)

theorem expected_preserves_frontier_empty (heap : Heap) (changed : Nat)
    (noFuture : FrontierEmpty heap) : FrontierEmpty (expectedHeap heap changed) := by
  rw [expectedHeap_eq_allocations]
  exact allocate_preserves_frontier_empty _ (.parent heap.next)
    (allocate_preserves_frontier_empty heap (.leaf changed) noFuture)

theorem mutateLeaf_exact (heap : Heap) (handle value : Nat) (callback : Nat → Nat × α)
    (image : LeafImage heap handle value) :
    mutateLeaf heap handle callback = some
      { output := (callback value).2
        receiver := heap.next
        heap := (allocate heap (.leaf (callback value).1)).2 } := by
  simp only [mutateLeaf, leaf_image_read heap handle value image] <;> rfl

/-- The successful body equation is an observed local result, not admission
for nested_exact. No preservation is asserted for an arbitrary supplied body. -/
theorem mutateParent_exact (heap : Heap) (root child : Nat)
    (body : Heap → Nat → Option (Outcome α)) (actual : Outcome α)
    (inside : root < heap.next) (stored : heap.cells root = some (.parent child))
    (observed : body heap child = some actual) :
    mutateParent heap root body = some
      { output := actual.output
        receiver := actual.heap.next
        heap := (allocate actual.heap (.parent actual.receiver)).2 } := by
  simp only [mutateParent, readCell, inside, ite_true, stored, observed] <;> rfl

/-- Sole entry condition: actual closed typed root/child image. Callback values
and outputs are arbitrary; no successful-output or global heap-WF premise. -/
theorem nested_exact (heap : Heap) (root value : Nat) (callback : Nat → Nat × α)
    (image : RootImage heap root value) :
    nested heap root callback =
      some (expected heap (callback value).1 (callback value).2) := by
  rcases image with ⟨child, rootInside, childInside, parentStored, leafStored⟩
  have rootRead : readCell heap root = some (.parent child) := by
    simp only [readCell, rootInside, ite_true, parentStored]
  have leafRead : readLeaf heap child = some value :=
    leaf_image_read heap child value ⟨childInside, leafStored⟩
  simp only [nested, mutateParent, rootRead, mutateLeaf, leafRead] <;> rfl

/-- The actual returned outcome has the changed active value, exact output,
and all initially closed old alias images/values. No arbitrary-parent law. -/
theorem nested_observations (heap : Heap) (root value : Nat) (callback : Nat → Nat × α)
    (image : RootImage heap root value) :
    ∃ actual, nested heap root callback = some actual ∧
      actual.output = (callback value).2 ∧
      RootImage actual.heap actual.receiver (callback value).1 ∧
      readParent actual.heap actual.receiver = some (callback value).1 ∧
      readParent actual.heap root = some value ∧
      (∀ oldRoot oldValue, RootImage heap oldRoot oldValue →
        RootImage actual.heap oldRoot oldValue ∧
          readParent actual.heap oldRoot = some oldValue) ∧
      (∀ oldLeaf oldValue, LeafImage heap oldLeaf oldValue →
        LeafImage actual.heap oldLeaf oldValue ∧
          readLeaf actual.heap oldLeaf = some oldValue) := by
  refine ⟨expected heap (callback value).1 (callback value).2,
    nested_exact heap root value callback image, rfl,
    expected_root_image heap (callback value).1,
    expected_active_value heap (callback value).1,
    expected_preserves_root_value heap (callback value).1 root value image, ?_, ?_⟩
  · intro oldRoot oldValue oldImage
    exact ⟨expected_preserves_root_image heap (callback value).1 oldRoot oldValue oldImage,
      expected_preserves_root_value heap (callback value).1 oldRoot oldValue oldImage⟩
  · intro oldLeaf oldValue oldImage
    exact ⟨expected_preserves_leaf_image heap (callback value).1 oldLeaf oldValue oldImage,
      expected_preserves_leaf_value heap (callback value).1 oldLeaf oldValue oldImage⟩

/-- Ordinary Err is an opaque callback output, so both fresh installations
remain in the actual selected heap. The callback equation is a result observation. -/
theorem nested_error_exact {ε β : Type} (heap : Heap) (root value changed : Nat)
    (callback : Nat → Nat × Except ε β) (error : ε)
    (image : RootImage heap root value)
    (returned : callback value = (changed, .error error)) :
    nested heap root callback =
      some (expected heap changed (Except.error error : Except ε β)) := by
  simpa only [returned] using nested_exact heap root value callback image

theorem nested_error_retains {ε β : Type} (heap : Heap) (root value changed : Nat)
    (callback : Nat → Nat × Except ε β) (error : ε)
    (image : RootImage heap root value)
    (returned : callback value = (changed, .error error)) :
    ∃ actual, nested heap root callback = some actual ∧
      actual.output = .error error ∧
      readParent actual.heap actual.receiver = some changed ∧
      readParent actual.heap root = some value ∧
      (∀ oldLeaf oldValue, LeafImage heap oldLeaf oldValue →
        readLeaf actual.heap oldLeaf = some oldValue) := by
  refine ⟨expected heap changed (Except.error error : Except ε β),
    nested_error_exact heap root value changed callback error image returned,
    rfl, expected_active_value heap changed,
    expected_preserves_root_value heap changed root value image, ?_⟩
  intro oldLeaf oldValue oldImage
  exact expected_preserves_leaf_value heap changed oldLeaf oldValue oldImage

#print axioms expectedHeap_eq_allocations
#print axioms expectedHeap_frontier
#print axioms expectedHeap_old_cell
#print axioms expected_root_image
#print axioms expected_active_value
#print axioms expected_preserves_leaf_image
#print axioms expected_preserves_root_image
#print axioms expected_preserves_leaf_value
#print axioms expected_preserves_root_value
#print axioms expected_preserves_frontier_empty
#print axioms mutateLeaf_exact
#print axioms mutateParent_exact
#print axioms nested_exact
#print axioms nested_observations
#print axioms nested_error_exact
#print axioms nested_error_retains

end AnnealResearch.HelperNestedMutation
