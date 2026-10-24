import Std

/-!
A selected two-level logical heap for the fresh, no-collection helper prefix.
Guarded lookup ignores off-frontier cells. Option failure describes an invalid
owned lookup, not an ordinary callback Err, source panic or object-language UB.
Closed typed images are separate from the frontier and arbitrary heap shape.
This is no Rust/GC/helper/generated-code adequacy or physical resource model.
-/

namespace AnnealResearch.HelperValueHeap

inductive Cell where
  | leaf (value : Nat)
  | parent (child : Nat)
  deriving DecidableEq, Repr

structure Heap where
  next : Nat
  cells : Nat → Option Cell

def readCell (heap : Heap) (index : Nat) : Option Cell :=
  if index < heap.next then heap.cells index else none

def readLeaf (heap : Heap) (index : Nat) : Option Nat :=
  match readCell heap index with
  | some (.leaf value) => some value
  | _ => none

def readParent (heap : Heap) (index : Nat) : Option Nat :=
  match readCell heap index with
  | some (.parent child) => readLeaf heap child
  | _ => none

def LeafImage (heap : Heap) (index value : Nat) : Prop :=
  index < heap.next ∧ heap.cells index = some (.leaf value)

def RootImage (heap : Heap) (root value : Nat) : Prop :=
  ∃ child, root < heap.next ∧ child < heap.next ∧
    heap.cells root = some (.parent child) ∧
    heap.cells child = some (.leaf value)

/-- A stronger optional representation condition, not generic source admission. -/
def FrontierEmpty (heap : Heap) : Prop :=
  ∀ index, heap.next ≤ index → heap.cells index = none

/-- Selected append allocation; it does not implement reuse, GC or failure. -/
def allocate (heap : Heap) (cell : Cell) : Nat × Heap :=
  (heap.next, { next := heap.next + 1, cells := fun index =>
    if index = heap.next then some cell else heap.cells index })

def empty : Heap := { next := 0, cells := fun _ => none }

theorem readCell_outside (heap : Heap) (index : Nat)
    (outside : heap.next ≤ index) : readCell heap index = none := by
  simp [readCell, Nat.not_lt.mpr outside]

theorem leaf_image_read (heap : Heap) (index value : Nat)
    (image : LeafImage heap index value) : readLeaf heap index = some value := by
  rcases image with ⟨inside, stored⟩
  simp [readLeaf, readCell, inside, stored]

theorem root_image_read (heap : Heap) (root value : Nat)
    (image : RootImage heap root value) : readParent heap root = some value := by
  rcases image with ⟨child, rootInside, childInside, parentStored, leafStored⟩
  simp [readParent, readLeaf, readCell, rootInside, childInside, parentStored, leafStored]

theorem root_image_tags_distinct (heap : Heap) (root child value : Nat)
    (parentStored : heap.cells root = some (.parent child))
    (leafStored : heap.cells child = some (.leaf value)) : root ≠ child := by
  intro same
  subst child
  rw [parentStored] at leafStored
  cases leafStored

theorem allocate_index (heap : Heap) (cell : Cell) :
    (allocate heap cell).1 = heap.next := rfl

theorem allocate_frontier (heap : Heap) (cell : Cell) :
    (allocate heap cell).2.next = heap.next + 1 := rfl

theorem allocate_new_cell (heap : Heap) (cell : Cell) :
    readCell (allocate heap cell).2 (allocate heap cell).1 = some cell := by
  simp [allocate, readCell]

theorem allocate_old_cell (heap : Heap) (cell : Cell) (index : Nat)
    (inside : index < heap.next) :
    (allocate heap cell).2.cells index = heap.cells index := by
  have different : index ≠ heap.next := by omega
  simp [allocate, different]

theorem allocate_old_read (heap : Heap) (cell : Cell) (index : Nat)
    (inside : index < heap.next) :
    readCell (allocate heap cell).2 index = readCell heap index := by
  have afterInside : index < heap.next + 1 := by omega
  have different : index ≠ heap.next := by omega
  simp [readCell, allocate, inside, afterInside, different]

theorem allocate_leaf_image (heap : Heap) (value : Nat) :
    LeafImage (allocate heap (.leaf value)).2 heap.next value := by
  simp [LeafImage, allocate]

theorem allocate_preserves_leaf_image (heap : Heap) (cell : Cell)
    (index value : Nat) (image : LeafImage heap index value) :
    LeafImage (allocate heap cell).2 index value := by
  rcases image with ⟨inside, stored⟩
  constructor
  · change index < heap.next + 1
    omega
  · rw [allocate_old_cell heap cell index inside]
    exact stored

theorem allocate_preserves_root_image (heap : Heap) (cell : Cell)
    (root value : Nat) (image : RootImage heap root value) :
    RootImage (allocate heap cell).2 root value := by
  rcases image with ⟨child, rootInside, childInside, parentStored, leafStored⟩
  refine ⟨child, ?_, ?_, ?_, ?_⟩
  · change root < heap.next + 1
    omega
  · change child < heap.next + 1
    omega
  · rw [allocate_old_cell heap cell root rootInside]
    exact parentStored
  · rw [allocate_old_cell heap cell child childInside]
    exact leafStored

theorem allocate_preserves_frontier_empty (heap : Heap) (cell : Cell)
    (noFuture : FrontierEmpty heap) : FrontierEmpty (allocate heap cell).2 := by
  intro index outside
  have beyond : heap.next ≤ index := by
    change heap.next + 1 ≤ index at outside
    omega
  have different : index ≠ heap.next := by
    change heap.next + 1 ≤ index at outside
    omega
  simpa [allocate, different] using noFuture index beyond

theorem empty_frontier_empty : FrontierEmpty empty := by
  intro index _
  rfl

#print axioms readCell_outside
#print axioms leaf_image_read
#print axioms root_image_read
#print axioms root_image_tags_distinct
#print axioms allocate_index
#print axioms allocate_frontier
#print axioms allocate_new_cell
#print axioms allocate_old_cell
#print axioms allocate_old_read
#print axioms allocate_leaf_image
#print axioms allocate_preserves_leaf_image
#print axioms allocate_preserves_root_image
#print axioms allocate_preserves_frontier_empty
#print axioms empty_frontier_empty

end AnnealResearch.HelperValueHeap
