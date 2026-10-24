import AnnealResearch.TreeMemoryControls

/-!
Constructed Cell and zero-size exceptions for the frozen owned source-equation
wrapper. Settings are explicitly supplied selected specializations of the
pinned reborrow_settings.md, not a verified type/layout computation.

Every birth equation executes reborrow, including its original initial-access
list. Expected trees/states are written separately, with no default-success
extraction. The truly empty allocation is distinct from a zero-sized protected
reference into a positive-size allocation. The latter's nonempty outside array
can refute global constructor matching after dead release; the former cannot.

These equations imply no whole Rust execution, all-allocator safety, frame
consumption, helper/generated-code binding, or ISA theorem. Parent compiles.
-/
namespace AnnealResearch.TreeExceptions

open TreePermissions TreeMemory TreeMemoryControls

attribute [local simp] Pointer.basic MiniRustReference.checkPtr MiniRustReference.free
  MiniRustReference.replace TreeReference.addNode TreeReference.modifyAt
  TreeReference.replaceNth TreeReference.arraysSized TreeReference.childrenSized
  TreeReference.initialAccesses TreeReference.access TreeReference.pathPresent
  TreeReference.findNode TreeReference.Node.permissions TreeReference.Node.children
  TreeReference.accessCore TreeReference.accessChildren TreeReference.transitionRange
  TreeReference.transitionPrefix TreeReference.nodeRelation TreeReference.childPath
  TreeReference.Result.mapState TreeReference.Result.bind TreeReference.containsStrong
  TreeReference.childrenContainStrong TreeReference.unprotectAt
  TreeReference.unprotectPermissions TreeReference.releaseTraverse TreeReference.releaseCore
  TreeReference.releaseChildren TreeReference.applyAccesses TreeReference.Node.protection
  TreeReference.kindsMatch TreeReference.childrenMatch Permission.transition
  Permission.initAccess Permission.matchesProtector Permission.isProt
  Permission.preventsDeallocation Permission.unprotect Protected.yes
  UPermission.transition UPermission.localRead UPermission.localWrite
  UPermission.foreignRead UPermission.foreignWrite UPermission.initAccess
  UPermission.preventsDeallocation PPermission.transition PPermission.localRead
  PPermission.localWrite PPermission.foreignRead PPermission.foreignWrite
  PPermission.initAccess PPermission.preventsDeallocation PPermission.unprotect

/- Actual raw allocation branches establish that the inherited initial raw
records of each selected size can be allocated. One candidate is a witness,
not a restriction of allocator choices or a universal safety proof. -/

theorem raw_allocate_zero :
    MiniRustReference.allocateAt MiniRustReference.empty .heap 0 1 16 =
      .ok (⟨16, some 0⟩, (initial 0).raw) := rfl

theorem raw_allocate_one :
    MiniRustReference.allocateAt MiniRustReference.empty .heap 1 1 16 =
      .ok (⟨16, some 0⟩, (initial 1).raw) := rfl

theorem raw_allocate_two :
    MiniRustReference.allocateAt MiniRustReference.empty .heap 2 1 16 =
      .ok (⟨16, some 0⟩, (initial 2).raw) := rfl

def child : Pointer := ⟨16, some (0, [0])⟩

/- Strong Cell: shared immutable reference to non-frozen interior-mutable data.
The source shared-reference branch supplies Cell inside and outside. A mutable
reference to such data would select Reserved under protection instead. -/

def sharedCell : Settings := ⟨[.prot .cell], .prot .cell, .strong⟩

def cellTree : Tree :=
  .mk [.unprot .unique] .no [.mk [.prot .cell] .strong []]

def cellBorn : State :=
  { setTree (initial 1) 0 cellTree with currentFrame := [(0, [0])] }

def cellDead : State := freed cellBorn cellTree (block 1)

def cellReleasedTree : Tree :=
  .mk [.unprot .unique] .no [.mk [.unprot .cell] .strong []]

def cellReleased : State := setTree cellDead 0 cellReleasedTree

theorem cell_initial_access_is_none :
    Permission.initAccess (.prot .cell) = none ∧
    TreeReference.initialAccesses cellTree [0] 0 sharedCell.inside = .ok () cellTree := by
  simp [cellTree, sharedCell]

theorem construct_shared_cell :
    reborrow (initial 1) root sharedCell = .ok child cellBorn := by
  simp [reborrow, initial, root, sharedCell, block, cellBorn, cellTree, setTree, child]

theorem strong_cell_deallocate :
    deallocate cellBorn child .heap 1 1 = .ok () cellDead := by
  simp [deallocate, freeWith, hookTarget, cellBorn, child, initial, block, cellTree,
    setTree, cellDead, freed]

theorem strong_cell_dead_release :
    release cellDead (0, [0]) = .ok () cellReleased := by
  simp [release, cellDead, freed, cellBorn, initial, block, cellTree, cellReleased,
    cellReleasedTree, setTree]

/-- The nonempty dead Cell permission list is converted under the retained flag.
This is an actual completed Memory.release equation, not a frame-pop theorem. -/
theorem strong_cell_matching_boundary :
    TreeReference.arraysSized cellTree 1 = true ∧
    TreeReference.kindsMatch cellTree = true ∧
    TreeReference.arraysSized cellReleasedTree 1 = true ∧
    TreeReference.kindsMatch cellReleasedTree = false ∧
    TreeReference.containsStrong cellTree = false := by
  simp [cellTree, cellReleasedTree]

/- A true empty allocation: neither the root nor its protected child has bytes.
No inside access occurs. Deallocation and release do not create a nonempty
permission-kind mismatch; matching remains vacuously true. -/

def zeroInside : Settings :=
  ⟨[], .prot (.reserved false false), .strong⟩

def emptyTree : Tree := .mk [] .no [.mk [] .strong []]

def emptyBorn : State :=
  { setTree (initial 0) 0 emptyTree with currentFrame := [(0, [0])] }

def emptyDead : State := freed emptyBorn emptyTree (block 0)
def emptyReleased : State := setTree emptyDead 0 emptyTree

theorem zero_inside_executes_no_initial_access (tree : Tree) (path : Path) (offset : Nat) :
    TreeReference.initialAccesses tree path offset zeroInside.inside = .ok () tree := rfl

theorem construct_true_empty :
    reborrow (initial 0) root zeroInside = .ok child emptyBorn := by
  simp [reborrow, initial, root, zeroInside, block, emptyBorn, emptyTree, setTree, child]

theorem true_empty_deallocate :
    deallocate emptyBorn child .heap 0 1 = .ok () emptyDead := by
  simp [deallocate, freeWith, hookTarget, emptyBorn, child, initial, block, emptyTree,
    setTree, emptyDead, freed]

theorem true_empty_dead_release :
    release emptyDead (0, [0]) = .ok () emptyReleased := by
  simp [release, emptyDead, freed, emptyBorn, initial, block, emptyTree,
    emptyReleased, setTree]

theorem true_empty_matching_is_vacuous :
    TreeReference.arraysSized emptyTree 0 = true ∧
    TreeReference.kindsMatch emptyTree = true ∧
    TreeReference.containsStrong emptyTree = false ∧
    (TreeReference.findNode emptyTree [0]).map TreeReference.Node.permissions = some [] ∧
    (TreeReference.findNode emptyTree [0]).map TreeReference.Node.protection = some .strong := by
  simp [emptyTree]

/- Empty inside list in positive-size storage: the protected outside byte is
Reserved with neither history bit set. The root and child paths must be kept
distinct when a deallocation writes the *whole allocation*. -/

def zeroReferenceTree : Tree :=
  .mk [.unprot .unique] .no [.mk [.prot (.reserved false false)] .strong []]

def zeroReferenceBorn : State :=
  { setTree (initial 1) 0 zeroReferenceTree with currentFrame := [(0, [0])] }

def zeroForeignTree : Tree :=
  .mk [.unprot .unique] .no [.mk [.prot .disabled] .strong []]

def zeroReferenceDead : State := freed zeroReferenceBorn zeroForeignTree (block 1)

def zeroReleasedTree : Tree :=
  .mk [.unprot .unique] .no [.mk [.unprot .disabled] .strong []]

def zeroReferenceReleased : State := setTree zeroReferenceDead 0 zeroReleasedTree

def zeroLocalTrial : Tree :=
  .mk [.unprot .unique] .no [.mk [.prot .unique] .strong []]

theorem construct_zero_reference_in_positive_storage :
    reborrow (initial 1) root zeroInside = .ok child zeroReferenceBorn := by
  simp [reborrow, initial, root, zeroInside, block, zeroReferenceBorn,
    zeroReferenceTree, setTree, child]

theorem zero_reference_outside_is_unused :
    (TreeReference.findNode zeroReferenceTree [0]).map TreeReference.Node.permissions =
      some [.prot (.reserved false false)] ∧
    TreeReference.containsStrong zeroReferenceTree = false := by
  simp [zeroReferenceTree]

theorem root_write_disables_unused_zero_reference :
    TreeReference.access zeroReferenceTree (some []) .write 0 1 = .ok () zeroForeignTree := by
  simp [zeroReferenceTree, zeroForeignTree]

theorem root_deallocate_allows_unused_zero_reference :
    deallocate zeroReferenceBorn root .heap 1 1 = .ok () zeroReferenceDead := by
  simp [deallocate, freeWith, hookTarget, zeroReferenceBorn, root, initial, block,
    zeroReferenceTree, zeroForeignTree, zeroReferenceDead, freed, setTree]

theorem zero_reference_dead_release :
    release zeroReferenceDead (0, [0]) = .ok () zeroReferenceReleased := by
  simp [release, zeroReferenceDead, freed, zeroReferenceBorn, initial, block,
    zeroForeignTree, zeroReferenceTree, zeroReleasedTree, zeroReferenceReleased, setTree]

theorem positive_storage_zero_reference_matching_boundary :
    TreeReference.arraysSized zeroReferenceTree 1 = true ∧
    TreeReference.kindsMatch zeroReferenceTree = true ∧
    TreeReference.kindsMatch zeroForeignTree = true ∧
    TreeReference.arraysSized zeroReleasedTree 1 = true ∧
    TreeReference.kindsMatch zeroReleasedTree = false ∧
    (TreeReference.findNode zeroReleasedTree [0]).map TreeReference.Node.protection =
      some .strong := by
  simp [zeroReferenceTree, zeroForeignTree, zeroReleasedTree]

theorem child_write_activates_zero_reference :
    TreeReference.access zeroReferenceTree (some [0]) .write 0 1 = .ok () zeroLocalTrial ∧
    TreeReference.containsStrong zeroLocalTrial = true := by
  simp [zeroReferenceTree, zeroLocalTrial]

/-- This is a separate operation from the same birth state, not a continuation
after the successful root-free path or after an earlier terminal UB. -/
theorem child_deallocate_blocks_zero_reference :
    deallocate zeroReferenceBorn child .heap 1 1 =
      .ub .strongProtector zeroReferenceBorn := by
  simp [deallocate, freeWith, hookTarget, zeroReferenceBorn, child, initial, block,
    zeroReferenceTree, setTree]

theorem deallocation_path_changes_outcome :
    deallocate zeroReferenceBorn root .heap 1 1 ≠
      deallocate zeroReferenceBorn child .heap 1 1 := by
  rw [root_deallocate_allows_unused_zero_reference, child_deallocate_blocks_zero_reference]
  intro impossible
  cases impossible

#print axioms raw_allocate_zero
#print axioms raw_allocate_one
#print axioms raw_allocate_two
#print axioms cell_initial_access_is_none
#print axioms construct_shared_cell
#print axioms strong_cell_deallocate
#print axioms strong_cell_dead_release
#print axioms strong_cell_matching_boundary
#print axioms zero_inside_executes_no_initial_access
#print axioms construct_true_empty
#print axioms true_empty_deallocate
#print axioms true_empty_dead_release
#print axioms true_empty_matching_is_vacuous
#print axioms construct_zero_reference_in_positive_storage
#print axioms zero_reference_outside_is_unused
#print axioms root_write_disables_unused_zero_reference
#print axioms root_deallocate_allows_unused_zero_reference
#print axioms zero_reference_dead_release
#print axioms positive_storage_zero_reference_matching_boundary
#print axioms child_write_activates_zero_reference
#print axioms child_deallocate_blocks_zero_reference
#print axioms deallocation_path_changes_outcome

end AnnealResearch.TreeExceptions
