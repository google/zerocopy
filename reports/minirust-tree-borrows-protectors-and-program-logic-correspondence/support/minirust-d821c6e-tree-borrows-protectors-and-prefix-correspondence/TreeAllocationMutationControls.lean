import AnnealResearch.TreeAllocationDomain
import AnnealResearch.TreeMemoryControls
import AnnealResearch.TreeLiveKindControls

/-!
Distinct observations challenge zero initialization, a wrong root path, and
omitted whole-tree replacement. Width/live matching cannot detect a changed
initial byte. The zeroing mutant deliberately edits the actual successful birth;
it is not an alternative semantics or a claim that zero-filled states are UB.
The stray input/frame is an owned-product specimen, not source reachable.
-/
namespace AnnealResearch.TreeAllocationMutationControls

open TreePermissions

abbrev R := TreeMemory.State
abbrev F := TreeFactoredMemory.State

def empty : R := ⟨MiniRustReference.empty, fun _ => none, []⟩
def zeroByte : MiniRustReference.Byte := .init ⟨0, by decide⟩ none

theorem actual_birth : TreeMemory.allocateAt empty .heap 1 1 16 =
    .ok TreeMemoryControls.root (TreeMemoryControls.initial 1) := rfl

/-- A deliberate mutation of actual successful allocation: zero only the new
record's bytes. Keep the actual pointer, root tree, metadata and frame. -/
def zeroingAllocate (state : R) (kind : MiniRustReference.Kind) (size align address : Nat) :
    TreeMemory.Result TreeMemory.Pointer :=
  TreeMemoryControls.chain (TreeMemory.allocateAt state kind size align address) fun pointer changed =>
    match pointer.provenance with
    | none => .ok pointer changed
    | some (id, _) =>
      match changed.raw.allocations id with
      | none => .ok pointer changed
      | some allocation =>
        .ok pointer { changed with
          raw := MiniRustReference.replace changed.raw id { allocation with data := fun _ => zeroByte } }

def zeroBlock : MiniRustReference.Allocation :=
  { TreeMemoryControls.block 1 with data := fun _ => zeroByte }
def zeroBorn : R :=
  { TreeMemoryControls.initial 1 with
    raw := MiniRustReference.replace (TreeMemoryControls.initial 1).raw 0 zeroBlock }

theorem mutant_zeroing_birth : zeroingAllocate empty .heap 1 1 16 =
    .ok TreeMemoryControls.root zeroBorn := by
  simp only [zeroingAllocate, actual_birth, TreeMemoryControls.chain]
  rfl

attribute [local simp] TreeMemory.Pointer.basic MiniRustReference.checkPtr MiniRustReference.load
  MiniRustReference.replace TreeReference.access TreeReference.pathPresent TreeReference.findNode
  TreeReference.arraysSized TreeReference.childrenSized TreeReference.Node.permissions
  TreeReference.Node.children TreeReference.accessCore TreeReference.accessChildren
  TreeReference.transitionRange TreeReference.transitionPrefix TreeReference.nodeRelation
  TreeReference.childPath TreeReference.Result.mapState Permission.transition
  UPermission.transition UPermission.localRead

theorem actual_Uninit_load :
    TreeMemory.load (TreeMemoryControls.initial 1) TreeMemoryControls.root 1 1 =
      .ok [.uninit] (TreeMemoryControls.initial 1) := by
  simp [TreeMemory.load, TreeMemory.hookTarget, TreeMemoryControls.initial,
    TreeMemoryControls.root, TreeMemoryControls.block, TreeMemory.setTree]
  funext id
  by_cases selected : id = 0 <;> simp [selected]

theorem mutant_zero_load : TreeMemory.load zeroBorn TreeMemoryControls.root 1 1 =
    .ok [zeroByte] zeroBorn := by
  simp [TreeMemory.load, TreeMemory.hookTarget, TreeMemoryControls.initial,
    TreeMemoryControls.root, TreeMemoryControls.block, TreeMemory.setTree,
    zeroBorn, zeroBlock]
  funext id
  by_cases selected : id = 0 <;> simp [selected]

theorem zeroBorn_width : TreeMemoryEncoding.RWellSized zeroBorn := by
  intro id allocation tree rawFound treeFound
  by_cases selected : id = 0
  · subst id
    have sameAllocation : zeroBlock = allocation := by
      simpa [zeroBorn, TreeMemoryControls.initial] using rawFound
    have sameTree : TreeAllocation.referenceRoot 1 = tree := by
      simpa [zeroBorn, TreeMemoryControls.initial, TreeAllocation.referenceRoot,
        TreeAllocation.rootPermissions] using treeFound
    subst allocation
    subst tree
    exact TreeAllocation.referenceRoot_width 1
  · simp [zeroBorn, TreeMemoryControls.initial, selected] at rawFound

theorem zeroBorn_matching : TreeLiveKinds.LiveKinds zeroBorn := by
  apply TreeLiveKindControls.single_tree_live _ (TreeAllocation.referenceRoot 1)
  · intro id
    simp [zeroBorn, TreeMemoryControls.initial, TreeAllocation.referenceRoot,
      TreeAllocation.rootPermissions]
  · exact TreeAllocation.referenceRoot_matching 1

/-- A nonempty width/matching state can give the wrong initial load reply.
Those predicates do not establish allocation-byte initialization. -/
theorem zeroing_survives_tree_invariants :
    TreeMemoryEncoding.RWellSized zeroBorn ∧ TreeLiveKinds.LiveKinds zeroBorn ∧
      [.uninit] ≠ [zeroByte] := by
  exact ⟨zeroBorn_width, zeroBorn_matching, by intro impossible; cases impossible⟩

theorem wrong_root_path_changes_outcome :
    TreeMemory.load (TreeMemoryControls.initial 1) ⟨16, some (0, [7])⟩ 1 1 =
      .unsupported (.tree .invalidPath) (TreeMemoryControls.initial 1) := by
  simp [TreeMemory.load, TreeMemory.hookTarget, TreeMemoryControls.initial,
    TreeMemoryControls.block]

def leaf : TreeFactored.Topology := .node .nil
def poison : TreeFactored.State :=
  ⟨.node (.cons leaf .nil), fun _ => ⟨[.prot .unique, .prot .unique], .strong⟩⟩
def stray : F :=
  { raw := MiniRustReference.empty
    trees := fun id => if id = 0 then some poison else none
    currentFrame := [(9, [2])] }
def replaced : F :=
  { TreeFactoredMemory.setTree stray 0 (TreeAllocation.factoredRoot 1) with
    raw := MiniRustReference.append stray.raw (TreeMemoryControls.block 1) }

theorem actual_poison_replacement :
    TreeFactoredMemory.allocateAt stray .heap 1 1 16 = .ok TreeMemoryControls.root replaced := rfl

theorem replacement_observations :
    stray.raw = MiniRustReference.empty ∧
    TreeFactored.findTopology poison.topology [0] = some leaf ∧
    (poison.store []).permissions.length = 2 ∧
    replaced.trees 0 = some (TreeAllocation.factoredRoot 1) ∧
    TreeFactored.findTopology (TreeAllocation.factoredRoot 1).topology [0] = none ∧
    ((TreeAllocation.factoredRoot 1).store []).protection = .no ∧
    ((TreeAllocation.factoredRoot 1).store []).permissions = [.unprot .unique] ∧
    replaced.currentFrame = [(9, [2])] := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp [replaced, TreeFactoredMemory.setTree]

theorem poisoned_empty_raw_is_WF : MiniRustReference.StateWF stray.raw :=
  MiniRustReference.emptyStateWF

#print axioms actual_birth
#print axioms mutant_zeroing_birth
#print axioms actual_Uninit_load
#print axioms mutant_zero_load
#print axioms zeroBorn_width
#print axioms zeroBorn_matching
#print axioms zeroing_survives_tree_invariants
#print axioms wrong_root_path_changes_outcome
#print axioms actual_poison_replacement
#print axioms replacement_observations
#print axioms poisoned_empty_raw_is_WF

end AnnealResearch.TreeAllocationMutationControls
