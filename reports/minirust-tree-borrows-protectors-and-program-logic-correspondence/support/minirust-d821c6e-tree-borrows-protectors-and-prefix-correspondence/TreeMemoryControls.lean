import AnnealResearch.TreeMemory

/-!
Constructed controls use actual reborrow/initial-access/store operations in the
owned source-equation wrapper. Expected states below are separately written
trees, not success extracted with a default. The live-Frozen failure specimen
is only shape-admitted; its program reachability is deliberately unclaimed.
-/
namespace AnnealResearch.TreeMemoryControls

open TreePermissions TreeMemory

def seven : MiniRustReference.Byte := .init ⟨7, by decide⟩ none

def block (size : Nat) : MiniRustReference.Allocation :=
  { base := 16, size, align := 1, kind := .heap, live := true, data := fun _ => .uninit }

def initial (size : Nat) : State :=
  { raw := { next := 1, allocations := fun id => if id = 0 then some (block size) else none }
    trees := fun id => if id = 0 then
      some (.mk (List.replicate size (.unprot .unique)) .no []) else none
    currentFrame := [] }

def root : Pointer := ⟨16, some (0, [])⟩
def a : Pointer := ⟨16, some (0, [0])⟩
def b : Pointer := ⟨16, some (0, [1])⟩
def t : Pointer := ⟨16, some (0, [0, 0])⟩

def mutable : Settings := ⟨[.unprot .reserved], .unprot .reserved, .no⟩
def protectedMutable (protection : Protected) : Settings :=
  ⟨[.prot (.reserved false false)], .prot (.reserved false false), protection⟩

def treeA : Tree := .mk [.unprot .unique] .no [.mk [.unprot .reserved] .no []]
def treeAB : Tree :=
  .mk [.unprot .unique] .no [.mk [.unprot .reserved] .no [], .mk [.unprot .reserved] .no []]
def treeRead (protection : Protected) : Tree :=
  .mk [.unprot .unique] .no
    [.mk [.unprot .reserved] .no [.mk [.prot (.reserved true false)] protection []],
      .mk [.unprot .reserved] .no []]
def treeWrite (protection : Protected) : Tree :=
  .mk [.unprot .unique] .no
    [.mk [.unprot .unique] .no [.mk [.prot .unique] protection []],
      .mk [.unprot .disabled] .no []]

def stateA : State := setTree (initial 1) 0 treeA
def stateAB : State := setTree stateA 0 treeAB
def readState (protection : Protected) : State :=
  { setTree stateAB 0 (treeRead protection) with currentFrame := [(0, [0, 0])] }

def writtenBlock : MiniRustReference.Allocation :=
  { block 1 with data := fun index =>
      if 0 ≤ index ∧ index < 0 + [seven].length then
        [seven].getD (index - 0) .uninit else (block 1).data index }

def writeState (protection : Protected) : State :=
  { setTree (readState protection) 0 (treeWrite protection) with
    raw := MiniRustReference.replace (readState protection).raw 0 writtenBlock }

def freed (before : State) (tree : Tree) (allocation : MiniRustReference.Allocation) : State :=
  { setTree before 0 tree with raw :=
      (MiniRustReference.replace before.raw 0 { allocation with live := false }) }

def chain (result : Result A) (next : A → State → Result B) : Result B :=
  match result with
  | .ok value state => next value state
  | .ub fault state => .ub fault state
  | .unsupported reason state => .unsupported reason state
  | .noChoice state => .noChoice state

def constructRead (protection : Protected) : Result Pointer :=
  chain (reborrow (initial 1) root mutable) fun first afterA =>
    chain (reborrow afterA root mutable) fun _ afterB =>
      reborrow afterB first (protectedMutable protection)

attribute [local simp] Pointer.basic MiniRustReference.checkPtr MiniRustReference.load
  MiniRustReference.store MiniRustReference.free MiniRustReference.replace
  TreeReference.addNode TreeReference.modifyAt TreeReference.replaceNth
  TreeReference.arraysSized TreeReference.childrenSized TreeReference.initialAccesses
  TreeReference.access TreeReference.pathPresent TreeReference.findNode
  TreeReference.Node.permissions TreeReference.Node.children
  TreeReference.accessCore TreeReference.accessChildren TreeReference.transitionRange
  TreeReference.transitionPrefix TreeReference.nodeRelation TreeReference.childPath
  TreeReference.Result.mapState TreeReference.Result.bind
  TreeReference.containsStrong TreeReference.childrenContainStrong
  TreeReference.unprotectAt TreeReference.unprotectPermissions TreeReference.releaseTraverse
  TreeReference.releaseCore TreeReference.releaseChildren TreeReference.applyAccesses
  TreeReference.Node.protection TreeReference.kindsMatch TreeReference.childrenMatch
  Permission.transition Permission.initAccess Permission.matchesProtector Permission.isProt
  Permission.preventsDeallocation Permission.unprotect Protected.yes
  UPermission.transition UPermission.localRead UPermission.localWrite
  UPermission.foreignRead UPermission.foreignWrite UPermission.initAccess
  UPermission.preventsDeallocation PPermission.transition PPermission.localRead
  PPermission.localWrite PPermission.foreignRead PPermission.foreignWrite
  PPermission.initAccess PPermission.preventsDeallocation PPermission.unprotect

theorem construct_a : reborrow (initial 1) root mutable = .ok a stateA := by
  simp [reborrow, initial, root, mutable, block, stateA, treeA, setTree, a]

theorem construct_b : reborrow stateA root mutable = .ok b stateAB := by
  simp [reborrow, stateA, initial, root, mutable, block, stateAB, treeAB, treeA, setTree, b]

theorem construct_t_strong :
    reborrow stateAB a (protectedMutable .strong) = .ok t (readState .strong) := by
  simp [reborrow, stateAB, stateA, initial, a, protectedMutable, block, readState,
    treeRead, treeAB, treeA, setTree, t]

theorem construct_t_weak :
    reborrow stateAB a (protectedMutable .weak) = .ok t (readState .weak) := by
  simp [reborrow, stateAB, stateA, initial, a, protectedMutable, block, readState,
    treeRead, treeAB, treeA, setTree, t]

theorem full_strong_construction : constructRead .strong = .ok t (readState .strong) := by
  simp only [constructRead, construct_a, chain, construct_b, construct_t_strong]

theorem full_weak_construction : constructRead .weak = .ok t (readState .weak) := by
  simp only [constructRead, construct_a, chain, construct_b, construct_t_weak]

theorem actual_strong_write : store (readState .strong) t [seven] 1 =
    .ok () (writeState .strong) := by
  simp [store, hookTarget, readState, stateAB, stateA, initial, t, block, treeRead,
    treeAB, treeA, setTree, writeState, treeWrite, writtenBlock]

theorem actual_weak_write : store (readState .weak) t [seven] 1 =
    .ok () (writeState .weak) := by
  simp [store, hookTarget, readState, stateAB, stateA, initial, t, block, treeRead,
    treeAB, treeA, setTree, writeState, treeWrite, writtenBlock]

theorem strong_grandchild_blocks_free :
    deallocate (writeState .strong) t .heap 1 1 =
      .ub .strongProtector (writeState .strong) := by
  simp [deallocate, freeWith, writeState, hookTarget, readState, stateAB, stateA,
    initial, t, block, treeRead, treeAB, treeA, treeWrite, setTree, writtenBlock]

def rootOnly (tree : Tree) : Bool :=
  decide (tree.protection = .strong) && tree.permissions.any Permission.preventsDeallocation

theorem omitted_recursion_changes_outcome :
    freeWith rootOnly false (writeState .strong) t .heap 1 1 =
      .ok () (freed (writeState .strong) (treeWrite .strong) writtenBlock) := by
  simp [freeWith, rootOnly, writeState, hookTarget, readState, stateAB, stateA,
    initial, t, block, treeRead, treeAB, treeA, treeWrite, setTree, writtenBlock, freed]

def treeReleased : Tree :=
  .mk [.unprot .unique] .no
    [.mk [.unprot .unique] .no [.mk [.unprot .unique] .no []],
      .mk [.unprot .disabled] .no []]

def releasedState : State := setTree (writeState .strong) 0 treeReleased

theorem successful_live_release : release (writeState .strong) (0, [0, 0]) =
    .ok () releasedState := by
  simp [release, writeState, readState, stateAB, stateA, initial, block, treeRead,
    treeAB, treeA, treeWrite, setTree, writtenBlock, releasedState, treeReleased]

theorem free_after_release : deallocate releasedState t .heap 1 1 =
    .ok () (freed releasedState treeReleased writtenBlock) := by
  simp [deallocate, freeWith, releasedState, treeReleased, writeState, hookTarget,
    readState, stateAB, stateA, initial, t, block, treeRead, treeAB, treeA, treeWrite,
    setTree, writtenBlock, freed]

theorem weak_used_grandchild_allows_free : deallocate (writeState .weak) t .heap 1 1 =
    .ok () (freed (writeState .weak) (treeWrite .weak) writtenBlock) := by
  simp [deallocate, freeWith, writeState, hookTarget, readState, stateAB, stateA,
    initial, t, block, treeRead, treeAB, treeA, treeWrite, setTree, writtenBlock, freed]

def deadWeak : State := freed (writeState .weak) (treeWrite .weak) writtenBlock
def treeDeadWeakReleased : Tree :=
  .mk [.unprot .unique] .no
    [.mk [.unprot .unique] .no [.mk [.unprot .unique] .weak []],
      .mk [.unprot .disabled] .no []]
def deadWeakReleased : State := setTree deadWeak 0 treeDeadWeakReleased

theorem successful_dead_weak_release : release deadWeak (0, [0, 0]) =
    .ok () deadWeakReleased := by
  simp [release, deadWeak, freed, writeState, readState, stateAB, stateA, initial,
    block, treeRead, treeAB, treeA, treeWrite, setTree, writtenBlock, deadWeakReleased,
    treeDeadWeakReleased]

theorem dead_weak_release_refutes_global_matching :
    TreeReference.kindsMatch (treeWrite .weak) = true ∧
    TreeReference.kindsMatch treeDeadWeakReleased = false := by
  simp [treeWrite, treeDeadWeakReleased]

theorem eager_commit_changes_failure_residual :
    deallocate (readState .strong) t .heap 1 1 = .ub .strongProtector (readState .strong) ∧
    freeWith TreeReference.containsStrong true (readState .strong) t .heap 1 1 =
      .ub .strongProtector (setTree (readState .strong) 0 (treeWrite .strong)) ∧
    (TreeReference.findNode (treeRead .strong) [1]).map TreeReference.Node.permissions ≠
      (TreeReference.findNode (treeWrite .strong) [1]).map TreeReference.Node.permissions := by
  simp [deallocate, freeWith, readState, hookTarget, stateAB, stateA, initial, t,
    block, treeRead, treeAB, treeA, treeWrite, setTree]

def twoPointer : Pointer := ⟨17, some (0, [])⟩
def twoChild : Pointer := ⟨17, some (0, [0])⟩
def twoTree : Tree := .mk [.unprot .unique, .unprot .unique] .no
  [.mk [.prot (.reserved false false), .prot (.reserved true false)] .strong []]
def twoRead : State :=
  { setTree (initial 2) 0 twoTree with currentFrame := [(0, [0])] }
def twoTrial : Tree := .mk [.unprot .unique, .unprot .unique] .no
  [.mk [.prot .disabled, .prot (.reserved true false)] .strong []]

theorem construct_two_byte_history :
    reborrow (initial 2) twoPointer (protectedMutable .strong) = .ok twoChild twoRead := by
  simp [reborrow, initial, twoPointer, protectedMutable, block, twoChild,
    twoRead, twoTree, setTree]

theorem two_byte_trial_retains_earlier_change :
    TreeReference.access twoTree (some []) .write 0 2 =
      .ub .protectedForeignWriteReservedAfterLocalRead twoTrial := by
  simp [twoTree, twoTrial]

theorem two_byte_public_store_rolls_back : store twoRead root [seven, seven] 1 =
    .ub (.tree .protectedForeignWriteReservedAfterLocalRead) twoRead := by
  simp [store, twoRead, initial, root, hookTarget, block, twoTree, setTree]

def liveFailureTree : Tree := .mk [.unprot .frozen] .no [.mk [.prot .unique] .strong []]
def liveFailureConverted : Tree :=
  .mk [.unprot .frozen] .no [.mk [.unprot .unique] .strong []]
def liveFailure : State :=
  { setTree (initial 1) 0 liveFailureTree with currentFrame := [(0, [0])] }

/-- Shape-admitted counterexample only; no claim this tree is program reachable. -/
theorem live_failed_release_commits_conversion : release liveFailure (0, [0]) =
    .ub (.tree .unprotectedLocalWriteFrozen) (setTree liveFailure 0 liveFailureConverted) := by
  simp [release, liveFailure, initial, block, liveFailureTree, liveFailureConverted, setTree]

theorem live_failure_matching_scope :
    TreeReference.arraysSized liveFailureTree 1 = true ∧
    TreeReference.kindsMatch liveFailureTree = true ∧
    TreeReference.kindsMatch liveFailureConverted = false := by
  simp [liveFailureTree, liveFailureConverted]

#print axioms construct_a
#print axioms construct_b
#print axioms construct_t_strong
#print axioms construct_t_weak
#print axioms full_strong_construction
#print axioms full_weak_construction
#print axioms actual_strong_write
#print axioms actual_weak_write
#print axioms strong_grandchild_blocks_free
#print axioms omitted_recursion_changes_outcome
#print axioms successful_live_release
#print axioms free_after_release
#print axioms weak_used_grandchild_allows_free
#print axioms successful_dead_weak_release
#print axioms dead_weak_release_refutes_global_matching
#print axioms eager_commit_changes_failure_residual
#print axioms construct_two_byte_history
#print axioms two_byte_trial_retains_earlier_change
#print axioms two_byte_public_store_rolls_back
#print axioms live_failed_release_commits_conversion
#print axioms live_failure_matching_scope

end AnnealResearch.TreeMemoryControls
