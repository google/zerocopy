import AnnealResearch.TreeFactoredReborrow
import AnnealResearch.TreeMemoryControls

/-!
Reference-wrapper controls isolate reborrow's commit and registration ordering.
The parent tree below is a shape-admitted specimen with a Disabled byte; no
construction or Rust reachability claim is made for it. The actual wrapper
inserts its child, performs one successful initial read, then fails at the next
byte. Separate Cell settings request no initial access and succeed unchanged at
the ancestor, appending one protector entry only after successful birth.
-/
namespace AnnealResearch.TreeReborrowStateControls

open TreePermissions
open TreeMemory

def rootTree : Tree := .mk [.unprot .unique, .unprot .disabled] .no []
def before : State :=
  { setTree (TreeMemoryControls.initial 2) 0 rootTree with currentFrame := [(42, [3])] }
def childPointer : Pointer := ⟨16, some (0, [0])⟩
def reads : Settings :=
  ⟨[.prot (.reserved false false), .prot (.reserved false false)], .prot .disabled, .strong⟩
def partialTree : Tree :=
  .mk [.unprot .unique, .unprot .disabled] .no
    [.mk [.prot (.reserved true false), .prot (.reserved false false)] .strong []]
def partialState : State := setTree before 0 partialTree

theorem actual_partial_initial_failure :
    reborrow before TreeMemoryControls.root reads =
      .ub (.tree .unprotectedLocalReadDisabled) partialState := by
  simp [reborrow, before, rootTree, TreeMemoryControls.initial, TreeMemoryControls.root,
    TreeMemoryControls.block, setTree, MiniRustReference.checkPtr, Pointer.basic,
    Permission.matchesProtector, Permission.isProt, Protected.yes,
    TreeReference.addNode, TreeReference.modifyAt, TreeReference.arraysSized,
    TreeReference.childrenSized, TreeReference.Node.permissions,
    TreeReference.initialAccesses, Permission.initAccess, PPermission.initAccess, reads, partialState, partialTree,
    TreeReference.access, TreeReference.pathPresent, TreeReference.findNode,
    TreeReference.Node.children, TreeReference.accessCore, TreeReference.accessChildren,
    TreeReference.transitionRange, TreeReference.transitionPrefix,
    TreeReference.nodeRelation, TreeReference.childPath,
    Permission.transition, UPermission.transition, UPermission.localRead,
    PPermission.transition, PPermission.localRead,
    TreeReference.Result.bind, TreeReference.Result.mapState]

theorem failed_birth_retains_partial_tree_and_old_frame :
    partialState.raw = before.raw ∧
    partialState.currentFrame = [(42, [3])] ∧
    partialState.trees 0 = some partialTree ∧
    TreeReference.findNode partialTree [0] =
      some (.mk [.prot (.reserved true false), .prot (.reserved false false)] .strong []) := by
  exact ⟨rfl, rfl, by simp [partialState, setTree], rfl⟩

def cells : Settings := ⟨[.prot .cell, .prot .cell], .prot .cell, .strong⟩
def cellTree : Tree :=
  .mk [.unprot .unique, .unprot .disabled] .no [.mk [.prot .cell, .prot .cell] .strong []]
def cellState : State :=
  { setTree before 0 cellTree with currentFrame := before.currentFrame ++ [(0, [0])] }

theorem actual_cell_birth_skips_initial_access :
    reborrow before TreeMemoryControls.root cells = .ok childPointer cellState := by
  simp [reborrow, before, rootTree, TreeMemoryControls.initial, TreeMemoryControls.root,
    TreeMemoryControls.block, setTree, MiniRustReference.checkPtr, Pointer.basic,
    Permission.matchesProtector, Permission.isProt, Protected.yes,
    TreeReference.addNode, TreeReference.modifyAt, TreeReference.arraysSized,
    TreeReference.childrenSized, TreeReference.Node.permissions,
    TreeReference.initialAccesses, Permission.initAccess, PPermission.initAccess, cells, cellState, cellTree, childPointer]

theorem cell_birth_registers_once_after_old_entries :
    cellState.raw = before.raw ∧
    cellState.currentFrame = [(42, [3]), (0, [0])] ∧
    TreeReference.Node.permissions cellTree = TreeReference.Node.permissions rootTree :=
  ⟨rfl, rfl, rfl⟩

/-- Settings validation executes before insertion path lookup. The supplied
path is missing, but a kind mismatch is the observed earlier rejection. -/
theorem settings_rejected_before_missing_parent :
    reborrow before ⟨16, some (0, [99])⟩
      ⟨[.unprot .reserved], .unprot .reserved, .strong⟩ =
      .unsupported .settings before := by
  rfl

#print axioms actual_partial_initial_failure
#print axioms failed_birth_retains_partial_tree_and_old_frame
#print axioms actual_cell_birth_skips_initial_access
#print axioms cell_birth_registers_once_after_old_entries
#print axioms settings_rejected_before_missing_parent

end AnnealResearch.TreeReborrowStateControls
