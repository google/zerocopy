import AnnealResearch.TreeAllocationDomain
import AnnealResearch.TreeAllocationMutationControls
import AnnealResearch.TreeAllocationFreshness
import AnnealResearch.TreeMemoryControls
import AnnealResearch.TreeReborrowAgreement
import AnnealResearch.TreeReborrowDomain
import AnnealResearch.TreeMemoryOperations
import AnnealResearch.TreeMemoryReleaseAgreement
import AnnealResearch.TreeMemoryPreservation

/-!
Actual selected-candidate birth into the old constructed nonempty histories.
The actual returned root drives both sibling reborrows; the returned first
child drives the protected grandchild; its returned pointer drives store/free.
R expected states are independently supplied old fixtures or explicit updates.
F observations are transferred through checked full correspondence and all-result
width closure, starting from an explicit empty F memory. No poststate is extracted
with a fallback or supplied by assuming successful execution.

These are finite owned-operation test sequencers, not an allocation-aware client,
a demonic-choice coverage theorem, OOM/progress claim or source/Rust adequacy.
The old supplied release provenance and retained registration list are explicit.
-/
namespace AnnealResearch.TreeAllocationControls

open TreePermissions
open TreeMemoryControls (initial root mutable protectedMutable seven)

def referenceEmpty : TreeMemory.State :=
  { raw := MiniRustReference.empty, trees := fun _ => none, currentFrame := [] }

def factoredEmpty : TreeFactoredMemory.State :=
  { raw := MiniRustReference.empty, trees := fun _ => none, currentFrame := [] }

theorem empty_reify : TreeFactoredMemory.reify factoredEmpty = referenceEmpty := rfl

theorem empty_sized : TreeFactoredMemory.WellSized factoredEmpty := by
  intro id allocation tree rawFound treeFound
  cases treeFound

theorem reference_birth_one :
    TreeMemory.allocateAt referenceEmpty .heap 1 1 16 = .ok root (initial 1) := rfl

theorem factored_birth_one :
    TreeFactoredMemory.translate (TreeFactoredMemory.allocateAt factoredEmpty .heap 1 1 16) =
      .ok root (initial 1) := by
  rw [← TreeAllocation.allocateAt_agrees, empty_reify]
  exact reference_birth_one

/-- Birth is nonempty/live and raw-admitted; source-style admission is proved
with its separate assumptions, not inferred from width or matching. -/
theorem birth_domains : MiniRustReference.StateWF (initial 1).raw ∧
    TreeMemoryEncoding.RWellSized (initial 1) ∧ TreeLiveKinds.LiveKinds (initial 1) := by
  have raw := TreeAllocationFreshness.reference_preserves_raw_StateWF
    referenceEmpty .heap 1 1 16 MiniRustReference.emptyStateWF ⟨0, rfl⟩
  have emptyWidth : TreeMemoryEncoding.RWellSized referenceEmpty := by
    intro id allocation tree rawFound treeFound
    cases treeFound
  have emptyMatching : TreeLiveKinds.LiveKinds referenceEmpty := by
    intro id allocation tree rawFound alive treeFound
    cases treeFound
  have sized := TreeAllocationDomain.reference_preserves_width
    referenceEmpty .heap 1 1 16 emptyWidth
  have matching := TreeAllocationDomain.reference_preserves_live
    referenceEmpty .heap 1 1 16 emptyMatching
  exact ⟨by simpa only [reference_birth_one, TreeAllocationFreshness.referenceResidual] using raw,
    by simpa only [reference_birth_one, TreeAllocationDomain.RResultWellSized,
      TreeLiveMemory.residual] using sized,
    by simpa only [reference_birth_one, TreeLiveMemory.ResultLiveKinds,
      TreeLiveMemory.residual] using matching⟩

theorem initial_set_root (size : Nat) :
    TreeMemory.setTree (initial size) 0 (TreeAllocation.referenceRoot size) = initial size := by
  unfold TreeMemory.setTree initial TreeAllocation.referenceRoot TreeAllocation.rootPermissions
  congr 1
  funext id
  by_cases zero : id = 0 <;> simp [zero]

/-- Reuse the parent-checked actual load observation; the recursive worker's
opaque reduction requires its existing finite simplification proof. -/
theorem initial_load_uninit :
    TreeMemory.load (initial 1) root 1 1 = .ok [.uninit] (initial 1) :=
  TreeAllocationMutationControls.actual_Uninit_load

/-- Test-only sequencer retaining every actual failure state; no semantics of
an allocation-aware arbitrary controller is introduced. -/
def fChain (answer : TreeFactoredMemory.Result A)
    (next : A → TreeFactoredMemory.State → TreeFactoredMemory.Result B) : TreeFactoredMemory.Result B :=
  match answer with
  | .ok value memory => next value memory
  | .ub fault memory => .ub fault memory
  | .unsupported reason memory => .unsupported reason memory
  | .noChoice memory => .noChoice memory

theorem fChain_sized {A B : Type} (answer : TreeFactoredMemory.Result A)
    (next : A → TreeFactoredMemory.State → TreeFactoredMemory.Result B)
    (sized : TreeFactoredMemory.WellSized answer.residual)
    (preserves : ∀ value memory, TreeFactoredMemory.WellSized memory →
      TreeFactoredMemory.WellSized (next value memory).residual) :
    TreeFactoredMemory.WellSized (fChain answer next).residual := by
  cases answer with
  | ok value memory => exact preserves value memory sized
  | ub fault memory => exact sized
  | unsupported reason memory => exact sized
  | noChoice memory => exact sized

/-- Shared proof transport, including actual failure states. This helper cases
on the existing result; it never selects a successful state by default. -/
theorem fChain_agrees {A B : Type} (answer : TreeFactoredMemory.Result A)
    (rNext : A → TreeMemory.State → TreeMemory.Result B)
    (fNext : A → TreeFactoredMemory.State → TreeFactoredMemory.Result B)
    (sized : TreeFactoredMemory.WellSized answer.residual)
    (agreement : ∀ value memory, TreeFactoredMemory.WellSized memory →
      rNext value (TreeFactoredMemory.reify memory) = TreeFactoredMemory.translate (fNext value memory)) :
    TreeMemoryControls.chain (TreeFactoredMemory.translate answer) rNext =
      TreeFactoredMemory.translate (fChain answer fNext) := by
  cases answer with
  | ok value memory => exact agreement value memory sized
  | ub fault memory => rfl
  | unsupported reason memory => rfl
  | noChoice memory => rfl

def rBornLoad : TreeMemory.Result (List MiniRustReference.Byte) :=
  TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 1 1 16)
    (fun pointer memory => TreeMemory.load memory pointer 1 1)

def fBornLoad : TreeFactoredMemory.Result (List MiniRustReference.Byte) :=
  fChain (TreeFactoredMemory.allocateAt factoredEmpty .heap 1 1 16)
    (fun pointer memory => TreeFactoredMemory.load memory pointer 1 1)

theorem reference_born_load : rBornLoad = .ok [.uninit] (initial 1) := by
  unfold rBornLoad
  rw [reference_birth_one]
  exact initial_load_uninit

theorem factored_born_load :
    TreeFactoredMemory.translate fBornLoad = .ok [.uninit] (initial 1) := by
  have agreement : rBornLoad = TreeFactoredMemory.translate fBornLoad := by
    unfold rBornLoad fBornLoad
    rw [← empty_reify, TreeAllocation.allocateAt_agrees]
    apply fChain_agrees _ _ _
      (TreeAllocationDomain.factored_preserves_width factoredEmpty .heap 1 1 16 empty_sized)
    intro pointer memory sized
    exact TreeMemoryOperations.load_agrees memory pointer 1 1 sized
  rw [← agreement]
  exact reference_born_load

/-- Both siblings use the actual returned root; the grandchild uses the first
actual child. The original independently checked constructRead equations apply. -/
def rConstructFrom (memory : TreeMemory.State) (pointer : TreeMemory.Pointer)
    (protection : Protected) : TreeMemory.Result TreeMemory.Pointer :=
  TreeMemoryControls.chain (TreeMemory.reborrow memory pointer mutable) fun first afterA =>
    TreeMemoryControls.chain (TreeMemory.reborrow afterA pointer mutable) fun _ afterB =>
      TreeMemory.reborrow afterB first (protectedMutable protection)

def fConstructFrom (memory : TreeFactoredMemory.State) (pointer : TreeMemory.Pointer)
    (protection : Protected) : TreeFactoredMemory.Result TreeMemory.Pointer :=
  fChain (TreeFactoredMemory.reborrow memory pointer mutable) fun first afterA =>
    fChain (TreeFactoredMemory.reborrow afterA pointer mutable) fun _ afterB =>
      TreeFactoredMemory.reborrow afterB first (protectedMutable protection)

theorem constructFrom_sized (memory : TreeFactoredMemory.State) (pointer : TreeMemory.Pointer)
    (protection : Protected) (sized : TreeFactoredMemory.WellSized memory) :
    TreeFactoredMemory.WellSized (fConstructFrom memory pointer protection).residual := by
  unfold fConstructFrom
  apply fChain_sized _ _ (TreeReborrowDomain.reborrow_preserves memory pointer mutable sized)
  intro first afterA sizedA
  apply fChain_sized _ _ (TreeReborrowDomain.reborrow_preserves afterA pointer mutable sizedA)
  intro second afterB sizedB
  exact TreeReborrowDomain.reborrow_preserves afterB first (protectedMutable protection) sizedB

theorem constructFrom_agrees (memory : TreeFactoredMemory.State) (pointer : TreeMemory.Pointer)
    (protection : Protected) (sized : TreeFactoredMemory.WellSized memory) :
    rConstructFrom (TreeFactoredMemory.reify memory) pointer protection =
      TreeFactoredMemory.translate (fConstructFrom memory pointer protection) := by
  unfold rConstructFrom fConstructFrom
  rw [TreeReborrowAgreement.reborrow_agrees memory pointer mutable sized]
  apply fChain_agrees _ _ _ (TreeReborrowDomain.reborrow_preserves memory pointer mutable sized)
  intro first afterA sizedA
  rw [TreeReborrowAgreement.reborrow_agrees afterA pointer mutable sizedA]
  apply fChain_agrees _ _ _ (TreeReborrowDomain.reborrow_preserves afterA pointer mutable sizedA)
  intro second afterB sizedB
  exact TreeReborrowAgreement.reborrow_agrees afterB first (protectedMutable protection) sizedB

def rBornConstruct (protection : Protected) : TreeMemory.Result TreeMemory.Pointer :=
  TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 1 1 16) fun pointer memory =>
    TreeMemoryControls.chain (TreeMemory.load memory pointer 1 1) fun _ afterLoad =>
      rConstructFrom afterLoad pointer protection

def fBornConstruct (protection : Protected) : TreeFactoredMemory.Result TreeMemory.Pointer :=
  fChain (TreeFactoredMemory.allocateAt factoredEmpty .heap 1 1 16) fun pointer memory =>
    fChain (TreeFactoredMemory.load memory pointer 1 1) fun _ afterLoad =>
      fConstructFrom afterLoad pointer protection

theorem bornConstruct_sized (protection : Protected) :
    TreeFactoredMemory.WellSized (fBornConstruct protection).residual := by
  unfold fBornConstruct
  apply fChain_sized _ _
    (TreeAllocationDomain.factored_preserves_width factoredEmpty .heap 1 1 16 empty_sized)
  intro pointer memory sized
  apply fChain_sized _ _ (TreeMemoryPreservation.load_preserves memory pointer 1 1 sized)
  intro bytes afterLoad afterSized
  exact constructFrom_sized afterLoad pointer protection afterSized

theorem bornConstruct_agrees (protection : Protected) :
    rBornConstruct protection = TreeFactoredMemory.translate (fBornConstruct protection) := by
  unfold rBornConstruct fBornConstruct
  rw [← empty_reify, TreeAllocation.allocateAt_agrees]
  apply fChain_agrees _ _ _
    (TreeAllocationDomain.factored_preserves_width factoredEmpty .heap 1 1 16 empty_sized)
  intro pointer memory sized
  rw [TreeMemoryOperations.load_agrees memory pointer 1 1 sized]
  apply fChain_agrees _ _ _ (TreeMemoryPreservation.load_preserves memory pointer 1 1 sized)
  intro bytes afterLoad afterSized
  exact constructFrom_agrees afterLoad pointer protection afterSized

theorem reference_born_strong :
    rBornConstruct .strong = .ok TreeMemoryControls.t (TreeMemoryControls.readState .strong) := by
  unfold rBornConstruct
  rw [reference_birth_one]
  simp only [TreeMemoryControls.chain]
  rw [initial_load_uninit]
  exact TreeMemoryControls.full_strong_construction

theorem reference_born_weak :
    rBornConstruct .weak = .ok TreeMemoryControls.t (TreeMemoryControls.readState .weak) := by
  unfold rBornConstruct
  rw [reference_birth_one]
  simp only [TreeMemoryControls.chain]
  rw [initial_load_uninit]
  exact TreeMemoryControls.full_weak_construction

theorem factored_born_strong :
    TreeFactoredMemory.translate (fBornConstruct .strong) =
      .ok TreeMemoryControls.t (TreeMemoryControls.readState .strong) := by
  rw [← bornConstruct_agrees]
  exact reference_born_strong

theorem zero_birth : TreeMemory.allocateAt referenceEmpty .heap 0 1 16 =
    .ok root (initial 0) ∧ (initial 0).trees 0 = some (.mk [] .no []) ∧
    root.provenance = some (0, []) ∧ (initial 0).currentFrame = [] ∧
    (initial 0).raw.allocations 0 = some (TreeMemoryControls.block 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem factored_zero_birth :
    TreeFactoredMemory.translate (TreeFactoredMemory.allocateAt factoredEmpty .heap 0 1 16) =
      .ok root (initial 0) := by
  rw [← TreeAllocation.allocateAt_agrees, empty_reify]
  exact zero_birth.1

def adjacentRoot : TreeMemory.Pointer := ⟨17, some (1, [])⟩
def adjacent : TreeMemory.State :=
  { TreeMemory.setTree (initial 1) 1 (TreeAllocation.referenceRoot 1) with
    raw := MiniRustReference.append (initial 1).raw { TreeMemoryControls.block 1 with base := 17 } }

def rTwoBirths (address : Nat) : TreeMemory.Result TreeMemory.Pointer :=
  TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 1 1 16)
    (fun _ memory => TreeMemory.allocateAt memory .heap 1 1 address)

def fTwoBirths (address : Nat) : TreeFactoredMemory.Result TreeMemory.Pointer :=
  fChain (TreeFactoredMemory.allocateAt factoredEmpty .heap 1 1 16)
    (fun _ memory => TreeFactoredMemory.allocateAt memory .heap 1 1 address)

/-- Selected candidate 16 is blocked; 17 is an actual alternative. This says
nothing about all-address coverage or the absence of all valid candidates. -/
theorem live_candidate_discriminator : rTwoBirths 16 = .noChoice (initial 1) ∧
    rTwoBirths 17 = .ok adjacentRoot adjacent := by
  constructor <;> unfold rTwoBirths <;> rw [reference_birth_one] <;> rfl

theorem factored_live_candidate_discriminator :
    TreeFactoredMemory.translate (fTwoBirths 16) = .noChoice (initial 1) ∧
    TreeFactoredMemory.translate (fTwoBirths 17) = .ok adjacentRoot adjacent := by
  have agreement : ∀ address, rTwoBirths address = TreeFactoredMemory.translate (fTwoBirths address) := by
    intro address
    unfold rTwoBirths fTwoBirths
    rw [← empty_reify, TreeAllocation.allocateAt_agrees]
    apply fChain_agrees _ _ _
      (TreeAllocationDomain.factored_preserves_width factoredEmpty .heap 1 1 16 empty_sized)
    intro pointer memory sized
    exact TreeAllocation.allocateAt_agrees memory .heap 1 1 address
  rw [← agreement 16, ← agreement 17]
  exact live_candidate_discriminator

/-- Supplied release provenance is the actual fixture's protected grandchild.
Release keeps the old registration list; no full frame-lifecycle claim is made. -/
def rLifecycle (memory : TreeMemory.State) (child : TreeMemory.Pointer) : TreeMemory.Result Unit :=
  TreeMemoryControls.chain (TreeMemory.store memory child [seven] 1) fun _ written =>
    TreeMemoryControls.chain (TreeMemory.deallocate written child .heap 1 1) fun _ dead =>
      TreeMemory.release dead (0, [0, 0])

def fLifecycle (memory : TreeFactoredMemory.State) (child : TreeMemory.Pointer) :
    TreeFactoredMemory.Result Unit :=
  fChain (TreeFactoredMemory.store memory child [seven] 1) fun _ written =>
    fChain (TreeFactoredMemory.deallocate written child .heap 1 1) fun _ dead =>
      TreeFactoredMemory.release dead (0, [0, 0])

theorem lifecycle_sized (memory : TreeFactoredMemory.State) (child : TreeMemory.Pointer)
    (sized : TreeFactoredMemory.WellSized memory) :
    TreeFactoredMemory.WellSized (fLifecycle memory child).residual := by
  unfold fLifecycle
  apply fChain_sized _ _ (TreeMemoryPreservation.store_preserves memory child [seven] 1 sized)
  intro reply written writtenSized
  apply fChain_sized _ _ (TreeMemoryPreservation.deallocate_preserves written child .heap 1 1 writtenSized)
  intro reply dead deadSized
  exact TreeMemoryPreservation.release_preserves dead (0, [0, 0]) deadSized

theorem lifecycle_agrees (memory : TreeFactoredMemory.State) (child : TreeMemory.Pointer)
    (sized : TreeFactoredMemory.WellSized memory) :
    rLifecycle (TreeFactoredMemory.reify memory) child =
      TreeFactoredMemory.translate (fLifecycle memory child) := by
  unfold rLifecycle fLifecycle
  rw [TreeMemoryOperations.store_agrees memory child [seven] 1 sized]
  apply fChain_agrees _ _ _ (TreeMemoryPreservation.store_preserves memory child [seven] 1 sized)
  intro reply written writtenSized
  rw [TreeMemoryOperations.deallocate_agrees written child .heap 1 1 writtenSized]
  apply fChain_agrees _ _ _ (TreeMemoryPreservation.deallocate_preserves written child .heap 1 1 writtenSized)
  intro reply dead deadSized
  exact TreeMemoryReleaseAgreement.release_agrees dead (0, [0, 0]) deadSized

theorem weak_lifecycle : rLifecycle (TreeMemoryControls.readState .weak) TreeMemoryControls.t =
    .ok () TreeMemoryControls.deadWeakReleased := by
  unfold rLifecycle
  rw [TreeMemoryControls.actual_weak_write]
  simp only [TreeMemoryControls.chain]
  rw [TreeMemoryControls.weak_used_grandchild_allows_free]
  exact TreeMemoryControls.successful_dead_weak_release

def rebornRoot : TreeMemory.Pointer := ⟨16, some (1, [])⟩
def reborn : TreeMemory.State :=
  { TreeMemory.setTree TreeMemoryControls.deadWeakReleased 1 (TreeAllocation.referenceRoot 1) with
    raw := MiniRustReference.append TreeMemoryControls.deadWeakReleased.raw (TreeMemoryControls.block 1) }

theorem reallocate_dead : TreeMemory.allocateAt TreeMemoryControls.deadWeakReleased .heap 1 1 16 =
    .ok rebornRoot reborn := rfl

def rWeakReallocate : TreeMemory.Result TreeMemory.Pointer :=
  TreeMemoryControls.chain (rBornConstruct .weak) fun child memory =>
    TreeMemoryControls.chain (rLifecycle memory child) fun _ dead =>
      TreeMemory.allocateAt dead .heap 1 1 16

def fWeakReallocate : TreeFactoredMemory.Result TreeMemory.Pointer :=
  fChain (fBornConstruct .weak) fun child memory =>
    fChain (fLifecycle memory child) fun _ dead =>
      TreeFactoredMemory.allocateAt dead .heap 1 1 16

theorem reference_weak_reallocation : rWeakReallocate = .ok rebornRoot reborn := by
  unfold rWeakReallocate
  rw [reference_born_weak]
  simp only [TreeMemoryControls.chain]
  rw [weak_lifecycle]
  exact reallocate_dead

theorem weakReallocate_sized : TreeFactoredMemory.WellSized fWeakReallocate.residual := by
  unfold fWeakReallocate
  apply fChain_sized _ _ (bornConstruct_sized .weak)
  intro child memory sized
  apply fChain_sized _ _ (lifecycle_sized memory child sized)
  intro reply dead deadSized
  exact TreeAllocationDomain.factored_preserves_width dead .heap 1 1 16 deadSized

theorem weakReallocate_agrees : rWeakReallocate = TreeFactoredMemory.translate fWeakReallocate := by
  unfold rWeakReallocate fWeakReallocate
  rw [bornConstruct_agrees]
  apply fChain_agrees _ _ _ (bornConstruct_sized .weak)
  intro child memory sized
  rw [lifecycle_agrees memory child sized]
  apply fChain_agrees _ _ _ (lifecycle_sized memory child sized)
  intro reply dead deadSized
  exact TreeAllocation.allocateAt_agrees dead .heap 1 1 16

theorem factored_weak_reallocation : TreeFactoredMemory.translate fWeakReallocate =
    .ok rebornRoot reborn := by
  rw [← weakReallocate_agrees]
  exact reference_weak_reallocation

/-- Numeric address 16 is reused, allocation ID 0 remains dead, its stale
Weak tree and registration survive, and only ID 1 receives the fresh root. -/
theorem reused_address_keeps_old : rebornRoot.addr = root.addr ∧
    rebornRoot.provenance = some (1, []) ∧ reborn.raw.next = 2 ∧
    reborn.raw.allocations 0 = some { TreeMemoryControls.writtenBlock with live := false } ∧
    reborn.trees 0 = some TreeMemoryControls.treeDeadWeakReleased ∧
    reborn.trees 1 = some (TreeAllocation.referenceRoot 1) ∧
    reborn.currentFrame = [(0, [0, 0])] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stale_root_is_dead : TreeMemory.load reborn root 1 1 = .ub (.basic .dead) reborn := rfl

def rStaleAfterReallocation : TreeMemory.Result (List MiniRustReference.Byte) :=
  TreeMemoryControls.chain rWeakReallocate (fun _ memory => TreeMemory.load memory root 1 1)

def fStaleAfterReallocation : TreeFactoredMemory.Result (List MiniRustReference.Byte) :=
  fChain fWeakReallocate (fun _ memory => TreeFactoredMemory.load memory root 1 1)

theorem actual_stale_failure : rStaleAfterReallocation = .ub (.basic .dead) reborn ∧
    TreeFactoredMemory.translate fStaleAfterReallocation = .ub (.basic .dead) reborn := by
  have reference : rStaleAfterReallocation = .ub (.basic .dead) reborn := by
    unfold rStaleAfterReallocation
    rw [reference_weak_reallocation]
    exact stale_root_is_dead
  refine ⟨reference, ?_⟩
  have agreement : rStaleAfterReallocation = TreeFactoredMemory.translate fStaleAfterReallocation := by
    unfold rStaleAfterReallocation fStaleAfterReallocation
    rw [weakReallocate_agrees]
    apply fChain_agrees _ _ _ weakReallocate_sized
    intro pointer memory sized
    exact TreeMemoryOperations.load_agrees memory root 1 1 sized
  rw [← agreement]
  exact reference

/-- The existing live allocation is zero-sized, but its base still excludes
candidate 16 for a later nonempty block. R and actual F sequences retain the
first birth state on noChoice; this is not global exhaustion. -/
theorem zst_then_nonempty_same_base :
    TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 0 1 16)
        (fun _ memory => TreeMemory.allocateAt memory .heap 1 1 16) = .noChoice (initial 0) ∧
    TreeFactoredMemory.translate
      (fChain (TreeFactoredMemory.allocateAt factoredEmpty .heap 0 1 16)
        (fun _ memory => TreeFactoredMemory.allocateAt memory .heap 1 1 16)) = .noChoice (initial 0) := by
  have reference :
      TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 0 1 16)
        (fun _ memory => TreeMemory.allocateAt memory .heap 1 1 16) = .noChoice (initial 0) := by
    rw [zero_birth.1]
    rfl
  refine ⟨reference, ?_⟩
  have agreement :
      TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 0 1 16)
          (fun _ memory => TreeMemory.allocateAt memory .heap 1 1 16) =
        TreeFactoredMemory.translate
          (fChain (TreeFactoredMemory.allocateAt factoredEmpty .heap 0 1 16)
            (fun _ memory => TreeFactoredMemory.allocateAt memory .heap 1 1 16)) := by
    rw [← empty_reify, TreeAllocation.allocateAt_agrees]
    apply fChain_agrees _ _ _
      (TreeAllocationDomain.factored_preserves_width factoredEmpty .heap 0 1 16 empty_sized)
    intro pointer memory sized
    exact TreeAllocation.allocateAt_agrees memory .heap 1 1 16
  rw [← agreement]
  exact reference

/-- Conversely, a new zero-size block cannot use the live nonempty block's
base 16. Empty requested size does not bypass the allocator's same-base rule. -/
theorem nonempty_then_zst_same_base :
    TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 1 1 16)
        (fun _ memory => TreeMemory.allocateAt memory .heap 0 1 16) = .noChoice (initial 1) ∧
    TreeFactoredMemory.translate
      (fChain (TreeFactoredMemory.allocateAt factoredEmpty .heap 1 1 16)
        (fun _ memory => TreeFactoredMemory.allocateAt memory .heap 0 1 16)) = .noChoice (initial 1) := by
  have reference :
      TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 1 1 16)
        (fun _ memory => TreeMemory.allocateAt memory .heap 0 1 16) = .noChoice (initial 1) := by
    rw [reference_birth_one]
    rfl
  refine ⟨reference, ?_⟩
  have agreement :
      TreeMemoryControls.chain (TreeMemory.allocateAt referenceEmpty .heap 1 1 16)
          (fun _ memory => TreeMemory.allocateAt memory .heap 0 1 16) =
        TreeFactoredMemory.translate
          (fChain (TreeFactoredMemory.allocateAt factoredEmpty .heap 1 1 16)
            (fun _ memory => TreeFactoredMemory.allocateAt memory .heap 0 1 16)) := by
    rw [← empty_reify, TreeAllocation.allocateAt_agrees]
    apply fChain_agrees _ _ _
      (TreeAllocationDomain.factored_preserves_width factoredEmpty .heap 1 1 16 empty_sized)
    intro pointer memory sized
    exact TreeAllocation.allocateAt_agrees memory .heap 0 1 16
  rw [← agreement]
  exact reference

#print axioms empty_reify
#print axioms empty_sized
#print axioms reference_birth_one
#print axioms factored_birth_one
#print axioms birth_domains
#print axioms initial_set_root
#print axioms initial_load_uninit
#print axioms fChain_sized
#print axioms fChain_agrees
#print axioms reference_born_load
#print axioms factored_born_load
#print axioms constructFrom_sized
#print axioms constructFrom_agrees
#print axioms bornConstruct_sized
#print axioms bornConstruct_agrees
#print axioms reference_born_strong
#print axioms reference_born_weak
#print axioms factored_born_strong
#print axioms zero_birth
#print axioms factored_zero_birth
#print axioms live_candidate_discriminator
#print axioms factored_live_candidate_discriminator
#print axioms lifecycle_sized
#print axioms lifecycle_agrees
#print axioms weak_lifecycle
#print axioms reallocate_dead
#print axioms reference_weak_reallocation
#print axioms weakReallocate_sized
#print axioms weakReallocate_agrees
#print axioms factored_weak_reallocation
#print axioms reused_address_keeps_old
#print axioms stale_root_is_dead
#print axioms actual_stale_failure

#print axioms zst_then_nonempty_same_base
#print axioms nonempty_then_zst_same_base

end AnnealResearch.TreeAllocationControls
