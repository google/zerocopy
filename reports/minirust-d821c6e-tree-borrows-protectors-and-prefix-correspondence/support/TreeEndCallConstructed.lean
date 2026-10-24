import AnnealResearch.TreeAllocationControls
import AnnealResearch.TreeLiveKindControls
import AnnealResearch.TreeEndCall

/-!
Positive two-allocation construction for ordered end-call controls. R/F
sequencers invoke their actual operations from the existing empty memories.
Each real allocation reply supplies the root of its protected reborrow; the
two real child replies are returned together. Expected complete states below
are explicit maps/trees, never extracted from a presumed successful result.

The one-byte Strong mutable settings are supplied owned data. This does not
compute source settings or prove source frame ownership, Return, Drop, helper
adequacy, progress, all-choice safety or an architecture/cost decision.
-/
namespace AnnealResearch.TreeEndCallConstructed

open TreePermissions
open TreeMemoryControls (chain)
open TreeAllocationControls (fChain)

def block (address : Nat) : MiniRustReference.Allocation :=
  { base := address, size := 1, align := 1, kind := .heap, live := true
    data := fun _ => .uninit }

def rootTree : TreeReference.Node := .mk [.unprot .unique] .no []
def protectedTree : TreeReference.Node :=
  .mk [.unprot .unique] .no [.mk [.prot (.reserved true false)] .strong []]
def convertedTree : TreeReference.Node :=
  .mk [.unprot .unique] .no [.mk [.unprot .reserved] .strong []]
def releasedTree : TreeReference.Node :=
  .mk [.unprot .unique] .no [.mk [.unprot .reserved] .no []]

def settings : TreeMemory.Settings := TreeMemoryControls.protectedMutable .strong
def root0 : TreeMemory.Pointer := ⟨16, some (0, [])⟩
def root1 : TreeMemory.Pointer := ⟨32, some (1, [])⟩
def child0 : TreeMemory.Pointer := ⟨16, some (0, [0])⟩
def child1 : TreeMemory.Pointer := ⟨32, some (1, [0])⟩
def registrations : List TreeMemory.Provenance := [(0, [0]), (1, [0])]

def singleRaw : MiniRustReference.State :=
  { next := 1, allocations := fun id => if id = 0 then some (block 16) else none }
def twoRaw : MiniRustReference.State :=
  { next := 2, allocations := fun id =>
      if id = 1 then some (block 32) else if id = 0 then some (block 16) else none }

def oneRoot : TreeMemory.State :=
  { raw := singleRaw
    trees := fun id => if id = 0 then some rootTree else none
    currentFrame := [] }
def oneProtected : TreeMemory.State :=
  { raw := singleRaw
    trees := fun id => if id = 0 then some protectedTree else none
    currentFrame := [(0, [0])] }
def beforeSecond : TreeMemory.State :=
  { raw := twoRaw
    trees := fun id =>
      if id = 1 then some rootTree else if id = 0 then some protectedTree else none
    currentFrame := [(0, [0])] }

/-- Pure expected-state constructor, independent of every runner. -/
def pairState (first second : TreeReference.Node) : TreeMemory.State :=
  { raw := twoRaw
    trees := fun id => if id = 1 then some second else if id = 0 then some first else none
    currentFrame := registrations }

def before : TreeMemory.State := pairState protectedTree protectedTree
def afterFirst : TreeMemory.State := pairState releasedTree protectedTree
def afterBoth : TreeMemory.State := pairState releasedTree releasedTree

def rConstruct : TreeMemory.Result (TreeMemory.Pointer × TreeMemory.Pointer) :=
  chain (TreeMemory.allocateAt TreeAllocationControls.referenceEmpty .heap 1 1 16)
    fun firstRoot afterBirth =>
      chain (TreeMemory.reborrow afterBirth firstRoot settings) fun firstChild afterFirst =>
        chain (TreeMemory.allocateAt afterFirst .heap 1 1 32) fun secondRoot afterSecond =>
          chain (TreeMemory.reborrow afterSecond secondRoot settings) fun secondChild ready =>
            .ok (firstChild, secondChild) ready

def fConstruct : TreeFactoredMemory.Result (TreeMemory.Pointer × TreeMemory.Pointer) :=
  fChain (TreeFactoredMemory.allocateAt TreeAllocationControls.factoredEmpty .heap 1 1 16)
    fun firstRoot afterBirth =>
      fChain (TreeFactoredMemory.reborrow afterBirth firstRoot settings) fun firstChild afterFirst =>
        fChain (TreeFactoredMemory.allocateAt afterFirst .heap 1 1 32) fun secondRoot afterSecond =>
          fChain (TreeFactoredMemory.reborrow afterSecond secondRoot settings) fun secondChild ready =>
            .ok (firstChild, secondChild) ready

attribute [local simp] TreeMemory.Pointer.basic MiniRustReference.checkPtr
  MiniRustReference.replace TreeReference.addNode TreeReference.modifyAt TreeReference.replaceNth
  TreeReference.arraysSized TreeReference.childrenSized TreeReference.initialAccesses
  TreeReference.access TreeReference.pathPresent TreeReference.findNode
  TreeReference.Node.permissions TreeReference.Node.children TreeReference.Node.protection
  TreeReference.accessCore TreeReference.accessChildren TreeReference.transitionRange
  TreeReference.transitionPrefix TreeReference.nodeRelation TreeReference.childPath
  TreeReference.Result.mapState TreeReference.Result.bind TreeReference.unprotectAt
  TreeReference.unprotectPermissions TreeReference.releaseTraverse TreeReference.releaseCore
  TreeReference.releaseChildren TreeReference.applyAccesses TreeReference.kindsMatch
  TreeReference.childrenMatch Permission.transition Permission.initAccess Permission.matchesProtector
  Permission.isProt Permission.unprotect Protected.yes UPermission.transition UPermission.localRead
  UPermission.localWrite UPermission.foreignRead UPermission.foreignWrite UPermission.initAccess
  PPermission.transition PPermission.localRead PPermission.localWrite PPermission.foreignRead
  PPermission.foreignWrite PPermission.initAccess PPermission.unprotect

theorem first_birth :
    TreeMemory.allocateAt TreeAllocationControls.referenceEmpty .heap 1 1 16 =
      .ok root0 oneRoot := rfl

theorem first_reborrow : TreeMemory.reborrow oneRoot root0 settings =
    .ok child0 oneProtected := by
  simp [TreeMemory.reborrow, oneRoot, root0, settings,
    TreeMemoryControls.protectedMutable, rootTree, protectedTree, oneProtected,
    singleRaw, block, TreeMemory.setTree, child0]
  funext id
  by_cases zero : id = 0 <;> simp [zero]

theorem second_birth : TreeMemory.allocateAt oneProtected .heap 1 1 32 =
    .ok root1 beforeSecond := by
  change TreeMemory.Result.ok root1
    { TreeMemory.setTree oneProtected 1 rootTree with raw := (MiniRustReference.append singleRaw (block 32)) } =
      .ok root1 beforeSecond
  rfl

theorem second_reborrow : TreeMemory.reborrow beforeSecond root1 settings =
    .ok child1 before := by
  simp [TreeMemory.reborrow, beforeSecond, root1, settings,
    TreeMemoryControls.protectedMutable, rootTree, protectedTree, before,
    pairState, registrations, twoRaw, block, TreeMemory.setTree, child1]
  funext id
  by_cases one : id = 1 <;> simp [one]

theorem actual_construction : rConstruct = .ok (child0, child1) before := by
  simp only [rConstruct, first_birth, chain, first_reborrow, second_birth, second_reborrow]

theorem construction_agrees :
    rConstruct = TreeFactoredMemory.translate fConstruct := by
  unfold rConstruct fConstruct
  rw [← TreeAllocationControls.empty_reify, TreeAllocation.allocateAt_agrees]
  apply TreeAllocationControls.fChain_agrees _ _ _
    (TreeAllocationDomain.factored_preserves_width TreeAllocationControls.factoredEmpty
      .heap 1 1 16 TreeAllocationControls.empty_sized)
  intro firstRoot afterBirth birthSized
  rw [TreeReborrowAgreement.reborrow_agrees afterBirth firstRoot settings birthSized]
  apply TreeAllocationControls.fChain_agrees _ _ _
    (TreeReborrowDomain.reborrow_preserves afterBirth firstRoot settings birthSized)
  intro firstChild afterFirst firstSized
  rw [TreeAllocation.allocateAt_agrees afterFirst .heap 1 1 32]
  apply TreeAllocationControls.fChain_agrees _ _ _
    (TreeAllocationDomain.factored_preserves_width afterFirst .heap 1 1 32 firstSized)
  intro secondRoot afterSecond secondSized
  rw [TreeReborrowAgreement.reborrow_agrees afterSecond secondRoot settings secondSized]
  apply TreeAllocationControls.fChain_agrees _ _ _
    (TreeReborrowDomain.reborrow_preserves afterSecond secondRoot settings secondSized)
  intro secondChild ready readySized
  rfl

theorem construction_sized : TreeFactoredMemory.WellSized fConstruct.residual := by
  unfold fConstruct
  apply TreeAllocationControls.fChain_sized _ _
    (TreeAllocationDomain.factored_preserves_width TreeAllocationControls.factoredEmpty
      .heap 1 1 16 TreeAllocationControls.empty_sized)
  intro firstRoot afterBirth birthSized
  apply TreeAllocationControls.fChain_sized _ _
    (TreeReborrowDomain.reborrow_preserves afterBirth firstRoot settings birthSized)
  intro firstChild afterFirst firstSized
  apply TreeAllocationControls.fChain_sized _ _
    (TreeAllocationDomain.factored_preserves_width afterFirst .heap 1 1 32 firstSized)
  intro secondRoot afterSecond secondSized
  apply TreeAllocationControls.fChain_sized _ _
    (TreeReborrowDomain.reborrow_preserves afterSecond secondRoot settings secondSized)
  intro secondChild ready readySized
  exact readySized

/-- Case the actual F result. Its pointer pair is equal because translation
retains values; memory is related only by exact reification. -/
theorem actual_factored_construction :
    ∃ memory, fConstruct = .ok (child0, child1) memory ∧
      TreeFactoredMemory.reify memory = before ∧ TreeFactoredMemory.WellSized memory := by
  have observed : TreeFactoredMemory.translate fConstruct = .ok (child0, child1) before :=
    construction_agrees.symm.trans actual_construction
  have sized := construction_sized
  cases actual : fConstruct with
  | ub fault memory => simp only [actual, TreeFactoredMemory.translate] at observed; cases observed
  | unsupported reason memory =>
    simp only [actual, TreeFactoredMemory.translate] at observed; cases observed
  | noChoice memory => simp only [actual, TreeFactoredMemory.translate] at observed; cases observed
  | ok children memory =>
    simp only [actual, TreeFactoredMemory.translate] at observed
    obtain ⟨sameChildren, represented⟩ := TreeMemory.Result.ok.inj observed
    subst children
    refine ⟨memory, rfl, represented, ?_⟩
    simpa only [actual, TreeFactoredMemory.Result.residual] using sized

theorem protected_unprotect : TreeReference.unprotectAt protectedTree [0] =
    .ok [some .read] convertedTree := by
  simp [protectedTree, convertedTree]

theorem protected_traversal :
    TreeReference.releaseTraverse convertedTree (some [0]) [some .read] =
      .ok () releasedTree := by
  simp [convertedTree, releasedTree]

theorem pair_set_first (first second replacement : TreeReference.Node) :
    TreeMemory.setTree (pairState first second) 0 replacement = pairState replacement second := by
  unfold TreeMemory.setTree pairState
  congr 1
  funext id
  by_cases zero : id = 0
  · subst id; rfl
  · simp [zero]

theorem pair_set_second (first second replacement : TreeReference.Node) :
    TreeMemory.setTree (pairState first second) 1 replacement = pairState first replacement := by
  unfold TreeMemory.setTree pairState
  congr 1
  funext id
  by_cases one : id = 1 <;> simp [one]

theorem first_release : TreeMemory.release before (0, [0]) = .ok () afterFirst := by
  change TreeMemory.release (pairState protectedTree protectedTree) (0, [0]) =
    .ok () (pairState releasedTree protectedTree)
  simp only [TreeMemory.release, pairState, twoRaw, block, Nat.zero_ne_one,
    ite_false, ite_true, protected_unprotect, Bool.not_true, Bool.false_eq_true,
    protected_traversal]
  change TreeMemory.Result.ok ()
    (TreeMemory.setTree (pairState protectedTree protectedTree) 0 releasedTree) = _
  rw [pair_set_first]
  rfl

theorem second_release : TreeMemory.release afterFirst (1, [0]) = .ok () afterBoth := by
  change TreeMemory.release (pairState releasedTree protectedTree) (1, [0]) =
    .ok () (pairState releasedTree releasedTree)
  simp only [TreeMemory.release, pairState, twoRaw, block, ite_true,
    protected_unprotect, Bool.not_true, Bool.false_eq_true, ite_false,
    protected_traversal]
  change TreeMemory.Result.ok ()
    (TreeMemory.setTree (pairState releasedTree protectedTree) 1 releasedTree) = _
  rw [pair_set_second]
  rfl

theorem pair_sized (first second : TreeReference.Node)
    (firstWidth : TreeReference.arraysSized first 1 = true)
    (secondWidth : TreeReference.arraysSized second 1 = true) :
    TreeMemoryEncoding.RWellSized (pairState first second) := by
  intro id allocation tree rawFound treeFound
  by_cases one : id = 1
  · subst id
    have sameAllocation : allocation = block 32 := by
      simpa [pairState, twoRaw] using rawFound.symm
    have sameTree : tree = second := by
      simpa [pairState] using treeFound.symm
    subst allocation
    subst tree
    exact secondWidth
  · by_cases zero : id = 0
    · subst id
      have sameAllocation : allocation = block 16 := by
        simpa [pairState, twoRaw] using rawFound.symm
      have sameTree : tree = first := by
        simpa [pairState] using treeFound.symm
      subst allocation
      subst tree
      exact firstWidth
    · simp [pairState, twoRaw, one, zero] at rawFound

theorem pair_live (first second : TreeReference.Node)
    (firstMatch : TreeReference.kindsMatch first = true)
    (secondMatch : TreeReference.kindsMatch second = true) :
    TreeLiveKinds.LiveKinds (pairState first second) := by
  intro id allocation tree rawFound alive treeFound
  by_cases one : id = 1
  · subst id
    have sameTree : tree = second := by
      simpa [pairState] using treeFound.symm
    subst tree
    exact secondMatch
  · by_cases zero : id = 0
    · subst id
      have sameTree : tree = first := by
        simpa [pairState] using treeFound.symm
      subst tree
      exact firstMatch
    · simp [pairState, one, zero] at treeFound

theorem all_stage_widths :
    TreeMemoryEncoding.RWellSized before ∧ TreeMemoryEncoding.RWellSized afterFirst ∧
      TreeMemoryEncoding.RWellSized afterBoth := by
  have protectedWidth : TreeReference.arraysSized protectedTree 1 = true := by simp [protectedTree]
  have releasedWidth : TreeReference.arraysSized releasedTree 1 = true := by simp [releasedTree]
  exact ⟨pair_sized _ _ protectedWidth protectedWidth,
    pair_sized _ _ releasedWidth protectedWidth, pair_sized _ _ releasedWidth releasedWidth⟩

theorem all_stage_liveKinds :
    TreeLiveKinds.LiveKinds before ∧ TreeLiveKinds.LiveKinds afterFirst ∧
      TreeLiveKinds.LiveKinds afterBoth := by
  have protectedMatch : TreeReference.kindsMatch protectedTree = true := by simp [protectedTree]
  have releasedMatch : TreeReference.kindsMatch releasedTree = true := by simp [releasedTree]
  exact ⟨pair_live _ _ protectedMatch protectedMatch,
    pair_live _ _ releasedMatch protectedMatch, pair_live _ _ releasedMatch releasedMatch⟩

theorem nonempty_distinct_registered :
    child0.provenance = some (0, [0]) ∧ child1.provenance = some (1, [0]) ∧
      (0 : Nat) ≠ 1 ∧ before.currentFrame = registrations ∧
      before.raw.allocations 0 = some (block 16) ∧
      before.raw.allocations 1 = some (block 32) ∧
      (block 16).live = true ∧ (block 32).live = true ∧
      protectedTree.permissions.length = 1 ∧
      (TreeReference.findNode protectedTree [0]).map TreeReference.Node.permissions =
        some [.prot (.reserved true false)] := by
  refine ⟨rfl, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [protectedTree]

theorem releases_change_both :
    (TreeReference.findNode protectedTree [0]).map TreeReference.Node.protection = some .strong ∧
      (TreeReference.findNode releasedTree [0]).map TreeReference.Node.protection = some .no ∧
      (TreeReference.findNode releasedTree [0]).map TreeReference.Node.permissions =
        some [.unprot .reserved] ∧
      afterFirst.raw = before.raw ∧ afterBoth.raw = before.raw ∧
      afterFirst.currentFrame = before.currentFrame ∧ afterBoth.currentFrame = before.currentFrame := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [protectedTree, releasedTree]

def extra : TreeEndCall.SuppliedFrameExtra := ⟨registrations⟩

/-- The actual children supply the list entries. An absent provenance is an
explicit unsuccessful test-sequencer result, never a fabricated registration. -/
def rReleaseChildren (children : TreeMemory.Pointer × TreeMemory.Pointer)
    (memory : TreeMemory.State) : TreeMemory.Result Unit :=
  match children.1.provenance, children.2.provenance with
  | some first, some second => TreeEndCall.rEndCall memory ⟨[first, second]⟩
  | _, _ => .unsupported .basicRepresentation memory

def fReleaseChildren (children : TreeMemory.Pointer × TreeMemory.Pointer)
    (memory : TreeFactoredMemory.State) : TreeFactoredMemory.Result Unit :=
  match children.1.provenance, children.2.provenance with
  | some first, some second => TreeEndCall.fEndCall memory ⟨[first, second]⟩
  | _, _ => .unsupported .basicRepresentation memory

def rSequence : TreeMemory.Result Unit := chain rConstruct rReleaseChildren
def fSequence : TreeFactoredMemory.Result Unit := fChain fConstruct fReleaseChildren

theorem actual_endCall : TreeEndCall.rEndCall before extra = .ok () afterBoth := by
  simp only [TreeEndCall.rEndCall, extra, registrations, TreeEndCall.rReleaseList,
    first_release, second_release]

theorem actual_sequence : rSequence = .ok () afterBoth := by
  simp only [rSequence, actual_construction, chain]
  exact actual_endCall

/-- The example's supplied value equals the actual recorded list; the core
still accepts it independently and does not mutate that memory field. -/
theorem actual_supplied_registrations :
    rReleaseChildren (child0, child1) before = TreeEndCall.rEndCall before extra ∧
      extra.protectors = before.currentFrame ∧
      afterBoth.currentFrame = registrations := ⟨rfl, rfl, rfl⟩

theorem releaseChildren_agrees (memory : TreeFactoredMemory.State)
    (children : TreeMemory.Pointer × TreeMemory.Pointer)
    (sized : TreeFactoredMemory.WellSized memory) :
    rReleaseChildren children (TreeFactoredMemory.reify memory) =
      TreeFactoredMemory.translate (fReleaseChildren children memory) := by
  unfold rReleaseChildren fReleaseChildren
  cases first : children.1.provenance with
  | none => rfl
  | some firstEntry =>
    cases second : children.2.provenance with
    | none => rfl
    | some secondEntry =>
      exact TreeEndCall.endCall_agrees memory ⟨[firstEntry, secondEntry]⟩ sized

theorem sequence_agrees : rSequence = TreeFactoredMemory.translate fSequence := by
  unfold rSequence fSequence
  rw [construction_agrees]
  apply TreeAllocationControls.fChain_agrees _ _ _ construction_sized
  intro children memory sized
  exact releaseChildren_agrees memory children sized

/-- Local observed-success lifting, retaining the actual F successor and its
width. This does not cancel full-memory reification or assume public success. -/
theorem factored_release_success (memory : TreeFactoredMemory.State)
    (entry : TreeMemory.Provenance) (expected : TreeMemory.State)
    (sized : TreeFactoredMemory.WellSized memory)
    (observed : TreeMemory.release (TreeFactoredMemory.reify memory) entry = .ok () expected) :
    ∃ after, TreeFactoredMemory.release memory entry = .ok () after ∧
      TreeFactoredMemory.reify after = expected ∧ TreeFactoredMemory.WellSized after := by
  have represented := (TreeMemoryReleaseAgreement.release_agrees memory entry sized).symm.trans observed
  have width := TreeMemoryPreservation.release_preserves memory entry sized
  cases actual : TreeFactoredMemory.release memory entry with
  | ub fault after => simp only [actual, TreeFactoredMemory.translate] at represented; cases represented
  | unsupported reason after =>
    simp only [actual, TreeFactoredMemory.translate] at represented; cases represented
  | noChoice after => simp only [actual, TreeFactoredMemory.translate] at represented; cases represented
  | ok reply after =>
    cases reply
    simp only [actual, TreeFactoredMemory.translate] at represented
    have same := (TreeMemory.Result.ok.inj represented).2
    refine ⟨after, rfl, same, ?_⟩
    simpa only [actual, TreeMemoryDomain.ResultWellSized,
      TreeFactoredMemory.Result.residual] using width

/-- One actual F construction, its two actual release successes and its actual
fold/whole-sequence result. Only represented memory equality is claimed.
Concrete successful matching openly shares the explicit reference query. -/
theorem actual_factored_two_releases :
    ∃ ready first last,
      fConstruct = .ok (child0, child1) ready ∧
      TreeFactoredMemory.reify ready = before ∧ TreeFactoredMemory.WellSized ready ∧
      TreeFactoredMemory.release ready (0, [0]) = .ok () first ∧
      TreeFactoredMemory.reify first = afterFirst ∧
      TreeFactoredMemory.release first (1, [0]) = .ok () last ∧
      TreeFactoredMemory.reify last = afterBoth ∧
      TreeEndCall.fEndCall ready extra = .ok () last ∧
      fSequence = .ok () last ∧ TreeFactoredMemory.WellSized last ∧
      TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify last) ∧
      last.raw = ready.raw ∧ last.currentFrame = ready.currentFrame ∧
      ready.currentFrame = registrations := by
  obtain ⟨ready, constructed, representedReady, readySized⟩ := actual_factored_construction
  obtain ⟨first, releasedFirst, representedFirst, firstSized⟩ :=
    factored_release_success ready (0, [0]) afterFirst readySized
      (by rw [representedReady]; exact first_release)
  obtain ⟨last, releasedLast, representedLast, lastSized⟩ :=
    factored_release_success first (1, [0]) afterBoth firstSized
      (by rw [representedFirst]; exact second_release)
  have folded : TreeEndCall.fEndCall ready extra = .ok () last := by
    simp only [TreeEndCall.fEndCall, extra, registrations, TreeEndCall.fReleaseList,
      releasedFirst, releasedLast]
  have sequenced : fSequence = .ok () last := by
    simp only [fSequence, constructed, fChain]
    exact folded
  have matching : TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify last) := by
    rw [representedLast]
    exact all_stage_liveKinds.2.2
  have retained : (last.raw, last.currentFrame) = (ready.raw, ready.currentFrame) := by
    have observed := TreeEndCall.fEndCall_retains ready extra
    rw [folded] at observed
    exact observed
  have supplied : ready.currentFrame = registrations :=
    congrArg TreeMemory.State.currentFrame representedReady
  exact ⟨ready, first, last, constructed, representedReady, readySized,
    releasedFirst, representedFirst, releasedLast, representedLast,
    folded, sequenced, lastSized, matching,
    congrArg Prod.fst retained, congrArg Prod.snd retained, supplied⟩

#print axioms first_birth
#print axioms first_reborrow
#print axioms second_birth
#print axioms second_reborrow
#print axioms actual_construction
#print axioms construction_agrees
#print axioms construction_sized
#print axioms actual_factored_construction
#print axioms protected_unprotect
#print axioms protected_traversal
#print axioms pair_set_first
#print axioms pair_set_second
#print axioms first_release
#print axioms second_release
#print axioms pair_sized
#print axioms pair_live
#print axioms all_stage_widths
#print axioms all_stage_liveKinds
#print axioms nonempty_distinct_registered
#print axioms releases_change_both
#print axioms actual_endCall
#print axioms actual_sequence
#print axioms actual_supplied_registrations
#print axioms releaseChildren_agrees
#print axioms sequence_agrees
#print axioms factored_release_success
#print axioms actual_factored_two_releases

end AnnealResearch.TreeEndCallConstructed
