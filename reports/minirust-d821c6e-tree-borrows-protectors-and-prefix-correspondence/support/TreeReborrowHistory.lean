import AnnealResearch.TreeReborrowLive
import AnnealResearch.TreeReborrowPrefixes
import AnnealResearch.TreeMemoryPairing
import AnnealResearch.TreeLiveKindControls

/-!
A concrete owned-operation history consumes actual reborrow pointer replies.
It constructs two siblings and a protected grandchild, stores through the returned
protected pointer, releases it, frees its allocation, then finishes. This is a
scoped client witness, not an arbitrary-controller or Rust/source safety claim.
The matching predicate supplies no frame/protector obligation; release retains
the existing registration list and deallocation retains dead records.
-/
namespace AnnealResearch.TreeReborrowHistory

open TreePermissions
open TreeReborrowClient

inductive Control where
  | start
  | sibling (first : TreeMemory.Pointer)
  | protect (first : TreeMemory.Pointer)
  | write (child : TreeMemory.Pointer)
  | release (child : TreeMemory.Pointer)
  | free (child : TreeMemory.Pointer)
  | done
  | wrongReply

def unitNext (next : Control) : Reply → Control
  | .base .unit => next
  | _ => .wrongReply

def controller : Controller Control
  | .start => .call (.reborrow TreeMemoryControls.root TreeMemoryControls.mutable)
      (fun reply => match reply with | .pointer first => .sibling first | _ => .wrongReply)
  | .sibling first => .call (.reborrow TreeMemoryControls.root TreeMemoryControls.mutable)
      (fun reply => match reply with | .pointer _ => .protect first | _ => .wrongReply)
  | .protect first => .call (.reborrow first (TreeMemoryControls.protectedMutable .strong))
      (fun reply => match reply with | .pointer child => .write child | _ => .wrongReply)
  | .write child => .call (.base (.store child [TreeMemoryControls.seven] 1))
      (unitNext (.release child))
  | .release child => match child.provenance with
      | none => .halt 99
      | some provenance => .call (.base (.release provenance)) (unitNext (.free child))
  | .free child => .call (.base (.free child .heap 1 1)) (unitNext .done)
  | .done => .halt 7
  | .wrongReply => .halt 999

def c0 : RConfig Control := .running .start (TreeMemoryControls.initial 1)
def c1 : RConfig Control := .running (.sibling TreeMemoryControls.a) TreeMemoryControls.stateA
def c2 : RConfig Control := .running (.protect TreeMemoryControls.a) TreeMemoryControls.stateAB
def c3 : RConfig Control := .running (.write TreeMemoryControls.t) (TreeMemoryControls.readState .strong)
def c4 : RConfig Control := .running (.release TreeMemoryControls.t) (TreeMemoryControls.writeState .strong)
def c5 : RConfig Control := .running (.free TreeMemoryControls.t) TreeMemoryControls.releasedState
def freed : TreeMemory.State := TreeMemoryControls.freed TreeMemoryControls.releasedState
  TreeMemoryControls.treeReleased TreeMemoryControls.writtenBlock
def c6 : RConfig Control := .running .done freed
def c7 : RConfig Control := .finished .done 7 freed

theorem step0 : rStep controller c0 = some c1 := by
  simp only [c0, c1, rStep, controller, rDispatch, TreeMemoryControls.construct_a,
    TreeMemoryClient.rMap, rResume]

theorem step1 : rStep controller c1 = some c2 := by
  simp only [c1, c2, rStep, controller, rDispatch, TreeMemoryControls.construct_b,
    TreeMemoryClient.rMap, rResume]

theorem step2 : rStep controller c2 = some c3 := by
  simp only [c2, c3, rStep, controller, rDispatch, TreeMemoryControls.construct_t_strong,
    TreeMemoryClient.rMap, rResume]

theorem step3 : rStep controller c3 = some c4 := by
  simp only [c3, c4, rStep, controller, rDispatch, TreeMemoryClient.rDispatch,
    TreeMemoryControls.actual_strong_write, TreeMemoryClient.rMap, rResume, unitNext]

theorem step4 : rStep controller c4 = some c5 := by
  simp only [c4, c5, rStep, controller, TreeMemoryControls.t, rDispatch,
    TreeMemoryClient.rDispatch, TreeMemoryControls.successful_live_release,
    TreeMemoryClient.rMap, rResume, unitNext]

theorem step5 : rStep controller c5 = some c6 := by
  simp only [c5, c6, freed, rStep, controller, rDispatch, TreeMemoryClient.rDispatch,
    TreeMemoryControls.free_after_release, TreeMemoryClient.rMap, rResume, unitNext]

theorem step6 : rStep controller c6 = some c7 := rfl

theorem seven_step_history : rIterate controller 7 c0 = some c7 := by
  simp only [rIterate, TreeMemoryClient.iterate, step0, step1, step2, step3,
    step4, step5, step6, Option.bind_some]

/-- Backward safety through an actual transition. Its local transition equation
is derived from concrete execution above; it is not the general client's input. -/
theorem noUB_before_step (before after : RConfig Control)
    (actual : rStep controller before = some after)
    (currentSafe : ¬ TreeMemoryClient.RConfig.IsUB before)
    (laterSafe : RNoUB controller after) : RNoUB controller before := by
  intro count reached observed bad
  cases count with
  | zero =>
    have same : before = reached := Option.some.inj observed
    exact currentSafe (by rw [same]; exact bad)
  | succ count =>
    have tail : rIterate controller count after = some reached := by
      simpa only [rIterate, TreeMemoryClient.iterate, actual, Option.bind_some] using observed
    exact laterSafe count reached tail bad

theorem finished_NoUB : RNoUB controller c7 := by
  intro count reached observed bad
  cases count with
  | zero =>
    have same : c7 = reached := Option.some.inj observed
    rw [← same] at bad
    exact bad
  | succ count =>
    simp only [rIterate, TreeMemoryClient.iterate, c7, rStep, Option.bind_none] at observed
    cases observed

theorem constructed_history_NoUB : RNoUB controller c0 := by
  apply noUB_before_step c0 c1 step0 (by intro bad; exact bad)
  apply noUB_before_step c1 c2 step1 (by intro bad; exact bad)
  apply noUB_before_step c2 c3 step2 (by intro bad; exact bad)
  apply noUB_before_step c3 c4 step3 (by intro bad; exact bad)
  apply noUB_before_step c4 c5 step4 (by intro bad; exact bad)
  apply noUB_before_step c5 c6 step5 (by intro bad; exact bad)
  exact noUB_before_step c6 c7 step6 (by intro bad; exact bad) finished_NoUB

theorem initial_matching : TreeLivePrefixes.RConfigKinds c0 := by
  apply TreeLiveKindControls.single_tree_live _ (.mk [.unprot .unique] .no [])
  · intro id
    simp [TreeMemoryControls.initial]
  · simp [TreeReference.kindsMatch, TreeReference.childrenMatch,
      Permission.matchesProtector, Permission.isProt, Protected.yes]

theorem stable_history_matching (count : Nat) (reached : RConfig Control)
    (observed : rIterate controller count c0 = some reached) :
    TreeLivePrefixes.RConfigKinds reached :=
  TreeReborrowLive.prefix_preserves controller count c0 reached initial_matching observed

def fmemory : TreeFactoredMemory.State :=
  TreeMemoryPairing.single (TreeMemoryControls.block 1)
    (TreeFactoredMemory.reborrowChild [.unprot .unique] .no) []
def f0 : FConfig Control := .running .start fmemory

theorem initial_reifies : reifyConfig f0 = c0 := by
  change TreeMemoryClient.RConfig.running .start (TreeFactoredMemory.reify fmemory) = c0
  unfold c0 fmemory TreeMemoryPairing.single TreeFactoredMemory.reify TreeMemoryControls.initial
  congr 2
  funext id
  by_cases zero : id = 0
  · subst id
    simp [TreeFactoredReborrow.child_reify]
  · simp [zero]

theorem initial_sized : ConfigWellSized f0 := by
  apply TreeMemoryPairing.single_sized
  apply TreeFactoredReborrow.child_uniform
  rfl

/-- Actual F execution reaches some full state with precisely the constructed
reference outcome. No fallback or default extracts a successful result. -/
theorem factored_seven_step_history :
    ∃ reached, fIterate controller 7 f0 = some reached ∧
      reifyConfig reached = c7 ∧ ConfigWellSized reached := by
  have agreement := TreeReborrowPrefixes.prefix_agrees controller 7 f0 initial_sized
  rw [initial_reifies, seven_step_history] at agreement
  cases actual : fIterate controller 7 f0 with
  | none => rw [actual] at agreement; cases agreement
  | some reached =>
    rw [actual, Option.map_some] at agreement
    refine ⟨reached, rfl, (Option.some.inj agreement).symm, ?_⟩
    exact TreeReborrowPrefixes.prefix_preserves controller 7 f0 reached initial_sized actual

theorem factored_constructed_NoUB : FNoUB controller f0 := by
  apply (TreeReborrowPrefixes.noUB_iff controller f0 initial_sized).1
  rw [initial_reifies]
  exact constructed_history_NoUB

#print axioms step0
#print axioms step1
#print axioms step2
#print axioms step3
#print axioms step4
#print axioms step5
#print axioms step6
#print axioms seven_step_history
#print axioms noUB_before_step
#print axioms finished_NoUB
#print axioms constructed_history_NoUB
#print axioms initial_matching
#print axioms stable_history_matching
#print axioms initial_reifies
#print axioms initial_sized
#print axioms factored_seven_step_history
#print axioms factored_constructed_NoUB

end AnnealResearch.TreeReborrowHistory
