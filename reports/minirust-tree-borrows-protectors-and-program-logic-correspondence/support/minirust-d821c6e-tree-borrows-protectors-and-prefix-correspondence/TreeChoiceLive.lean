import AnnealResearch.TreeChoiceClient
import AnnealResearch.TreeReborrowLive
import AnnealResearch.TreeAllocationDomain

/-!
Stable matching for every actual candidate edge and relational finite prefix.
The reference theorem requires only initial running/finished matching. Errors
retain exact memory without that matching obligation. Allocation uses its
separate all-result live theorem; this does not assert NoUB, progress or source
admission. Factored transfer waits for separate checked prefix correspondence.
-/

namespace AnnealResearch.TreeChoiceLive

universe u
open TreeChoiceClient
open TreeLiveKinds (LiveKinds)
open TreeLiveRelease (RunningKinds)
open TreeLivePrefixes (RConfigKinds)

theorem dispatch_preserves (candidate : Nat) (memory : TreeMemory.State) (command : Command)
    (matching : LiveKinds memory) : RunningKinds (rDispatch candidate memory command) := by
  cases command with
  | base command => exact TreeReborrowLive.dispatch_preserves memory command matching
  | allocate kind size align =>
    exact TreeLivePrefixes.map_runningKinds TreeReborrowClient.Reply.pointer _
      (TreeLiveRelease.resultLiveKinds_implies_runningKinds _
        (TreeAllocationDomain.reference_preserves_live memory kind size align candidate matching))

/-- On success, the actual Reply, including Reply.pointer, goes to next.
No pointer is manufactured, defaulted, discarded or replaced by a base reply.
Terminal branches retain the primitive's exact residual memory. -/
theorem resume_preserves {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeMemory.Result Reply) (successor : RConfig S)
    (matching : RunningKinds answer)
    (stepped : rResume control next answer = some successor) : RConfigKinds successor := by
  cases answer with
  | ok reply memory =>
    have same : TreeMemoryClient.RConfig.running (next reply) memory = successor :=
      Option.some.inj stepped
    rw [← same]
    exact matching
  | ub fault memory =>
    have same : TreeMemoryClient.RConfig.ub control fault memory = successor :=
      Option.some.inj stepped
    rw [← same]
    exact True.intro
  | unsupported reason memory =>
    have same : TreeMemoryClient.RConfig.unsupported control reason memory = successor :=
      Option.some.inj stepped
    rw [← same]
    exact True.intro
  | noChoice memory => cases stepped

theorem next_preserves {S : Type u} (controller : Controller S) (candidate : Nat)
    (config successor : RConfig S) (matching : RConfigKinds config)
    (stepped : rNext controller candidate config = some successor) : RConfigKinds successor := by
  cases config with
  | running control memory =>
    cases decision : controller control with
    | halt result =>
      simp only [rNext, decision] at stepped
      rw [← Option.some.inj stepped]
      exact matching
    | internal next =>
      simp only [rNext, decision] at stepped
      rw [← Option.some.inj stepped]
      exact matching
    | call command next =>
      apply resume_preserves control next (rDispatch candidate memory command) successor
        (dispatch_preserves candidate memory command matching)
      simpa only [rNext, decision] using stepped
  | finished control result memory => cases stepped
  | ub control fault memory => cases stepped
  | unsupported control reason memory => cases stepped

theorem step_preserves {S : Type u} (controller : Controller S)
    (config successor : RConfig S) (matching : RConfigKinds config)
    (stepped : RStep controller config successor) : RConfigKinds successor := by
  obtain ⟨candidate, actual⟩ := stepped
  exact next_preserves controller candidate config successor matching actual

/-- The relational prefix quantifies every candidate sequence. No successful
command, width, raw WF, freshness or NoUB admission is added. -/
theorem prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : RConfig S) (matching : RConfigKinds initial)
    (observed : RPrefix controller count initial reached) : RConfigKinds reached := by
  induction count generalizing initial with
  | zero =>
    change reached = initial at observed
    rw [observed]
    exact matching
  | succ count ih =>
    change ∃ middle, RStep controller initial middle ∧
      RPrefix controller count middle reached at observed
    obtain ⟨middle, edge, tail⟩ := observed
    exact ih middle (step_preserves controller initial middle matching edge) tail

#print axioms dispatch_preserves
#print axioms resume_preserves
#print axioms next_preserves
#print axioms step_preserves
#print axioms prefix_preserves

end AnnealResearch.TreeChoiceLive
