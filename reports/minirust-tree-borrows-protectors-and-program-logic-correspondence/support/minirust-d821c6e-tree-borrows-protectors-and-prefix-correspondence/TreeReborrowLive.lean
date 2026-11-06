import AnnealResearch.TreeReborrowClient
import AnnealResearch.TreeReborrowKinds
import AnnealResearch.TreeLivePrefixes

/-!
Positive reference matching for the separate reborrow/pointer-reply client.
The old complete configuration types are aliases, so its existing RConfigKinds
predicate is reused unchanged. Actual dispatch uses the old base dispatcher or
actual reborrow; successful resume applies the continuation to the real reply,
including returned pointers. No new operation or controller runner is defined.

Only initial RConfigKinds is required for finite-prefix preservation. Running
and finished boundaries match; terminal UB/unsupported keep their exact memory
without matching obligations, and noChoice has no successor. This is neither a
NoUB nor progress claim. New factored-prefix transfer waits for checked new
prefix correspondence and is deliberately absent from this module.
-/

namespace AnnealResearch.TreeReborrowLive

universe u
open TreeReborrowClient
open TreeLiveKinds (LiveKinds)
open TreeLiveRelease (RunningKinds)
open TreeLivePrefixes (RConfigKinds)

/-- Map only the actual reply. Reborrow's all-residual theorem supplies the
stronger primitive result before weakening to the stable-running observer. -/
theorem dispatch_preserves (memory : TreeMemory.State) (command : Command)
    (matching : LiveKinds memory) : RunningKinds (rDispatch memory command) := by
  cases command with
  | base command =>
    exact TreeLivePrefixes.map_runningKinds Reply.base _
      (TreeLivePrefixes.dispatch_preserves memory command matching)
  | reborrow pointer settings =>
    exact TreeLivePrefixes.map_runningKinds Reply.pointer _
      (TreeLiveRelease.resultLiveKinds_implies_runningKinds _
        (TreeReborrowKinds.reborrow_preserves_all memory pointer settings matching))

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

theorem step_preserves {S : Type u} (controller : Controller S)
    (config successor : RConfig S) (matching : RConfigKinds config)
    (stepped : rStep controller config = some successor) : RConfigKinds successor := by
  cases config with
  | running control memory =>
    cases decision : controller control with
    | halt result =>
      simp only [rStep, decision] at stepped
      rw [← Option.some.inj stepped]
      exact matching
    | internal next =>
      simp only [rStep, decision] at stepped
      rw [← Option.some.inj stepped]
      exact matching
    | call command next =>
      apply resume_preserves control next (rDispatch memory command) successor
        (dispatch_preserves memory command matching)
      simpa only [rStep, decision] using stepped
  | finished control result memory => cases stepped
  | ub control fault memory => cases stepped
  | unsupported control reason memory => cases stepped

/-- Arbitrary actual exact-n prefixes, including horizon zero and reached
terminal configurations. The output equation is an observation of execution,
not admission that commands succeed, avoid UB or eventually finish. -/
theorem prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : RConfig S) (matching : RConfigKinds initial)
    (observed : rIterate controller count initial = some reached) : RConfigKinds reached := by
  induction count generalizing initial with
  | zero =>
    have same : initial = reached := Option.some.inj observed
    rw [← same]
    exact matching
  | succ count ih =>
    cases stepped : rStep controller initial with
    | none =>
      simp only [rIterate, TreeMemoryClient.iterate, stepped, Option.bind_none] at observed
      cases observed
    | some next =>
      have nextMatching := step_preserves controller initial next matching stepped
      apply ih next nextMatching
      simpa only [rIterate, TreeMemoryClient.iterate, stepped, Option.bind_some] using observed

#print axioms dispatch_preserves
#print axioms resume_preserves
#print axioms step_preserves
#print axioms prefix_preserves

end AnnealResearch.TreeReborrowLive
