import AnnealResearch.TreeLiveRelease
import AnnealResearch.TreeMemoryPrefixAgreement

/-!
Positive matching at every stable running/finished boundary of the unchanged
four-command client. UB/unsupported configurations retain their exact memory
and impose no matching obligation. NoUB is not assumed or concluded. The R
result needs only input live matching; the F corollary also uses the existing
width domain for correspondence. Reborrow/pointer replies are not added here.
-/
namespace AnnealResearch.TreeLivePrefixes

universe u
open TreeMemoryClient
open TreeLiveKinds (LiveKinds)
open TreeLiveRelease (RunningKinds)

def RConfigKinds {S : Type u} : RConfig S → Prop
  | .running _ memory => LiveKinds memory
  | .finished _ _ memory => LiveKinds memory
  | .ub _ _ _ => True
  | .unsupported _ _ _ => True

def FConfigKinds {S : Type u} (config : FConfig S) : Prop :=
  RConfigKinds (reifyConfig config)

theorem map_runningKinds {A B : Type} (f : A → B) (answer : TreeMemory.Result A)
    (matching : RunningKinds answer) : RunningKinds (rMap f answer) := by
  cases answer <;> exact matching

theorem dispatch_preserves (memory : TreeMemory.State) (command : Command)
    (matching : LiveKinds memory) : RunningKinds (rDispatch memory command) := by
  cases command with
  | load pointer size align =>
    exact map_runningKinds _ _ (TreeLiveRelease.load_preserves memory pointer size align matching)
  | store pointer bytes align =>
    exact map_runningKinds _ _ (TreeLiveRelease.store_preserves memory pointer bytes align matching)
  | free pointer kind size align =>
    exact map_runningKinds _ _
      (TreeLiveRelease.deallocate_preserves memory pointer kind size align matching)
  | release provenance =>
    exact map_runningKinds _ _ (TreeLiveRelease.release_preserves memory provenance matching)

theorem resume_preserves {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeMemory.Result Reply) (successor : RConfig S)
    (matching : RunningKinds answer)
    (stepped : rResume control next answer = some successor) : RConfigKinds successor := by
  cases answer with
  | ok reply memory =>
    have same : RConfig.running (next reply) memory = successor := Option.some.inj stepped
    rw [← same]
    exact matching
  | ub fault memory =>
    have same : RConfig.ub control fault memory = successor := Option.some.inj stepped
    rw [← same]
    exact True.intro
  | unsupported reason memory =>
    have same : RConfig.unsupported control reason memory = successor := Option.some.inj stepped
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

/-- The output equation observes an arbitrary actual finite prefix, including
terminal ones. It is not an admission that the controller avoids UB or halts. -/
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
      simp only [rIterate, iterate, stepped, Option.bind_none] at observed
      cases observed
    | some next =>
      have nextMatching := step_preserves controller initial next matching stepped
      apply ih next nextMatching
      simpa only [rIterate, iterate, stepped, Option.bind_some] using observed

/-- Existing exact prefix correspondence transfers the positive invariant.
The operational domain is required only by that correspondence. -/
theorem factored_prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) (sized : ConfigWellSized initial)
    (matching : FConfigKinds initial)
    (observed : fIterate controller count initial = some reached) : FConfigKinds reached := by
  have correspondence := TreeMemoryPrefixAgreement.prefix_agrees controller count initial sized
  rw [observed, Option.map_some] at correspondence
  exact prefix_preserves controller count (reifyConfig initial) (reifyConfig reached)
    matching correspondence

#print axioms map_runningKinds
#print axioms dispatch_preserves
#print axioms resume_preserves
#print axioms step_preserves
#print axioms prefix_preserves
#print axioms factored_prefix_preserves

end AnnealResearch.TreeLivePrefixes
