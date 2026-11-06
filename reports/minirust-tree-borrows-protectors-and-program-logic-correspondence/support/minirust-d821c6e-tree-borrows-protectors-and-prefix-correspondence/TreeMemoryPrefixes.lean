import AnnealResearch.TreeMemoryClient
import AnnealResearch.TreeMemoryPreservation

/-!
Structural-domain and exact-step composition for the fixed reply-only
controller. Every actual some successor participates, including UB and
unsupported configurations with changed memory. noChoice remains absent.
No safety, progress, liveness, path or successful-command premise is added.

This substantial checkpoint establishes dispatch closure, successor closure and
exact one-step reification. Exact-n iteration and NoUB equivalence remain the
next explicitly pending layer after this module is checked.
-/

namespace AnnealResearch.TreeMemoryPrefixes

universe u

open TreeMemoryClient

theorem fMap_residual {A B : Type} (f : A → B) (answer : TreeFactoredMemory.Result A) :
    (fMap f answer).residual = answer.residual := by
  cases answer <;> rfl

theorem dispatch_preserves (memory : TreeFactoredMemory.State) (command : Command)
    (sized : TreeFactoredMemory.WellSized memory) :
    TreeFactoredMemory.WellSized (fDispatch memory command).residual := by
  cases command with
  | load pointer size align =>
      simp only [fDispatch, fMap_residual]
      exact TreeMemoryPreservation.load_preserves memory pointer size align sized
  | store pointer bytes align =>
      simp only [fDispatch, fMap_residual]
      exact TreeMemoryPreservation.store_preserves memory pointer bytes align sized
  | free pointer kind size align =>
      simp only [fDispatch, fMap_residual]
      exact TreeMemoryPreservation.deallocate_preserves memory pointer kind size align sized
  | release provenance =>
      simp only [fDispatch, fMap_residual]
      exact TreeMemoryPreservation.release_preserves memory provenance sized

/-- Actual success/error configurations retain exactly the primitive residual
memory; the success continuation changes only control. noChoice has no witness. -/
theorem resume_memory {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) (successor : FConfig S)
    (stepped : fResume control next answer = some successor) :
    successor.memory = answer.residual := by
  cases answer with
  | ok reply memory =>
      have same : FConfig.running (next reply) memory = successor := Option.some.inj stepped
      rw [← same] <;> rfl
  | ub fault memory =>
      have same : FConfig.ub control fault memory = successor := Option.some.inj stepped
      rw [← same] <;> rfl
  | unsupported reason memory =>
      have same : FConfig.unsupported control reason memory = successor := Option.some.inj stepped
      rw [← same] <;> rfl
  | noChoice memory =>
      simp only [fResume] at stepped
      cases stepped

theorem resume_preserves {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) (successor : FConfig S)
    (sized : TreeFactoredMemory.WellSized answer.residual)
    (stepped : fResume control next answer = some successor) :
    ConfigWellSized successor := by
  unfold ConfigWellSized
  rw [resume_memory control next answer successor stepped]
  exact sized

/-- The some-successor equation observes the actual transition; it is not a
premise that a memory command succeeds. UB/unsupported successors are included. -/
theorem step_preserves {S : Type u} (controller : Controller S)
    (config successor : FConfig S) (sized : ConfigWellSized config)
    (stepped : fStep controller config = some successor) : ConfigWellSized successor := by
  cases config with
  | running control memory =>
      cases decision : controller control with
      | halt result =>
          simp only [fStep, decision] at stepped
          rw [← Option.some.inj stepped]
          exact sized
      | internal next =>
          simp only [fStep, decision] at stepped
          rw [← Option.some.inj stepped]
          exact sized
      | call command next =>
          have resumed : fResume control next (fDispatch memory command) = some successor := by
            simpa only [fStep, decision] using stepped
          exact resume_preserves control next (fDispatch memory command) successor
            (dispatch_preserves memory command sized) resumed
  | finished control result memory =>
      simp only [fStep] at stepped
      cases stepped
  | ub control fault memory =>
      simp only [fStep] at stepped
      cases stepped
  | unsupported control reason memory =>
      simp only [fStep] at stepped
      cases stepped

theorem step_agrees {S : Type u} (controller : Controller S) (config : FConfig S)
    (sized : ConfigWellSized config) :
    rStep controller (reifyConfig config) = (fStep controller config).map reifyConfig := by
  cases config with
  | running control memory =>
      cases decision : controller control with
      | halt result =>
          simp only [reifyConfig, rStep, fStep, decision, Option.map_some] <;> rfl
      | internal next =>
          simp only [reifyConfig, rStep, fStep, decision, Option.map_some] <;> rfl
      | call command next =>
          simp only [reifyConfig, rStep, fStep, decision]
          rw [TreeMemoryClient.dispatch_agrees memory command sized]
          exact reify_resume control next (fDispatch memory command)
  | finished control result memory => rfl
  | ub control fault memory => rfl
  | unsupported control reason memory => rfl

#print axioms fMap_residual
#print axioms dispatch_preserves
#print axioms resume_memory
#print axioms resume_preserves
#print axioms step_preserves
#print axioms step_agrees

end AnnealResearch.TreeMemoryPrefixes
