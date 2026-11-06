import AnnealResearch.TreeReborrowClient

/-!
Exact finite-prefix composition for the separate actual reborrow/pointer-reply
client. The same arbitrary-S deterministic controller sees control/replies only.
Only initial ConfigWellSized is admission. Every actual some successor preserves
the domain, including partial UB/unsupported memories; noChoice has no successor.

The exact-n full-configuration equation includes horizon zero and terminal error
horizons, without terminal stuttering. NoUB equivalence quantifies all finite
prefixes; it is not arbitrary-client safety, progress, termination, fairness,
internal cost, allocator-choice or source/helper/Rust adequacy.
-/

namespace AnnealResearch.TreeReborrowPrefixes

universe u

open TreeReborrowClient

theorem resume_preserves {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) (successor : FConfig S)
    (sized : TreeFactoredMemory.WellSized answer.residual)
    (stepped : fResume control next answer = some successor) :
    ConfigWellSized successor := by
  change TreeFactoredMemory.WellSized successor.memory
  rw [resume_memory control next answer successor stepped]
  exact sized

/-- The successor equation observes the actual step. It includes command UB
and unsupported outcomes and does not assert successful command execution. -/
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
      change rStep controller (.running control (TreeFactoredMemory.reify memory)) =
        (fStep controller (.running control memory)).map reifyConfig
      cases decision : controller control with
      | halt result =>
          simp only [rStep, fStep, decision, Option.map_some] <;> rfl
      | internal next =>
          simp only [rStep, fStep, decision, Option.map_some] <;> rfl
      | call command next =>
          simp only [rStep, fStep, decision]
          rw [dispatch_agrees memory command sized]
          exact reify_resume control next (fDispatch memory command)
  | finished control result memory => rfl
  | ub control fault memory => rfl
  | unsupported control reason memory => rfl

theorem rIterate_succ {S : Type u} (controller : Controller S) (count : Nat)
    (initial : RConfig S) :
    rIterate controller (count + 1) initial =
      (rStep controller initial).bind (fun next => rIterate controller count next) := rfl

theorem fIterate_succ {S : Type u} (controller : Controller S) (count : Nat)
    (initial : FConfig S) :
    fIterate controller (count + 1) initial =
      (fStep controller initial).bind (fun next => fIterate controller count next) := rfl

theorem prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) (sized : ConfigWellSized initial)
    (reachedAt : fIterate controller count initial = some reached) : ConfigWellSized reached := by
  induction count generalizing initial with
  | zero =>
      have same : initial = reached := Option.some.inj reachedAt
      rw [← same]
      exact sized
  | succ count ih =>
      cases first : fStep controller initial with
      | none =>
          have expanded := reachedAt
          rw [fIterate_succ, first] at expanded
          change (none : Option (FConfig S)) = some reached at expanded
          cases expanded
      | some next =>
          have expanded := reachedAt
          rw [fIterate_succ, first] at expanded
          have tail : fIterate controller count next = some reached := expanded
          exact ih next (step_preserves controller initial next sized first) tail

/-- Every exact horizon compares complete resulting control, return/diagnostic
values and residual memory. Call continuations receive the same actual reply;
configurations do not add a separate reply trace. -/
theorem prefix_agrees {S : Type u} (controller : Controller S) (count : Nat)
    (initial : FConfig S) (sized : ConfigWellSized initial) :
    rIterate controller count (reifyConfig initial) =
      (fIterate controller count initial).map reifyConfig := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
      rw [rIterate_succ, fIterate_succ, step_agrees controller initial sized]
      cases first : fStep controller initial with
      | none => rfl
      | some next =>
          change rIterate controller count (reifyConfig next) =
            (fIterate controller count next).map reifyConfig
          exact ih next (step_preserves controller initial next sized first)

theorem related_prefix_agrees {S : Type u} (controller : Controller S) (count : Nat)
    (reference : RConfig S) (initial : FConfig S)
    (related : reference = reifyConfig initial) (sized : ConfigWellSized initial) :
    rIterate controller count reference = (fIterate controller count initial).map reifyConfig := by
  rw [related]
  exact prefix_agrees controller count initial sized

/-- Unsupported or absent successors can satisfy NoUB. Both directions retain
every finite bad prefix, including a UB input at horizon zero. -/
theorem noUB_iff {S : Type u} (controller : Controller S) (initial : FConfig S)
    (sized : ConfigWellSized initial) :
    RNoUB controller (reifyConfig initial) ↔ FNoUB controller initial := by
  constructor
  · intro referenceSafe count reached reachedAt bad
    have referenceReached :
        rIterate controller count (reifyConfig initial) = some (reifyConfig reached) := by
      rw [prefix_agrees controller count initial sized, reachedAt] <;> rfl
    exact referenceSafe count (reifyConfig reached) referenceReached
      ((TreeMemoryClient.reify_isUB reached).2 bad)
  · intro factoredSafe count reached reachedAt bad
    have agreement := prefix_agrees controller count initial sized
    rw [reachedAt] at agreement
    cases factoredAt : fIterate controller count initial with
    | none =>
        rw [factoredAt] at agreement
        cases agreement
    | some factored =>
        rw [factoredAt] at agreement
        have same : reached = reifyConfig factored := Option.some.inj agreement
        have reifiedBad : TreeMemoryClient.RConfig.IsUB (reifyConfig factored) := by
          rw [← same]
          exact bad
        exact factoredSafe count factored factoredAt
          ((TreeMemoryClient.reify_isUB factored).1 reifiedBad)

theorem related_noUB_iff {S : Type u} (controller : Controller S)
    (reference : RConfig S) (initial : FConfig S)
    (related : reference = reifyConfig initial) (sized : ConfigWellSized initial) :
    RNoUB controller reference ↔ FNoUB controller initial := by
  rw [related]
  exact noUB_iff controller initial sized

#print axioms resume_preserves
#print axioms step_preserves
#print axioms step_agrees
#print axioms rIterate_succ
#print axioms fIterate_succ
#print axioms prefix_preserves
#print axioms prefix_agrees
#print axioms related_prefix_agrees
#print axioms noUB_iff
#print axioms related_noUB_iff

end AnnealResearch.TreeReborrowPrefixes
