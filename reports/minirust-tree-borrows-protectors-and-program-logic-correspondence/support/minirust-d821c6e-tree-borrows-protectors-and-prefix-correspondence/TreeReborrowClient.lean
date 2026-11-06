import AnnealResearch.TreeMemoryPrefixes
import AnnealResearch.TreeReborrowAgreement
import AnnealResearch.TreeReborrowDomain

/-!
Separate experimental command/reply client adding actual reborrow and pointer
replies to the unchanged four-command client. A shared arbitrary-S controller
sees only control and actual replies. It has no memory-inspection argument.

The old complete R/F configuration types and reifier are reused, while resume,
step, exact-n iterations and NoUB observers below use the new decision/reply
types. Each primitive call is one client transition. UB and unsupported retain
the actual residual memory and cannot resume; noChoice has no successor. This
count is not a Rust instruction, cost, stack or timing measure.

This checkpoint proves dispatch equality under only existing WellSized and
all-result factored dispatch width closure. Finite-prefix composition and
stable live matching are later layers. No arbitrary-controller safety, progress,
allocation-choice or source/helper/Rust adequacy claim is made.
-/

namespace AnnealResearch.TreeReborrowClient

universe u

inductive Command where
  | base (command : TreeMemoryClient.Command)
  | reborrow (pointer : TreeMemory.Pointer) (settings : TreeMemory.Settings)

inductive Reply where
  | base (reply : TreeMemoryClient.Reply)
  | pointer (value : TreeMemory.Pointer)

inductive Decision (S : Type u) where
  | halt (result : Nat)
  | internal (next : S)
  | call (command : Command) (next : Reply → S)

abbrev Controller (S : Type u) := S → Decision S
abbrev RConfig (S : Type u) := TreeMemoryClient.RConfig S
abbrev FConfig (S : Type u) := TreeMemoryClient.FConfig S

abbrev reifyConfig {S : Type u} (config : FConfig S) : RConfig S :=
  TreeMemoryClient.reifyConfig config

abbrev ConfigWellSized {S : Type u} (config : FConfig S) : Prop :=
  TreeMemoryClient.ConfigWellSized config

def rDispatch (memory : TreeMemory.State) : Command → TreeMemory.Result Reply
  | .base command => TreeMemoryClient.rMap Reply.base (TreeMemoryClient.rDispatch memory command)
  | .reborrow pointer settings => TreeMemoryClient.rMap Reply.pointer
      (TreeMemory.reborrow memory pointer settings)

def fDispatch (memory : TreeFactoredMemory.State) : Command → TreeFactoredMemory.Result Reply
  | .base command => TreeMemoryClient.fMap Reply.base (TreeMemoryClient.fDispatch memory command)
  | .reborrow pointer settings => TreeMemoryClient.fMap Reply.pointer
      (TreeFactoredMemory.reborrow memory pointer settings)

def rResume {S : Type u} (control : S) (next : Reply → S) :
    TreeMemory.Result Reply → Option (RConfig S)
  | .ok reply memory => some (.running (next reply) memory)
  | .ub fault memory => some (.ub control fault memory)
  | .unsupported reason memory => some (.unsupported control reason memory)
  | .noChoice _ => none

def fResume {S : Type u} (control : S) (next : Reply → S) :
    TreeFactoredMemory.Result Reply → Option (FConfig S)
  | .ok reply memory => some (.running (next reply) memory)
  | .ub fault memory => some (.ub control fault memory)
  | .unsupported reason memory => some (.unsupported control reason memory)
  | .noChoice _ => none

def rStep {S : Type u} (controller : Controller S) : RConfig S → Option (RConfig S)
  | .running control memory =>
      match controller control with
      | .halt result => some (.finished control result memory)
      | .internal next => some (.running next memory)
      | .call command next => rResume control next (rDispatch memory command)
  | .finished _ _ _ => none
  | .ub _ _ _ => none
  | .unsupported _ _ _ => none

def fStep {S : Type u} (controller : Controller S) : FConfig S → Option (FConfig S)
  | .running control memory =>
      match controller control with
      | .halt result => some (.finished control result memory)
      | .internal next => some (.running next memory)
      | .call command next => fResume control next (fDispatch memory command)
  | .finished _ _ _ => none
  | .ub _ _ _ => none
  | .unsupported _ _ _ => none

/-- Reuse the existing exact-transition iterator with the new actual step.
Terminals are observed at their reached horizon and do not pad later horizons. -/
def rIterate {S : Type u} (controller : Controller S) (count : Nat) (config : RConfig S) :
    Option (RConfig S) := TreeMemoryClient.iterate (rStep controller) count config

def fIterate {S : Type u} (controller : Controller S) (count : Nat) (config : FConfig S) :
    Option (FConfig S) := TreeMemoryClient.iterate (fStep controller) count config

def RNoUB {S : Type u} (controller : Controller S) (initial : RConfig S) : Prop :=
  ∀ count reached, rIterate controller count initial = some reached →
    ¬ TreeMemoryClient.RConfig.IsUB reached

def FNoUB {S : Type u} (controller : Controller S) (initial : FConfig S) : Prop :=
  ∀ count reached, fIterate controller count initial = some reached →
    ¬ TreeMemoryClient.FConfig.IsUB reached

/-- Input WellSized is the only dispatch admission. Settings, pointer and
parent paths stay arbitrary; all actual result categories are translated. -/
theorem dispatch_agrees (memory : TreeFactoredMemory.State) (command : Command)
    (sized : TreeFactoredMemory.WellSized memory) :
    rDispatch (TreeFactoredMemory.reify memory) command =
      TreeFactoredMemory.translate (fDispatch memory command) := by
  cases command with
  | base command =>
      simp only [rDispatch, fDispatch]
      rw [TreeMemoryClient.dispatch_agrees memory command sized]
      exact TreeMemoryClient.map_translate Reply.base _
  | reborrow pointer settings =>
      simp only [rDispatch, fDispatch]
      rw [TreeReborrowAgreement.reborrow_agrees memory pointer settings sized]
      exact TreeMemoryClient.map_translate Reply.pointer _

theorem dispatch_preserves (memory : TreeFactoredMemory.State) (command : Command)
    (sized : TreeFactoredMemory.WellSized memory) :
    TreeFactoredMemory.WellSized (fDispatch memory command).residual := by
  cases command with
  | base command =>
      simp only [fDispatch, TreeMemoryPrefixes.fMap_residual]
      exact TreeMemoryPrefixes.dispatch_preserves memory command sized
  | reborrow pointer settings =>
      simp only [fDispatch, TreeMemoryPrefixes.fMap_residual]
      exact TreeReborrowDomain.reborrow_preserves memory pointer settings sized

theorem reify_resume {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) :
    rResume control next (TreeFactoredMemory.translate answer) =
      (fResume control next answer).map reifyConfig := by
  cases answer <;> rfl

/-- Resumption retains the exact memory returned by the primitive, including
partial-error memories. A successful pointer reply changes only control. -/
theorem resume_memory {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) (successor : FConfig S)
    (stepped : fResume control next answer = some successor) :
    successor.memory = answer.residual := by
  cases answer with
  | ok reply memory =>
      have same : TreeMemoryClient.FConfig.running (next reply) memory = successor :=
        Option.some.inj stepped
      rw [← same] <;> rfl
  | ub fault memory =>
      have same : TreeMemoryClient.FConfig.ub control fault memory = successor :=
        Option.some.inj stepped
      rw [← same] <;> rfl
  | unsupported reason memory =>
      have same : TreeMemoryClient.FConfig.unsupported control reason memory = successor :=
        Option.some.inj stepped
      rw [← same] <;> rfl
  | noChoice memory =>
      simp only [fResume] at stepped
      cases stepped

theorem rResume_noChoice {S : Type u} (control : S) (next : Reply → S)
    (memory : TreeMemory.State) : rResume control next (.noChoice memory) = none := rfl

theorem fResume_noChoice {S : Type u} (control : S) (next : Reply → S)
    (memory : TreeFactoredMemory.State) : fResume control next (.noChoice memory) = none := rfl

theorem rStep_finished {S : Type u} (controller : Controller S) (control : S)
    (result : Nat) (memory : TreeMemory.State) :
    rStep controller (.finished control result memory) = none := rfl

theorem rStep_UB {S : Type u} (controller : Controller S) (control : S)
    (fault : TreeMemory.Fault) (memory : TreeMemory.State) :
    rStep controller (.ub control fault memory) = none := rfl

theorem rStep_unsupported {S : Type u} (controller : Controller S) (control : S)
    (reason : TreeMemory.Unsupported) (memory : TreeMemory.State) :
    rStep controller (.unsupported control reason memory) = none := rfl

theorem fStep_finished {S : Type u} (controller : Controller S) (control : S)
    (result : Nat) (memory : TreeFactoredMemory.State) :
    fStep controller (.finished control result memory) = none := rfl

theorem fStep_UB {S : Type u} (controller : Controller S) (control : S)
    (fault : TreeMemory.Fault) (memory : TreeFactoredMemory.State) :
    fStep controller (.ub control fault memory) = none := rfl

theorem fStep_unsupported {S : Type u} (controller : Controller S) (control : S)
    (reason : TreeMemory.Unsupported) (memory : TreeFactoredMemory.State) :
    fStep controller (.unsupported control reason memory) = none := rfl

theorem rIterate_zero {S : Type u} (controller : Controller S) (config : RConfig S) :
    rIterate controller 0 config = some config := rfl

theorem fIterate_zero {S : Type u} (controller : Controller S) (config : FConfig S) :
    fIterate controller 0 config = some config := rfl

#print axioms dispatch_agrees
#print axioms dispatch_preserves
#print axioms reify_resume
#print axioms resume_memory
#print axioms rResume_noChoice
#print axioms fResume_noChoice
#print axioms rStep_finished
#print axioms rStep_UB
#print axioms rStep_unsupported
#print axioms fStep_finished
#print axioms fStep_UB
#print axioms fStep_unsupported
#print axioms rIterate_zero
#print axioms fIterate_zero

end AnnealResearch.TreeReborrowClient
