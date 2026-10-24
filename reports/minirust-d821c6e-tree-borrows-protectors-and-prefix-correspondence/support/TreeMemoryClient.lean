import AnnealResearch.TreeMemoryOperations
import AnnealResearch.TreeMemoryReleaseAgreement

/-!
Owned reply-driven controller for the four checked memory primitives. A shared
controller inspects only its control state and replies, never either memory
representation. The factored dispatcher executes the actual factored runners;
neither it nor its step function is defined by reference execution/reification.

Configurations retain control, return values, diagnostics, and full memory.
Only running configurations step. noChoice has no successor; it is not a new
terminal state. iterate counts exactly n transitions, including horizon zero.
The NoUB definitions permit unsupported/absent successors and imply neither
progress nor termination. No controller safety or all-prefix correspondence is
proved at this definitions/dispatch checkpoint; closure is a separate import.
-/

namespace AnnealResearch.TreeMemoryClient

universe u

inductive Command where
  | load (pointer : TreeMemory.Pointer) (size align : Nat)
  | store (pointer : TreeMemory.Pointer) (bytes : List MiniRustReference.Byte) (align : Nat)
  | free (pointer : TreeMemory.Pointer) (kind : MiniRustReference.Kind) (size align : Nat)
  | release (provenance : TreeMemory.Provenance)

inductive Reply where
  | bytes (values : List MiniRustReference.Byte)
  | unit

inductive Decision (S : Type u) where
  | halt (result : Nat)
  | internal (next : S)
  | call (command : Command) (next : Reply → S)

abbrev Controller (S : Type u) := S → Decision S

inductive RConfig (S : Type u) where
  | running (control : S) (memory : TreeMemory.State)
  | finished (control : S) (result : Nat) (memory : TreeMemory.State)
  | ub (control : S) (fault : TreeMemory.Fault) (memory : TreeMemory.State)
  | unsupported (control : S) (reason : TreeMemory.Unsupported) (memory : TreeMemory.State)

inductive FConfig (S : Type u) where
  | running (control : S) (memory : TreeFactoredMemory.State)
  | finished (control : S) (result : Nat) (memory : TreeFactoredMemory.State)
  | ub (control : S) (fault : TreeMemory.Fault) (memory : TreeFactoredMemory.State)
  | unsupported (control : S) (reason : TreeMemory.Unsupported) (memory : TreeFactoredMemory.State)

def RConfig.memory {S : Type u} : RConfig S → TreeMemory.State
  | .running _ memory => memory
  | .finished _ _ memory => memory
  | .ub _ _ memory => memory
  | .unsupported _ _ memory => memory

def FConfig.memory {S : Type u} : FConfig S → TreeFactoredMemory.State
  | .running _ memory => memory
  | .finished _ _ memory => memory
  | .ub _ _ memory => memory
  | .unsupported _ _ memory => memory

def RConfig.IsUB {S : Type u} : RConfig S → Prop
  | .ub _ _ _ => True
  | _ => False

def FConfig.IsUB {S : Type u} : FConfig S → Prop
  | .ub _ _ _ => True
  | _ => False

def reifyConfig {S : Type u} : FConfig S → RConfig S
  | .running control memory => .running control (TreeFactoredMemory.reify memory)
  | .finished control result memory => .finished control result (TreeFactoredMemory.reify memory)
  | .ub control fault memory => .ub control fault (TreeFactoredMemory.reify memory)
  | .unsupported control reason memory => .unsupported control reason (TreeFactoredMemory.reify memory)

def ConfigWellSized {S : Type u} (config : FConfig S) : Prop :=
  TreeFactoredMemory.WellSized config.memory

def rMap {A B : Type} (f : A → B) : TreeMemory.Result A → TreeMemory.Result B
  | .ok value memory => .ok (f value) memory
  | .ub fault memory => .ub fault memory
  | .unsupported reason memory => .unsupported reason memory
  | .noChoice memory => .noChoice memory

def fMap {A B : Type} (f : A → B) : TreeFactoredMemory.Result A → TreeFactoredMemory.Result B
  | .ok value memory => .ok (f value) memory
  | .ub fault memory => .ub fault memory
  | .unsupported reason memory => .unsupported reason memory
  | .noChoice memory => .noChoice memory

def rDispatch (memory : TreeMemory.State) : Command → TreeMemory.Result Reply
  | .load pointer size align => rMap Reply.bytes (TreeMemory.load memory pointer size align)
  | .store pointer bytes align => rMap (fun _ => Reply.unit) (TreeMemory.store memory pointer bytes align)
  | .free pointer kind size align =>
      rMap (fun _ => Reply.unit) (TreeMemory.deallocate memory pointer kind size align)
  | .release provenance => rMap (fun _ => Reply.unit) (TreeMemory.release memory provenance)

def fDispatch (memory : TreeFactoredMemory.State) : Command → TreeFactoredMemory.Result Reply
  | .load pointer size align => fMap Reply.bytes (TreeFactoredMemory.load memory pointer size align)
  | .store pointer bytes align => fMap (fun _ => Reply.unit) (TreeFactoredMemory.store memory pointer bytes align)
  | .free pointer kind size align =>
      fMap (fun _ => Reply.unit) (TreeFactoredMemory.deallocate memory pointer kind size align)
  | .release provenance => fMap (fun _ => Reply.unit) (TreeFactoredMemory.release memory provenance)

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

/-- Exactly n transitions; a terminal or absent successor makes every larger
horizon absent, rather than repeatedly returning the terminal configuration. -/
def iterate {C : Type u} (step : C → Option C) : Nat → C → Option C
  | 0, current => some current
  | count + 1, current => (step current).bind (fun next => iterate step count next)

def rIterate {S : Type u} (controller : Controller S) (count : Nat) (config : RConfig S) :
    Option (RConfig S) := iterate (rStep controller) count config

def fIterate {S : Type u} (controller : Controller S) (count : Nat) (config : FConfig S) :
    Option (FConfig S) := iterate (fStep controller) count config

def RNoUB {S : Type u} (controller : Controller S) (initial : RConfig S) : Prop :=
  ∀ count reached, rIterate controller count initial = some reached → ¬ reached.IsUB

def FNoUB {S : Type u} (controller : Controller S) (initial : FConfig S) : Prop :=
  ∀ count reached, fIterate controller count initial = some reached → ¬ reached.IsUB

theorem map_translate {A B : Type} (f : A → B) (answer : TreeFactoredMemory.Result A) :
    rMap f (TreeFactoredMemory.translate answer) = TreeFactoredMemory.translate (fMap f answer) := by
  cases answer <;> rfl

/-- The sole domain premise is the already fixed structural WellSized. -/
theorem dispatch_agrees (memory : TreeFactoredMemory.State) (command : Command)
    (sized : TreeFactoredMemory.WellSized memory) :
    rDispatch (TreeFactoredMemory.reify memory) command =
      TreeFactoredMemory.translate (fDispatch memory command) := by
  cases command with
  | load pointer size align =>
      simp only [rDispatch, fDispatch]
      rw [TreeMemoryOperations.load_agrees memory pointer size align sized]
      exact map_translate Reply.bytes _
  | store pointer bytes align =>
      simp only [rDispatch, fDispatch]
      rw [TreeMemoryOperations.store_agrees memory pointer bytes align sized]
      exact map_translate (fun _ => Reply.unit) _
  | free pointer kind size align =>
      simp only [rDispatch, fDispatch]
      rw [TreeMemoryOperations.deallocate_agrees memory pointer kind size align sized]
      exact map_translate (fun _ => Reply.unit) _
  | release provenance =>
      simp only [rDispatch, fDispatch]
      rw [TreeMemoryReleaseAgreement.release_agrees memory provenance sized]
      exact map_translate (fun _ => Reply.unit) _

theorem reify_resume {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) :
    rResume control next (TreeFactoredMemory.translate answer) =
      (fResume control next answer).map reifyConfig := by
  cases answer <;> rfl

theorem reify_memory {S : Type u} (config : FConfig S) :
    (reifyConfig config).memory = TreeFactoredMemory.reify config.memory := by
  cases config <;> rfl

theorem reify_isUB {S : Type u} (config : FConfig S) :
    (reifyConfig config).IsUB ↔ config.IsUB := by
  cases config <;> rfl

theorem iterate_zero {C : Type u} (step : C → Option C) (current : C) :
    iterate step 0 current = some current := rfl

theorem iterate_no_successor {C : Type u} (step : C → Option C) (current : C)
    (count : Nat) (stopped : step current = none) :
    iterate step (count + 1) current = none := by
  rw [iterate, stopped] <;> rfl

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

#print axioms map_translate
#print axioms dispatch_agrees
#print axioms reify_resume
#print axioms reify_memory
#print axioms reify_isUB
#print axioms iterate_zero
#print axioms iterate_no_successor
#print axioms rResume_noChoice
#print axioms fResume_noChoice
#print axioms rStep_finished
#print axioms rStep_UB
#print axioms rStep_unsupported
#print axioms fStep_finished
#print axioms fStep_UB
#print axioms fStep_unsupported

end AnnealResearch.TreeMemoryClient
