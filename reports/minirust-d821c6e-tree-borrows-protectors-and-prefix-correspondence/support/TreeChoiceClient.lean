import AnnealResearch.TreeReborrowClient
import AnnealResearch.TreeAllocationDomain

/-!
Separate explicit-candidate client over actual tree-memory operations. The shared
arbitrary-S controller sees only control and actual replies. Allocation and
reborrow deliver their actual pointer reply; the dispatcher never fabricates it.
The factored dispatcher calls actual F operations, not R through reification.

Each halt, internal action or primitive call is one owned client transition.
UB/unsupported retain actual complete partial residuals and cannot resume.
Every noChoice contributes no successor. RStep/FStep expose every Nat candidate;
Prefix counts exactly n transitions, including horizon zero, without stuttering.

Only candidate-specific dispatch/next agreement and all-result width closure are
proved here. Relational prefix coverage, NoUB equivalence, separate stable live
matching and controls remain later checkpoints. No arbitrary-client safety,
progress, source-helper/Rust adequacy or internal-cost interpretation is claimed.
-/
namespace AnnealResearch.TreeChoiceClient

universe u

inductive Command where
  | base (command : TreeReborrowClient.Command)
  | allocate (kind : MiniRustReference.Kind) (size align : Nat)

abbrev Reply := TreeReborrowClient.Reply

inductive Decision (S : Type u) where
  | halt (result : Nat)
  | internal (next : S)
  | call (command : Command) (next : Reply → S)

abbrev Controller (S : Type u) := S → Decision S
abbrev RConfig (S : Type u) := TreeReborrowClient.RConfig S
abbrev FConfig (S : Type u) := TreeReborrowClient.FConfig S

abbrev reifyConfig {S : Type u} (config : FConfig S) : RConfig S :=
  TreeReborrowClient.reifyConfig config

abbrev ConfigWellSized {S : Type u} (config : FConfig S) : Prop :=
  TreeReborrowClient.ConfigWellSized config

abbrev rResume {S : Type u} (control : S) (next : Reply → S) :
    TreeMemory.Result Reply → Option (RConfig S) :=
  TreeReborrowClient.rResume control next

abbrev fResume {S : Type u} (control : S) (next : Reply → S) :
    TreeFactoredMemory.Result Reply → Option (FConfig S) :=
  TreeReborrowClient.fResume control next

def rDispatch (candidate : Nat) (memory : TreeMemory.State) :
    Command → TreeMemory.Result Reply
  | .base command => TreeReborrowClient.rDispatch memory command
  | .allocate kind size align => TreeMemoryClient.rMap TreeReborrowClient.Reply.pointer
      (TreeMemory.allocateAt memory kind size align candidate)

def fDispatch (candidate : Nat) (memory : TreeFactoredMemory.State) :
    Command → TreeFactoredMemory.Result Reply
  | .base command => TreeReborrowClient.fDispatch memory command
  | .allocate kind size align => TreeMemoryClient.fMap TreeReborrowClient.Reply.pointer
      (TreeFactoredMemory.allocateAt memory kind size align candidate)

def rNext {S : Type u} (controller : Controller S) (candidate : Nat) :
    RConfig S → Option (RConfig S)
  | .running control memory =>
      match controller control with
      | .halt result => some (.finished control result memory)
      | .internal next => some (.running next memory)
      | .call command next => rResume control next (rDispatch candidate memory command)
  | .finished _ _ _ | .ub _ _ _ | .unsupported _ _ _ => none

def fNext {S : Type u} (controller : Controller S) (candidate : Nat) :
    FConfig S → Option (FConfig S)
  | .running control memory =>
      match controller control with
      | .halt result => some (.finished control result memory)
      | .internal next => some (.running next memory)
      | .call command next => fResume control next (fDispatch candidate memory command)
  | .finished _ _ _ | .ub _ _ _ | .unsupported _ _ _ => none

/-- Every candidate enters the relation; only an actual some successor is an
edge. Rejecting one candidate says nothing about all the other candidates. -/
def RStep {S : Type u} (controller : Controller S) (initial reached : RConfig S) : Prop :=
  ∃ candidate : Nat, rNext controller candidate initial = some reached

def FStep {S : Type u} (controller : Controller S) (initial reached : FConfig S) : Prop :=
  ∃ candidate : Nat, fNext controller candidate initial = some reached

/-- Exact relational transition count; terminal states are not repeated. -/
def Prefix {C : Type u} (step : C → C → Prop) : Nat → C → C → Prop
  | 0, initial, reached => reached = initial
  | count + 1, initial, reached =>
      ∃ middle, step initial middle ∧ Prefix step count middle reached

abbrev RPrefix {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : RConfig S) : Prop := Prefix (RStep controller) count initial reached

abbrev FPrefix {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) : Prop := Prefix (FStep controller) count initial reached

def RNoUB {S : Type u} (controller : Controller S) (initial : RConfig S) : Prop :=
  ∀ count reached, RPrefix controller count initial reached →
    ¬ TreeMemoryClient.RConfig.IsUB reached

def FNoUB {S : Type u} (controller : Controller S) (initial : FConfig S) : Prop :=
  ∀ count reached, FPrefix controller count initial reached →
    ¬ TreeMemoryClient.FConfig.IsUB reached

/-- Width is the only combined-dispatch premise. Allocation's branch equation
itself is unconditional; old base operations retain their existing width domain. -/
theorem dispatch_agrees (candidate : Nat) (memory : TreeFactoredMemory.State)
    (command : Command) (sized : TreeFactoredMemory.WellSized memory) :
    rDispatch candidate (TreeFactoredMemory.reify memory) command =
      TreeFactoredMemory.translate (fDispatch candidate memory command) := by
  cases command with
  | base command => exact TreeReborrowClient.dispatch_agrees memory command sized
  | allocate kind size align =>
    simp only [rDispatch, fDispatch]
    rw [TreeAllocation.allocateAt_agrees memory kind size align candidate]
    exact TreeMemoryClient.map_translate TreeReborrowClient.Reply.pointer _

theorem dispatch_preserves (candidate : Nat) (memory : TreeFactoredMemory.State)
    (command : Command) (sized : TreeFactoredMemory.WellSized memory) :
    TreeFactoredMemory.WellSized (fDispatch candidate memory command).residual := by
  cases command with
  | base command => exact TreeReborrowClient.dispatch_preserves memory command sized
  | allocate kind size align =>
    simp only [fDispatch, TreeMemoryPrefixes.fMap_residual]
    exact TreeAllocationDomain.factored_preserves_width memory kind size align candidate sized

/-- Full answer translation preserves the same actual reply and every residual
constructor. Reuse of resume is explicit; it does not add any synthetic reply. -/
theorem reify_resume {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) :
    rResume control next (TreeFactoredMemory.translate answer) =
      (fResume control next answer).map reifyConfig :=
  TreeReborrowClient.reify_resume control next answer

theorem resume_memory {S : Type u} (control : S) (next : Reply → S)
    (answer : TreeFactoredMemory.Result Reply) (successor : FConfig S)
    (stepped : fResume control next answer = some successor) :
    successor.memory = answer.residual :=
  TreeReborrowClient.resume_memory control next answer successor stepped

theorem rResume_ok {S : Type u} (control : S) (next : Reply → S)
    (reply : Reply) (memory : TreeMemory.State) :
    rResume control next (.ok reply memory) = some (.running (next reply) memory) := rfl

theorem fResume_ok {S : Type u} (control : S) (next : Reply → S)
    (reply : Reply) (memory : TreeFactoredMemory.State) :
    fResume control next (.ok reply memory) = some (.running (next reply) memory) := rfl

theorem rResume_noChoice {S : Type u} (control : S) (next : Reply → S)
    (memory : TreeMemory.State) : rResume control next (.noChoice memory) = none := rfl

theorem fResume_noChoice {S : Type u} (control : S) (next : Reply → S)
    (memory : TreeFactoredMemory.State) : fResume control next (.noChoice memory) = none := rfl

/-- An observed some successor includes actual UB/unsupported as well as normal
continuation. It is not a successful-command or NoUB admission. -/
theorem next_preserves {S : Type u} (controller : Controller S) (candidate : Nat)
    (config successor : FConfig S) (sized : ConfigWellSized config)
    (stepped : fNext controller candidate config = some successor) :
    ConfigWellSized successor := by
  cases config with
  | running control memory =>
    cases decision : controller control with
    | halt result =>
      simp only [fNext, decision] at stepped
      rw [← Option.some.inj stepped]
      exact sized
    | internal next =>
      simp only [fNext, decision] at stepped
      rw [← Option.some.inj stepped]
      exact sized
    | call command next =>
      have resumed : fResume control next (fDispatch candidate memory command) = some successor := by
        simpa only [fNext, decision] using stepped
      change TreeFactoredMemory.WellSized successor.memory
      rw [resume_memory control next (fDispatch candidate memory command) successor resumed]
      exact dispatch_preserves candidate memory command sized
  | finished control result memory =>
    simp only [fNext] at stepped
    cases stepped
  | ub control fault memory =>
    simp only [fNext] at stepped
    cases stepped
  | unsupported control reason memory =>
    simp only [fNext] at stepped
    cases stepped

theorem next_agrees {S : Type u} (controller : Controller S) (candidate : Nat)
    (config : FConfig S) (sized : ConfigWellSized config) :
    rNext controller candidate (reifyConfig config) =
      (fNext controller candidate config).map reifyConfig := by
  cases config with
  | running control memory =>
    change rNext controller candidate (.running control (TreeFactoredMemory.reify memory)) =
      (fNext controller candidate (.running control memory)).map reifyConfig
    cases decision : controller control with
    | halt result =>
      simp only [rNext, fNext, decision, Option.map_some] <;> rfl
    | internal next =>
      simp only [rNext, fNext, decision, Option.map_some] <;> rfl
    | call command next =>
      simp only [rNext, fNext, decision]
      rw [dispatch_agrees candidate memory command sized]
      exact reify_resume control next (fDispatch candidate memory command)
  | finished control result memory => rfl
  | ub control fault memory => rfl
  | unsupported control reason memory => rfl

theorem rNext_call_noChoice {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (memory residual : TreeMemory.State) (command : Command) (next : Reply → S)
    (decision : controller control = .call command next)
    (chosen : rDispatch candidate memory command = .noChoice residual) :
    rNext controller candidate (.running control memory) = none := by
  calc
    rNext controller candidate (.running control memory) =
        rResume control next (rDispatch candidate memory command) := by rw [rNext, decision]
    _ = rResume control next (.noChoice residual) := congrArg (rResume control next) chosen
    _ = none := rfl

theorem fNext_call_noChoice {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (memory residual : TreeFactoredMemory.State) (command : Command) (next : Reply → S)
    (decision : controller control = .call command next)
    (chosen : fDispatch candidate memory command = .noChoice residual) :
    fNext controller candidate (.running control memory) = none := by
  calc
    fNext controller candidate (.running control memory) =
        fResume control next (fDispatch candidate memory command) := by rw [fNext, decision]
    _ = fResume control next (.noChoice residual) := congrArg (fResume control next) chosen
    _ = none := rfl

theorem rNext_finished {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (result : Nat) (memory : TreeMemory.State) :
    rNext controller candidate (.finished control result memory) = none := rfl

theorem rNext_UB {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (fault : TreeMemory.Fault) (memory : TreeMemory.State) :
    rNext controller candidate (.ub control fault memory) = none := rfl

theorem rNext_unsupported {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (reason : TreeMemory.Unsupported) (memory : TreeMemory.State) :
    rNext controller candidate (.unsupported control reason memory) = none := rfl

theorem fNext_finished {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (result : Nat) (memory : TreeFactoredMemory.State) :
    fNext controller candidate (.finished control result memory) = none := rfl

theorem fNext_UB {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (fault : TreeMemory.Fault) (memory : TreeFactoredMemory.State) :
    fNext controller candidate (.ub control fault memory) = none := rfl

theorem fNext_unsupported {S : Type u} (controller : Controller S) (candidate : Nat)
    (control : S) (reason : TreeMemory.Unsupported) (memory : TreeFactoredMemory.State) :
    fNext controller candidate (.unsupported control reason memory) = none := rfl

theorem prefix_zero {C : Type u} (step : C → C → Prop) (initial reached : C) :
    Prefix step 0 initial reached ↔ reached = initial := Iff.rfl

theorem prefix_succ {C : Type u} (step : C → C → Prop) (count : Nat) (initial reached : C) :
    Prefix step (count + 1) initial reached ↔
      ∃ middle, step initial middle ∧ Prefix step count middle reached := Iff.rfl

theorem rPrefix_zero {S : Type u} (controller : Controller S) (initial reached : RConfig S) :
    RPrefix controller 0 initial reached ↔ reached = initial := Iff.rfl

theorem fPrefix_zero {S : Type u} (controller : Controller S) (initial reached : FConfig S) :
    FPrefix controller 0 initial reached ↔ reached = initial := Iff.rfl

#print axioms dispatch_agrees
#print axioms dispatch_preserves
#print axioms reify_resume
#print axioms resume_memory
#print axioms rResume_ok
#print axioms fResume_ok
#print axioms rResume_noChoice
#print axioms fResume_noChoice
#print axioms next_preserves
#print axioms next_agrees
#print axioms rNext_call_noChoice
#print axioms fNext_call_noChoice
#print axioms rNext_finished
#print axioms rNext_UB
#print axioms rNext_unsupported
#print axioms fNext_finished
#print axioms fNext_UB
#print axioms fNext_unsupported
#print axioms prefix_zero
#print axioms prefix_succ
#print axioms rPrefix_zero
#print axioms fPrefix_zero

end AnnealResearch.TreeChoiceClient
