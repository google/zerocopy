import AnnealResearch.TreeAllocationControls
import AnnealResearch.TreeChoiceClient

/-!
Finite relational controls for the actual candidate-specific client. Internal
loops and safe successors have all-prefix NoUB proofs over every candidate edge.
The initial allocation control also has an actual feasible bad alternative.
All expected memories are explicit; no fallback extracts a successful result.
F allocation/control observations use actual F execution and shared proved
correspondence. Reification is never canceled to infer literal F equality.
-/
namespace AnnealResearch.TreeChoiceControls

open TreePermissions
open TreeChoiceClient

def blockAt (address : Nat) : MiniRustReference.Allocation :=
  { base := address, size := 1, align := 1, kind := .heap, live := true
    data := fun _ => .uninit }

def pointerAt (address : Nat) : TreeMemory.Pointer := ⟨address, some (0, [])⟩

/-- Explicit expected memory, not an extracted allocator poststate. -/
def referenceBorn (address : Nat) : TreeMemory.State :=
  { raw := { next := 1, allocations := fun id => if id = 0 then some (blockAt address) else none }
    trees := fun id => if id = 0 then some (TreeAllocation.referenceRoot 1) else none
    currentFrame := [] }

def factoredBorn (address : Nat) : TreeFactoredMemory.State :=
  { raw := { next := 1, allocations := fun id => if id = 0 then some (blockAt address) else none }
    trees := fun id => if id = 0 then some (TreeAllocation.factoredRoot 1) else none
    currentFrame := [] }

theorem born_reify (address : Nat) :
    TreeFactoredMemory.reify (factoredBorn address) = referenceBorn address := by
  unfold TreeFactoredMemory.reify factoredBorn referenceBorn
  congr 1
  funext id
  by_cases zero : id = 0 <;> simp [zero, TreeAllocation.factoredRoot_reify]

theorem candidate_zero_rejected :
    TreeMemory.allocateAt TreeAllocationControls.referenceEmpty .heap 1 1 0 =
      .noChoice TreeAllocationControls.referenceEmpty := rfl

theorem candidate16_actual :
    TreeMemory.allocateAt TreeAllocationControls.referenceEmpty .heap 1 1 16 =
      .ok (pointerAt 16) (referenceBorn 16) :=
  TreeAllocationControls.reference_birth_one

theorem candidate32_actual :
    TreeMemory.allocateAt TreeAllocationControls.referenceEmpty .heap 1 1 32 =
      .ok (pointerAt 32) (referenceBorn 32) := rfl

theorem candidate32_bounds_load :
    TreeMemory.load (referenceBorn 32) (pointerAt 32) 2 1 =
      .ub (.basic .bounds) (referenceBorn 32) := rfl

/-- Shared proof transport observes actual F allocation, without assuming
injective reification or extracting a successful state with a fallback. -/
theorem factored_candidate16_actual :
    TreeFactoredMemory.translate
      (TreeFactoredMemory.allocateAt TreeAllocationControls.factoredEmpty .heap 1 1 16) =
        .ok (pointerAt 16) (referenceBorn 16) := by
  rw [← TreeAllocation.allocateAt_agrees, TreeAllocationControls.empty_reify]
  exact candidate16_actual

theorem factored_candidate32_actual :
    TreeFactoredMemory.translate
      (TreeFactoredMemory.allocateAt TreeAllocationControls.factoredEmpty .heap 1 1 32) =
        .ok (pointerAt 32) (referenceBorn 32) := by
  rw [← TreeAllocation.allocateAt_agrees, TreeAllocationControls.empty_reify]
  exact candidate32_actual

/-! Generic exact-prefix induction retains every candidate in the step relation. -/

theorem prefix_invariant {C : Type} (step : C → C → Prop) (property : C → Prop)
    (preserved : ∀ before after, property before → step before after → property after)
    (count : Nat) (initial reached : C) (admitted : property initial)
    (path : Prefix step count initial reached) : property reached := by
  induction count generalizing initial with
  | zero =>
    change reached = initial at path
    rw [path]
    exact admitted
  | succ count ih =>
    obtain ⟨middle, edge, rest⟩ := path
    exact ih middle (preserved initial middle admitted edge) rest

theorem prefix_stopped {C : Type} (step : C → C → Prop) (initial : C)
    (stopped : ∀ reached, ¬ step initial reached) (count : Nat) (reached : C) :
    ¬ Prefix step (count + 1) initial reached := by
  intro path
  obtain ⟨middle, edge, _⟩ := path
  exact stopped middle edge

def loop : Controller Unit := fun _ => .internal ()

theorem reference_loop_prefix (count : Nat) (memory : TreeMemory.State) :
    RPrefix loop count (.running () memory) (.running () memory) := by
  induction count with
  | zero => rfl
  | succ count ih => exact ⟨_, ⟨0, rfl⟩, ih⟩

theorem factored_loop_prefix (count : Nat) (memory : TreeFactoredMemory.State) :
    FPrefix loop count (.running () memory) (.running () memory) := by
  induction count with
  | zero => rfl
  | succ count ih => exact ⟨_, ⟨0, rfl⟩, ih⟩

theorem reference_loop_NoUB (memory : TreeMemory.State) :
    RNoUB loop (.running () memory) := by
  intro count reached path
  have same : reached = TreeMemoryClient.RConfig.running () memory := by
    apply prefix_invariant (RStep loop) (fun cfg => cfg = .running () memory)
      (count := count) (initial := .running () memory) (reached := reached) ?_ rfl path
    intro before after admitted edge
    rw [admitted] at edge
    obtain ⟨candidate, actual⟩ := edge
    change some (.running () memory) = some after at actual
    exact (Option.some.inj actual).symm
  rw [same]
  exact fun impossible => impossible

theorem factored_loop_NoUB (memory : TreeFactoredMemory.State) :
    FNoUB loop (.running () memory) := by
  intro count reached path
  have same : reached = TreeMemoryClient.FConfig.running () memory := by
    apply prefix_invariant (FStep loop) (fun cfg => cfg = .running () memory)
      (count := count) (initial := .running () memory) (reached := reached) ?_ rfl path
    intro before after admitted edge
    rw [admitted] at edge
    obtain ⟨candidate, actual⟩ := edge
    change some (.running () memory) = some after at actual
    exact (Option.some.inj actual).symm
  rw [same]
  exact fun impossible => impossible

inductive Control where
  | allocate
  | safe
  | load (pointer : TreeMemory.Pointer)
  | unexpected

/-- The actual reply is inspected, and the bad continuation retains that same
pointer. Other replies are handled explicitly without default extraction. -/
def chooseReply : Reply → Control
  | .pointer pointer => if pointer.addr = 32 then .load pointer else .safe
  | .base _ => .unexpected

def choices : Controller Control
  | .allocate => .call (.allocate .heap 1 1) chooseReply
  | .safe => .halt 7
  | .load pointer => .call (.base (.base (.load pointer 2 1))) (fun _ => .unexpected)
  | .unexpected => .halt 99

def rinitial : RConfig Control := .running .allocate TreeAllocationControls.referenceEmpty
def finitial : FConfig Control := .running .allocate TreeAllocationControls.factoredEmpty
def rsafe : RConfig Control := .running .safe (referenceBorn 16)
def rfinished : RConfig Control := .finished .safe 7 (referenceBorn 16)
def rloading : RConfig Control := .running (.load (pointerAt 32)) (referenceBorn 32)
def rfailed : RConfig Control :=
  .ub (.load (pointerAt 32)) (.basic .bounds) (referenceBorn 32)

theorem initial_reify : reifyConfig finitial = rinitial := by
  change TreeMemoryClient.RConfig.running .allocate
    (TreeFactoredMemory.reify TreeAllocationControls.factoredEmpty) = rinitial
  rw [TreeAllocationControls.empty_reify]
  rfl

theorem initial_sized : ConfigWellSized finitial := TreeAllocationControls.empty_sized

theorem reference_candidates :
    rNext choices 0 rinitial = none ∧
      rNext choices 16 rinitial = some rsafe ∧
      rNext choices 32 rinitial = some rloading := by
  constructor
  · simp only [rNext, rinitial, choices, rDispatch, candidate_zero_rejected,
      TreeMemoryClient.rMap, rResume, TreeReborrowClient.rResume]
  constructor
  · simp only [rNext, rinitial, choices, rDispatch, candidate16_actual,
      TreeMemoryClient.rMap, rResume, TreeReborrowClient.rResume, chooseReply]
    rfl
  · simp only [rNext, rinitial, choices, rDispatch, candidate32_actual,
      TreeMemoryClient.rMap, rResume, TreeReborrowClient.rResume, chooseReply]
    rfl

theorem reference_bad_load (candidate : Nat) :
    rNext choices candidate rloading = some rfailed := by
  simp only [rNext, rloading, choices, rDispatch, TreeReborrowClient.rDispatch,
    TreeMemoryClient.rDispatch, candidate32_bounds_load, TreeMemoryClient.rMap,
    rResume, TreeReborrowClient.rResume, rfailed]

/-- One rejected candidate coexists with a real edge at 16. -/
theorem reference_rejected_but_enabled :
    rNext choices 0 rinitial = none ∧ RStep choices rinitial rsafe :=
  ⟨reference_candidates.1, 16, reference_candidates.2.1⟩

theorem reference_safe_NoUB (memory : TreeMemory.State) :
    RNoUB choices (.running .safe memory) := by
  intro count reached path
  have admitted : reached = .running .safe memory ∨ reached = .finished .safe 7 memory := by
    apply prefix_invariant (RStep choices)
      (fun cfg => cfg = .running .safe memory ∨ cfg = .finished .safe 7 memory)
      (count := count) (initial := .running .safe memory) (reached := reached) ?_
      (Or.inl rfl) path
    intro before after admitted edge
    obtain ⟨candidate, actual⟩ := edge
    rcases admitted with same | same
    · rw [same] at actual
      change some (.finished .safe 7 memory) = some after at actual
      exact Or.inr (Option.some.inj actual).symm
    · rw [same] at actual
      change none = some after at actual
      cases actual
  rcases admitted with same | same
  · rw [same]; exact fun impossible => impossible
  · rw [same]; exact fun impossible => impossible

theorem factored_safe_NoUB (memory : TreeFactoredMemory.State) :
    FNoUB choices (.running .safe memory) := by
  intro count reached path
  have admitted : reached = .running .safe memory ∨ reached = .finished .safe 7 memory := by
    apply prefix_invariant (FStep choices)
      (fun cfg => cfg = .running .safe memory ∨ cfg = .finished .safe 7 memory)
      (count := count) (initial := .running .safe memory) (reached := reached) ?_
      (Or.inl rfl) path
    intro before after admitted edge
    obtain ⟨candidate, actual⟩ := edge
    rcases admitted with same | same
    · rw [same] at actual
      change some (.finished .safe 7 memory) = some after at actual
      exact Or.inr (Option.some.inj actual).symm
    · rw [same] at actual
      change none = some after at actual
      cases actual
  rcases admitted with same | same
  · rw [same]; exact fun impossible => impossible
  · rw [same]; exact fun impossible => impossible

theorem reference_alternative_prefixes :
    RPrefix choices 2 rinitial rfinished ∧ RPrefix choices 2 rinitial rfailed := by
  constructor
  · exact ⟨rsafe, ⟨16, reference_candidates.2.1⟩, rfinished, ⟨0, rfl⟩, rfl⟩
  · exact ⟨rloading, ⟨32, reference_candidates.2.2⟩,
      rfailed, ⟨0, reference_bad_load 0⟩, rfl⟩

theorem reference_initial_not_NoUB : ¬ RNoUB choices rinitial := by
  intro safe
  exact safe 2 rfailed reference_alternative_prefixes.2 (by trivial)

/-! Actual F witnesses are selected by executing F at the same candidate.
The bridge proves the represented result, without canceling reification. -/

theorem lift_actual_next {S : Type} (controller : Controller S) (candidate : Nat)
    (config : FConfig S) (successor : RConfig S) (sized : ConfigWellSized config)
    (actual : rNext controller candidate (reifyConfig config) = some successor) :
    ∃ changed, fNext controller candidate config = some changed ∧
      reifyConfig changed = successor := by
  have agreement := next_agrees controller candidate config sized
  rw [actual] at agreement
  generalize chosen : fNext controller candidate config = answer at agreement
  cases answer with
  | none => cases agreement
  | some changed =>
    refine ⟨changed, rfl, ?_⟩
    have same : some successor = some (reifyConfig changed) := by
      exact agreement
    exact (Option.some.inj same).symm

theorem factored_rejected_but_enabled :
    fNext choices 0 finitial = none ∧
      ∃ safe, fNext choices 16 finitial = some safe ∧ reifyConfig safe = rsafe := by
  constructor
  · rfl
  · apply lift_actual_next choices 16 finitial rsafe initial_sized
    rw [initial_reify]
    exact reference_candidates.2.1

theorem factored_safe_witness :
    ∃ safe finished,
      FPrefix choices 1 finitial safe ∧ reifyConfig safe = rsafe ∧
      FNoUB choices safe ∧ FPrefix choices 2 finitial finished ∧
      reifyConfig finished = rfinished := by
  obtain ⟨safe, first, represented⟩ := factored_rejected_but_enabled.2
  have sized := next_preserves choices 16 finitial safe initial_sized first
  obtain ⟨finished, last, representedLast⟩ :=
    lift_actual_next choices 0 safe rfinished sized (by rw [represented]; rfl)
  have safeAll : FNoUB choices safe := by
    cases safe with
    | running control memory =>
      have controlSame : control = Control.safe := by
        exact congrArg (fun config : RConfig Control =>
          match config with
          | .running value _ => value
          | .finished value _ _ => value
          | .ub value _ _ => value
          | .unsupported value _ _ => value) represented
      subst control
      exact factored_safe_NoUB memory
    | finished control result memory => cases represented
    | ub control fault memory => cases represented
    | unsupported control reason memory => cases represented
  refine ⟨safe, finished, ?_, represented, safeAll, ?_, representedLast⟩
  · exact ⟨safe, ⟨16, first⟩, rfl⟩
  · exact ⟨safe, ⟨16, first⟩, finished, ⟨0, last⟩, rfl⟩

theorem factored_bad_witness :
    ∃ loading failed,
      fNext choices 32 finitial = some loading ∧ reifyConfig loading = rloading ∧
      fNext choices 0 loading = some failed ∧ reifyConfig failed = rfailed ∧
      FPrefix choices 2 finitial failed ∧ TreeMemoryClient.FConfig.IsUB failed := by
  obtain ⟨loading, first, represented⟩ :=
    lift_actual_next choices 32 finitial rloading initial_sized
      (by rw [initial_reify]; exact reference_candidates.2.2)
  have sized := next_preserves choices 32 finitial loading initial_sized first
  obtain ⟨failed, last, representedLast⟩ :=
    lift_actual_next choices 0 loading rfailed sized
      (by rw [represented]; exact reference_bad_load 0)
  refine ⟨loading, failed, first, represented, last, representedLast, ?_, ?_⟩
  · exact ⟨loading, ⟨32, first⟩, failed, ⟨0, last⟩, rfl⟩
  · apply (TreeMemoryClient.reify_isUB failed).mp
    change TreeMemoryClient.RConfig.IsUB (reifyConfig failed)
    rw [representedLast]
    trivial

theorem factored_initial_not_NoUB : ¬ FNoUB choices finitial := by
  obtain ⟨_, failed, _, _, _, _, path, bad⟩ := factored_bad_witness
  intro safe
  exact safe 2 failed path bad

/-! Actual unsupported allocation: zero alignment is an owned representation
boundary, not an allocation-choice failure. The continuation is never taken. -/

def unsupportedCall : Controller Unit := fun _ =>
  .call (.allocate .heap 1 0) (fun _ => ())

def runsupportedInitial : RConfig Unit :=
  .running () TreeAllocationControls.referenceEmpty
def funsupportedInitial : FConfig Unit :=
  .running () TreeAllocationControls.factoredEmpty
def runsupported : RConfig Unit :=
  .unsupported () .basicRepresentation TreeAllocationControls.referenceEmpty
def funsupported : FConfig Unit :=
  .unsupported () .basicRepresentation TreeAllocationControls.factoredEmpty

theorem actual_unsupported (candidate : Nat) :
    rNext unsupportedCall candidate runsupportedInitial = some runsupported ∧
      fNext unsupportedCall candidate funsupportedInitial = some funsupported := by
  constructor <;> rfl

theorem unsupported_reached :
    RPrefix unsupportedCall 1 runsupportedInitial runsupported ∧
      FPrefix unsupportedCall 1 funsupportedInitial funsupported := by
  exact ⟨⟨runsupported, ⟨0, (actual_unsupported 0).1⟩, rfl⟩,
    ⟨funsupported, ⟨0, (actual_unsupported 0).2⟩, rfl⟩⟩

theorem reference_bad_no_padding (count : Nat) (reached : RConfig Control) :
    ¬ RPrefix choices (count + 1) rfailed reached := by
  apply prefix_stopped
  intro next edge
  obtain ⟨candidate, actual⟩ := edge
  change none = some next at actual
  cases actual

theorem actual_factored_bad_no_padding (count : Nat) :
    ∃ failed, FPrefix choices 2 finitial failed ∧
      TreeMemoryClient.FConfig.IsUB failed ∧
      ∀ reached, ¬ FPrefix choices (count + 1) failed reached := by
  obtain ⟨_, failed, _, _, _, _, path, bad⟩ := factored_bad_witness
  refine ⟨failed, path, bad, ?_⟩
  intro reached
  apply prefix_stopped
  intro next edge
  obtain ⟨candidate, actual⟩ := edge
  cases failed with
  | running control memory => cases bad
  | finished control result memory => cases bad
  | ub control fault memory =>
    change none = some next at actual
    cases actual
  | unsupported control reason memory => cases bad

theorem unsupported_no_padding (count : Nat) :
    (∀ reached, ¬ RPrefix unsupportedCall (count + 1) runsupported reached) ∧
      (∀ reached, ¬ FPrefix unsupportedCall (count + 1) funsupported reached) := by
  constructor
  · intro reached
    apply prefix_stopped
    intro next edge
    obtain ⟨candidate, actual⟩ := edge
    change none = some next at actual
    cases actual
  · intro reached
    apply prefix_stopped
    intro next edge
    obtain ⟨candidate, actual⟩ := edge
    change none = some next at actual
    cases actual

#print axioms born_reify
#print axioms candidate_zero_rejected
#print axioms candidate16_actual
#print axioms candidate32_actual
#print axioms candidate32_bounds_load
#print axioms factored_candidate16_actual
#print axioms factored_candidate32_actual
#print axioms prefix_invariant
#print axioms prefix_stopped
#print axioms reference_loop_prefix
#print axioms factored_loop_prefix
#print axioms reference_loop_NoUB
#print axioms factored_loop_NoUB
#print axioms initial_reify
#print axioms initial_sized
#print axioms reference_candidates
#print axioms reference_bad_load
#print axioms reference_rejected_but_enabled
#print axioms reference_safe_NoUB
#print axioms factored_safe_NoUB
#print axioms reference_alternative_prefixes
#print axioms reference_initial_not_NoUB
#print axioms lift_actual_next
#print axioms factored_rejected_but_enabled
#print axioms factored_safe_witness
#print axioms factored_bad_witness
#print axioms factored_initial_not_NoUB
#print axioms actual_unsupported
#print axioms unsupported_reached
#print axioms reference_bad_no_padding
#print axioms actual_factored_bad_no_padding
#print axioms unsupported_no_padding

end AnnealResearch.TreeChoiceControls
