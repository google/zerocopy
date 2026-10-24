import AnnealResearch.EffectfulDestructor
import AnnealResearch.MemoryPermissionInvariants
import AnnealResearch.TwoCleanup

/-!
Structural admission and engine-level controls for effectful cleanup.
MemoryWF remains the existing BasicMemory structural predicate, with no NoUB,
initialization, access-success, or permission-safety premise. The engine writes
only numeric no-fragment bytes, so its written-byte admission is automatic.

The rollback query is an ACTUAL runCoupled read of a live owned allCell
allocation. It is not a Rust post-drop-access guarantee: the audited Rust second
destructor reads its own field, not the first field. The retry control invokes
the engine a second time from an explicit restarted read phase; it does not
claim that the original engine has an edge out of its unwound terminal phase,
or that either full cleanup controller performs that restart. These controls
challenge exact owned state/effect preservation, not every Rust optimization.
-/

namespace AnnealResearch.EffectfulControls

open Execution MemoryPermissions EffectfulDestructor

namespace Admission

def EngineMemoryWF (state : State Coupled) : Prop :=
  MemoryPermissionInvariants.MemoryWF state.data.memory

/-- All result categories retain their actual residual property. noChoice has
no engine successor, rather than becoming a successful or bad configuration. -/
theorem handle_preserves_property {S : Type} (property : S → Prop)
    (field : Field) (data : Data S) (continuation : Reply → Phase × Event)
    (answer : Result Reply S) (after : State S)
    (known : MemoryPermissionInvariants.ResidualHolds property answer)
    (handled : handle field data continuation answer = some after) :
    property after.data.memory := by
  cases answer with
  | ok reply memory =>
      have same : (⟨(continuation reply).1,
        data.emitWith memory (continuation reply).2⟩ : State S) = after :=
        Option.some.inj handled
      rw [← same]
      exact known
  | ub fault memory =>
      have same : (⟨.bad fault, data.emitWith memory (.failed field fault)⟩ : State S) = after :=
        Option.some.inj handled
      rw [← same]
      exact known
  | unsupported memory =>
      have same : (⟨.unsupported, data.emitWith memory (.unsupported field)⟩ : State S) = after :=
        Option.some.inj handled
      rw [← same]
      exact known
  | noChoice memory => simp [handle] at handled

theorem engine_step_preserves_MemoryWF (pointer : MiniRustReference.Ptr)
    (field : Field) (outcome : Exit) {before after : State Coupled}
    (wf : EngineMemoryWF before)
    (edge : Step runCoupled pointer field outcome before after) :
    EngineMemoryWF after := by
  change next runCoupled pointer field outcome before = some after at edge
  cases phase : before.phase with
  | read =>
      exact handle_preserves_property MemoryPermissionInvariants.MemoryWF field before.data
        (readContinuation field) (runCoupled (.readU8 pointer 1 1) before.data.memory) after
        (MemoryPermissionInvariants.runCoupled_preserves_MemoryWF before.data.memory _ wf True.intro)
        (by simpa only [next, phase] using edge)
  | compute old =>
      have same : (⟨.write (increment old),
        before.data.emit (.incremented field old (increment old))⟩ : State Coupled) = after :=
        Option.some.inj (by simpa only [next, phase] using edge)
      rw [← same]
      exact wf
  | write value =>
      exact handle_preserves_property MemoryPermissionInvariants.MemoryWF field before.data
        (writeContinuation field value)
        (runCoupled (.writeRaw pointer 1 1 (.init value none)) before.data.memory) after
        (MemoryPermissionInvariants.runCoupled_preserves_MemoryWF before.data.memory _ wf True.intro)
        (by simpa only [next, phase] using edge)
  | decide =>
      have same : (⟨exitPhase outcome,
        before.data.emit (exitEvent field outcome)⟩ : State Coupled) = after :=
        Option.some.inj (by simpa only [next, phase] using edge)
      rw [← same]
      exact wf
  | returned => simp [next, phase] at edge
  | unwound => simp [next, phase] at edge
  | bad fault => simp [next, phase] at edge
  | unsupported => simp [next, phase] at edge

/-- Includes reachable UB residuals and selected return/unwind configurations. -/
theorem engine_reachable_MemoryWF (pointer : MiniRustReference.Ptr)
    (field : Field) (outcome : Exit) {before after : State Coupled}
    (wf : EngineMemoryWF before)
    (path : Reach (Step runCoupled pointer field outcome) before after) :
    EngineMemoryWF after :=
  invariant_reachable (Step := Step runCoupled pointer field outcome)
    (Invariant := EngineMemoryWF) wf
    (fun {s t} known edge => engine_step_preserves_MemoryWF pointer field outcome
      (before := s) (after := t) known edge) path

theorem pair_MemoryWF (first second : Fin 256) :
    MemoryPermissionInvariants.MemoryWF (EffectfulDestructor.Concrete.pair first second) :=
  MemoryPermissions.Fixtures.liveMemory_WF _ _ True.intro True.intro

theorem firstWritten_MemoryWF (first second : Fin 256) :
    MemoryPermissionInvariants.MemoryWF (EffectfulDestructor.Concrete.firstWritten first second) := by
  have known := MemoryPermissionInvariants.runCoupled_preserves_MemoryWF
    (EffectfulDestructor.Concrete.pair first second)
    (.writeRaw MemoryPermissions.Fixtures.pointer0 1 1
      (MemoryPermissions.Fixtures.byte (increment first)))
    (pair_MemoryWF first second) True.intro
  rw [EffectfulDestructor.Concrete.first_write first second] at known
  exact known

theorem bothWritten_MemoryWF (first second : Fin 256) :
    MemoryPermissionInvariants.MemoryWF (EffectfulDestructor.Concrete.bothWritten first second) := by
  have known := MemoryPermissionInvariants.runCoupled_preserves_MemoryWF
    (EffectfulDestructor.Concrete.firstWritten first second)
    (.writeRaw MemoryPermissions.Fixtures.pointer1 1 1
      (MemoryPermissions.Fixtures.byte (increment second)))
    (firstWritten_MemoryWF first second) True.intro
  rw [EffectfulDestructor.Concrete.second_write first second] at known
  exact known

def pairData (first second : Fin 256) : Data Coupled :=
  ⟨EffectfulDestructor.Concrete.pair first second, [], 0⟩

theorem first_exit_residual_MemoryWF (first second : Fin 256) (outcome : Exit) :
    EngineMemoryWF
      ⟨exitPhase outcome,
        completedData (pairData first second)
          (EffectfulDestructor.Concrete.pair first second)
          (EffectfulDestructor.Concrete.firstWritten first second) .first first outcome⟩ :=
  engine_reachable_MemoryWF MemoryPermissions.Fixtures.pointer0 .first outcome
    (before := ⟨.read, pairData first second⟩) (pair_MemoryWF first second)
    (effectful_call runCoupled MemoryPermissions.Fixtures.pointer0 .first outcome
      (pairData first second) (EffectfulDestructor.Concrete.pair first second)
      (EffectfulDestructor.Concrete.firstWritten first second) first
      (EffectfulDestructor.Concrete.first_read first second)
      (EffectfulDestructor.Concrete.first_write first second))

end Admission

namespace BeforeUnwind

open MemoryPermissions.Fixtures

def initialData (value : Fin 256) : Data Coupled := ⟨aliasRead0 value, [], 0⟩
def initial (value : Fin 256) : State Coupled := ⟨.read, initialData value⟩

def readData (value : Fin 256) : Data Coupled :=
  (initialData value).emitWith (aliasRead1 value) (.read .first value)

def computeState (value : Fin 256) : State Coupled := ⟨.compute value, readData value⟩

def computedData (value : Fin 256) : Data Coupled :=
  (readData value).emit (.incremented .first value (increment value))

def writeState (value : Fin 256) : State Coupled :=
  ⟨.write (increment value), computedData value⟩

def failedData (value : Fin 256) : Data Coupled :=
  (computedData value).emitWith (aliasRead1 value) (.failed .first (.permission .localWriteFrozen))

def failed (value : Fin 256) : State Coupled :=
  ⟨.bad (.permission .localWriteFrozen), failedData value⟩

theorem read_succeeds (value : Fin 256) :
    Step runCoupled pointer0 .first .unwound (initial value) (computeState value) := rfl

theorem compute_succeeds (value : Fin 256) :
    Step runCoupled pointer0 .first .unwound (computeState value) (writeState value) := rfl

theorem write_fails_before_decide (value : Fin 256) :
    Step runCoupled pointer0 .first .unwound (writeState value) (failed value) := rfl

theorem actual_bad_prefix (value : Fin 256) :
    Reach (Step runCoupled pointer0 .first .unwound) (initial value) (failed value) :=
  Reach.tail (Reach.tail (Reach.tail (Reach.refl _) (read_succeeds value))
    (compute_succeeds value)) (write_fails_before_decide value)

theorem not_safe (value : Fin 256) :
    ¬ NoUB (Step runCoupled pointer0 .first .unwound) Bad (initial value) :=
  bad_prefix_not_noUB (actual_bad_prefix value) True.intro

theorem bad_is_terminal (value : Fin 256) :
    next runCoupled pointer0 .first .unwound (failed value) = none := rfl

theorem failure_observations (value : Fin 256) :
    (failed value).data.memory = aliasRead1 value ∧
    (failed value).data.engineCost = 3 ∧
    (failed value).data.events =
      [.read .first value, .incremented .first value (increment value),
        .failed .first (.permission .localWriteFrozen)] := ⟨rfl, rfl, rfl⟩

theorem initial_MemoryWF (value : Fin 256) : Admission.EngineMemoryWF (initial value) :=
  aliasing_WF value

/-- A structurally admitted failure is retained, not excluded by the invariant. -/
theorem bad_residual_MemoryWF (value : Fin 256) : Admission.EngineMemoryWF (failed value) :=
  Admission.engine_reachable_MemoryWF pointer0 .first .unwound
    (initial_MemoryWF value) (actual_bad_prefix value)

end BeforeUnwind

namespace RestartControls

open MemoryPermissions.Fixtures

theorem increment_zero : increment (0 : Fin 256) = 1 := by decide
theorem increment_one : increment (1 : Fin 256) = 2 := by decide

theorem actual_read_after_first_write (first second : Fin 256) :
    runCoupled (.readU8 pointer0 1 1) (EffectfulDestructor.Concrete.firstWritten first second) =
      .ok (.number (increment first)) (EffectfulDestructor.Concrete.firstWritten first second) :=
  EffectfulDestructor.Concrete.typed_cell_read
    (span := ⟨0, EffectfulDestructor.Concrete.firstAllocation first second, 0⟩) rfl rfl

/-- Restoring old memory changes an actual owned read, not just a pure
BasicMemory query. This is not the Rust fixture's second destructor access. -/
theorem rollback_changes_actual_read (second : Fin 256) :
    runCoupled (.readU8 pointer0 1 1) (EffectfulDestructor.Concrete.firstWritten 0 second) =
      .ok (.number 1) (EffectfulDestructor.Concrete.firstWritten 0 second) ∧
    runCoupled (.readU8 pointer0 1 1) (EffectfulDestructor.Concrete.pair 0 second) =
      .ok (.number 0) (EffectfulDestructor.Concrete.pair 0 second) ∧
    (1 : Fin 256) ≠ 0 := by
  exact ⟨by simpa only [increment_zero] using actual_read_after_first_write 0 second,
    EffectfulDestructor.Concrete.first_read 0 second, by decide⟩

def retryAllocation (second : Fin 256) : MiniRustReference.Allocation :=
  let bytes := [byte (increment (1 : Fin 256))]
  let allocation := EffectfulDestructor.Concrete.firstAllocation 0 second
  let writtenData : Nat → MiniRustReference.Byte := fun index =>
    if 0 ≤ index ∧ index < 0 + bytes.length then bytes.getD (index - 0) .uninit
    else allocation.data index
  { allocation with data := writtenData }

def retryMemory (second : Fin 256) : MiniRustReference.State :=
  MiniRustReference.replace (EffectfulDestructor.Concrete.firstMemory 0 second) 0
    (retryAllocation second)

def retryWritten (second : Fin 256) : Coupled := EffectfulDestructor.Concrete.cell (retryMemory second)

theorem retry_read (second : Fin 256) :
    runCoupled (.readU8 pointer0 1 1) (EffectfulDestructor.Concrete.firstWritten 0 second) =
      .ok (.number 1) (EffectfulDestructor.Concrete.firstWritten 0 second) :=
  (rollback_changes_actual_read second).1

theorem retry_write (second : Fin 256) :
    runCoupled (.writeRaw pointer0 1 1 (byte (increment (1 : Fin 256))))
        (EffectfulDestructor.Concrete.firstWritten 0 second) =
      .ok .unit (retryWritten second) :=
  EffectfulDestructor.Concrete.cell_write
    (span := ⟨0, EffectfulDestructor.Concrete.firstAllocation 0 second, 0⟩) rfl rfl

def firstCallData (second : Fin 256) : Data Coupled :=
  completedData (Admission.pairData 0 second)
    (EffectfulDestructor.Concrete.pair 0 second)
    (EffectfulDestructor.Concrete.firstWritten 0 second) .first 0 .unwound

def retryCompletedData (second : Fin 256) : Data Coupled :=
  completedData (firstCallData second)
    (EffectfulDestructor.Concrete.firstWritten 0 second) (retryWritten second) .first 1 .returned

theorem first_invocation_unwinds_after_write (second : Fin 256) :
    Reach (Step runCoupled pointer0 .first .unwound)
      ⟨.read, Admission.pairData 0 second⟩ ⟨.unwound, firstCallData second⟩ :=
  effectful_call runCoupled pointer0 .first .unwound (Admission.pairData 0 second)
    (EffectfulDestructor.Concrete.pair 0 second)
    (EffectfulDestructor.Concrete.firstWritten 0 second) 0
    (EffectfulDestructor.Concrete.first_read 0 second)
    (EffectfulDestructor.Concrete.first_write 0 second)

/-- This is a separate invocation after an explicit phase restart. There is
no claim of an engine edge from unwound back to read or of a controller path. -/
theorem retry_invocation_updates_again (second : Fin 256) :
    Reach (Step runCoupled pointer0 .first .returned)
      ⟨.read, firstCallData second⟩ ⟨.returned, retryCompletedData second⟩ :=
  effectful_call runCoupled pointer0 .first .returned (firstCallData second)
    (EffectfulDestructor.Concrete.firstWritten 0 second) (retryWritten second) 1
    (retry_read second) (retry_write second)

theorem retry_observations (second : Fin 256) :
    (retryCompletedData second).memory = retryWritten second ∧
    (retryCompletedData second).engineCost = 8 ∧
    MiniRustReference.load (retryWritten second).memory pointer0 1 1 =
      .ok ([byte 2], (retryWritten second).memory) := ⟨rfl, rfl, rfl⟩

theorem retry_residual_MemoryWF (second : Fin 256) :
    MemoryPermissionInvariants.MemoryWF (retryWritten second) := by
  have known := MemoryPermissionInvariants.runCoupled_preserves_MemoryWF
    (EffectfulDestructor.Concrete.firstWritten 0 second)
    (.writeRaw pointer0 1 1 (byte (increment (1 : Fin 256))))
    (Admission.firstWritten_MemoryWF 0 second) True.intro
  rw [retry_write second] at known
  exact known

end RestartControls

namespace ControllerAdmission

def HighMemoryWF (state : TwoCleanup.HighState Coupled) : Prop :=
  MemoryPermissionInvariants.MemoryWF state.data.memory

def LowMemoryWF (state : TwoCleanup.LowState Coupled) : Prop :=
  MemoryPermissionInvariants.MemoryWF state.data.memory

theorem high_step_preserves_MemoryWF (plan : TwoCleanup.Plan)
    {before after : TwoCleanup.HighState Coupled} (wf : HighMemoryWF before)
    (edge : TwoCleanup.HighStep runCoupled plan before after) : HighMemoryWF after := by
  cases edge with
  | enterBoth data mode => exact wf
  | enterFirst data mode => exact wf
  | enterSecond data mode => exact wf
  | engineFirst data afterData phase nextPhase owed mode engineEdge =>
      exact Admission.engine_step_preserves_MemoryWF (plan.pointer .first) .first plan.firstExit
        (before := ⟨phase, data⟩) (after := ⟨nextPhase, afterData⟩)
        (show Admission.EngineMemoryWF ⟨phase, data⟩ from wf) engineEdge
  | engineSecond data afterData phase nextPhase mode engineEdge =>
      exact Admission.engine_step_preserves_MemoryWF (plan.pointer .second) .second .returned
        (before := ⟨phase, data⟩) (after := ⟨nextPhase, afterData⟩)
        (show Admission.EngineMemoryWF ⟨phase, data⟩ from wf) engineEdge
  | returnedFirst data owed mode => exact wf
  | unwoundFirst data owed => exact wf
  | rejectedFirst data owed => exact wf
  | returnedSecond data mode => exact wf
  | unwoundSecond data => exact wf
  | rejectedSecond data => exact wf
  | finish data mode => exact wf

theorem high_reachable_MemoryWF (plan : TwoCleanup.Plan)
    {before after : TwoCleanup.HighState Coupled} (wf : HighMemoryWF before)
    (path : Reach (TwoCleanup.HighStep runCoupled plan) before after) : HighMemoryWF after :=
  invariant_reachable (Step := TwoCleanup.HighStep runCoupled plan)
    (Invariant := HighMemoryWF) wf
    (fun {s t} known edge => high_step_preserves_MemoryWF plan
      (before := s) (after := t) known edge) path

theorem low_step_preserves_MemoryWF (plan : TwoCleanup.Plan)
    {before after : TwoCleanup.LowState Coupled} (wf : LowMemoryWF before)
    (edge : TwoCleanup.LowStep runCoupled plan before after) : LowMemoryWF after := by
  cases edge with
  | testTrue ins => exact wf
  | testFalse ins => exact wf
  | clear ins => exact wf
  | invoke ins => exact wf
  | @engine data afterData field phase nextPhase normal unwind owed engineEdge =>
      exact Admission.engine_step_preserves_MemoryWF (plan.pointer field) field (TwoCleanup.outcome plan field)
        (before := ⟨phase, data⟩) (after := ⟨nextPhase, afterData⟩)
        (show Admission.EngineMemoryWF ⟨phase, data⟩ from wf) engineEdge
  | returned => exact wf
  | unwound => exact wf
  | finish ins => exact wf
  | reject ins => exact wf

theorem low_reachable_MemoryWF (plan : TwoCleanup.Plan)
    {before after : TwoCleanup.LowState Coupled} (wf : LowMemoryWF before)
    (path : Reach (TwoCleanup.LowStep runCoupled plan) before after) : LowMemoryWF after :=
  invariant_reachable (Step := TwoCleanup.LowStep runCoupled plan)
    (Invariant := LowMemoryWF) wf
    (fun {s t} known edge => low_step_preserves_MemoryWF plan
      (before := s) (after := t) known edge) path

end ControllerAdmission

namespace ControllerUB

open MemoryPermissions.Fixtures

/-- Both potential fields name the same owned byte. The second is never
entered: permission UB stops the first engine before its selected unwind. -/
def plan : TwoCleanup.Plan := ⟨fun _ => pointer0, .unwound⟩

def initial (value : Fin 256) : TwoCleanup.HighState Coupled :=
  TwoCleanup.initialHigh (aliasRead0 value) true

def enteredData (value : Fin 256) : Data Coupled :=
  (BeforeUnwind.initialData value).record (.entered .first)

def readData (value : Fin 256) : Data Coupled :=
  (enteredData value).emitWith (aliasRead1 value) (.read .first value)

def computedData (value : Fin 256) : Data Coupled :=
  (readData value).emit (.incremented .first value (increment value))

def failedData (value : Fin 256) : Data Coupled :=
  (computedData value).emitWith (aliasRead1 value)
    (.failed .first (.permission .localWriteFrozen))

def entered (value : Fin 256) : TwoCleanup.HighState Coupled :=
  ⟨.first .read true .normal, enteredData value⟩

def computed (value : Fin 256) : TwoCleanup.HighState Coupled :=
  ⟨.first (.compute value) true .normal, readData value⟩

def writing (value : Fin 256) : TwoCleanup.HighState Coupled :=
  ⟨.first (.write (increment value)) true .normal, computedData value⟩

def failed (value : Fin 256) : TwoCleanup.HighState Coupled :=
  ⟨.first (.bad (.permission .localWriteFrozen)) true .normal, failedData value⟩

theorem read_edge (value : Fin 256) :
    Step runCoupled pointer0 .first .unwound
      ⟨.read, enteredData value⟩ ⟨.compute value, readData value⟩ := rfl

theorem compute_edge (value : Fin 256) :
    Step runCoupled pointer0 .first .unwound
      ⟨.compute value, readData value⟩ ⟨.write (increment value), computedData value⟩ := rfl

theorem write_failure_edge (value : Fin 256) :
    Step runCoupled pointer0 .first .unwound
      ⟨.write (increment value), computedData value⟩
      ⟨.bad (.permission .localWriteFrozen), failedData value⟩ := rfl

/-- Starts at the ordinary controller entry, not a pre-entered engine state. -/
theorem high_bad_reached (value : Fin 256) :
    Reach (TwoCleanup.HighStep runCoupled plan) (initial value) (failed value) := by
  have entry : TwoCleanup.HighStep runCoupled plan (initial value) (entered value) :=
    TwoCleanup.HighStep.enterBoth _ _
  have reading : TwoCleanup.HighStep runCoupled plan (entered value) (computed value) :=
    TwoCleanup.HighStep.engineFirst _ _ _ _ _ _ (read_edge value)
  have computing : TwoCleanup.HighStep runCoupled plan (computed value) (writing value) :=
    TwoCleanup.HighStep.engineFirst _ _ _ _ _ _ (compute_edge value)
  have failing : TwoCleanup.HighStep runCoupled plan (writing value) (failed value) :=
    TwoCleanup.HighStep.engineFirst _ _ _ _ _ _ (write_failure_edge value)
  exact Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.refl _) entry) reading) computing) failing

theorem low_bad_reached (value : Fin 256) :
    Reach (TwoCleanup.LowStep runCoupled plan)
      (TwoCleanup.initialLow (aliasRead0 value) true) (TwoCleanup.compile (failed value)) :=
  TwoCleanup.compiled_reachable runCoupled plan (high_bad_reached value)

theorem high_not_safe (value : Fin 256) :
    ¬ NoUB (TwoCleanup.HighStep runCoupled plan) TwoCleanup.HighBad (initial value) :=
  bad_prefix_not_noUB (high_bad_reached value) True.intro

theorem low_not_safe (value : Fin 256) :
    ¬ NoUB (TwoCleanup.LowStep runCoupled plan) TwoCleanup.LowBad
      (TwoCleanup.initialLow (aliasRead0 value) true) :=
  bad_prefix_not_noUB (low_bad_reached value) True.intro

theorem retained_controller_observations (value : Fin 256) :
    (failed value).data.memory = aliasRead1 value ∧
    (failed value).data.engineCost = 3 ∧
    (failed value).data.events =
      [.entered .first, .read .first value,
        .incremented .first value (increment value), .failed .first (.permission .localWriteFrozen)] ∧
    (TwoCleanup.compile (failed value)).data.memory = aliasRead1 value ∧
    (TwoCleanup.compile (failed value)).secondOwed = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem high_bad_residual_MemoryWF (value : Fin 256) :
    ControllerAdmission.HighMemoryWF (failed value) :=
  ControllerAdmission.high_reachable_MemoryWF plan
    (before := initial value) (aliasing_WF value) (high_bad_reached value)

theorem low_bad_residual_MemoryWF (value : Fin 256) :
    ControllerAdmission.LowMemoryWF (TwoCleanup.compile (failed value)) :=
  ControllerAdmission.low_reachable_MemoryWF plan
    (before := TwoCleanup.initialLow (aliasRead0 value) true)
    (aliasing_WF value) (low_bad_reached value)

/-- The selected unwind outcome is not used as recovery from engine UB. -/
theorem high_bad_terminal (value : Fin 256) (after : TwoCleanup.HighState Coupled) :
    ¬ TwoCleanup.HighStep runCoupled plan (failed value) after := by
  intro edge
  cases edge with
  | engineFirst data after phase nextPhase owed mode engineEdge =>
      simp [EffectfulDestructor.Step, EffectfulDestructor.next] at engineEdge

theorem low_bad_terminal (value : Fin 256) (after : TwoCleanup.LowState Coupled) :
    ¬ TwoCleanup.LowStep runCoupled plan (TwoCleanup.compile (failed value)) after := by
  intro edge
  cases edge with
  | engine engineEdge =>
      simp [EffectfulDestructor.Step, EffectfulDestructor.next] at engineEdge

end ControllerUB

#print axioms Admission.handle_preserves_property
#print axioms Admission.engine_step_preserves_MemoryWF
#print axioms Admission.engine_reachable_MemoryWF
#print axioms Admission.pair_MemoryWF
#print axioms Admission.firstWritten_MemoryWF
#print axioms Admission.bothWritten_MemoryWF
#print axioms Admission.first_exit_residual_MemoryWF
#print axioms BeforeUnwind.read_succeeds
#print axioms BeforeUnwind.compute_succeeds
#print axioms BeforeUnwind.write_fails_before_decide
#print axioms BeforeUnwind.actual_bad_prefix
#print axioms BeforeUnwind.not_safe
#print axioms BeforeUnwind.bad_is_terminal
#print axioms BeforeUnwind.failure_observations
#print axioms BeforeUnwind.initial_MemoryWF
#print axioms BeforeUnwind.bad_residual_MemoryWF
#print axioms RestartControls.increment_zero
#print axioms RestartControls.increment_one
#print axioms RestartControls.actual_read_after_first_write
#print axioms RestartControls.rollback_changes_actual_read
#print axioms RestartControls.retry_read
#print axioms RestartControls.retry_write
#print axioms RestartControls.first_invocation_unwinds_after_write
#print axioms RestartControls.retry_invocation_updates_again
#print axioms RestartControls.retry_observations
#print axioms RestartControls.retry_residual_MemoryWF
#print axioms ControllerAdmission.high_step_preserves_MemoryWF
#print axioms ControllerAdmission.high_reachable_MemoryWF
#print axioms ControllerAdmission.low_step_preserves_MemoryWF
#print axioms ControllerAdmission.low_reachable_MemoryWF
#print axioms ControllerUB.read_edge
#print axioms ControllerUB.compute_edge
#print axioms ControllerUB.write_failure_edge
#print axioms ControllerUB.high_bad_reached
#print axioms ControllerUB.low_bad_reached
#print axioms ControllerUB.high_not_safe
#print axioms ControllerUB.low_not_safe
#print axioms ControllerUB.retained_controller_observations
#print axioms ControllerUB.high_bad_residual_MemoryWF
#print axioms ControllerUB.low_bad_residual_MemoryWF
#print axioms ControllerUB.high_bad_terminal
#print axioms ControllerUB.low_bad_terminal

end AnnealResearch.EffectfulControls
