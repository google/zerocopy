import AnnealResearch.TreeEndCall
import AnnealResearch.TreeMemoryOperations

/-!
A selected owned ResumeUnwind phase: one stored caller and departing callee,
one local, and BackToCaller. The actual stored callee supplies every operand.
The outer Option is structural selection, separate from owned noChoice.

Snapshot.detached is ghost observation outside Config, including at errors.
It is not a frame still stored in the source machine. Memory operations are
actual existing R/F operations; both runners share the disclosed stack/PC rules.
No source import, Rust/SpecR adequacy, Return/Drop, race checking, or NoUB claim.
-/

namespace AnnealResearch.ResumeUnwindPhase

structure PC where
  block : Nat
  statement : Nat
  deriving DecidableEq, Repr

structure Local where
  name : Nat
  pointer : TreeMemory.Pointer
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

inductive Action where
  | bottom
  | backToCaller (unwindBlock : Option Nat)
  deriving DecidableEq, Repr

structure Frame (P : Type) where
  pc : PC
  localSlot : Option Local
  extra : TreeEndCall.SuppliedFrameExtra
  action : Action
  payload : P

/-- push adds the last/source-active frame, rather than a source-list head. -/
inductive Stack (P : Type) where
  | empty
  | push (stem : Stack P) (frame : Frame P)

variable {P C M N : Type}

def view : Stack P → List (Frame P)
  | .empty => []
  | .push stem frame => view stem ++ [frame]

def pop : Stack P → Option (Stack P × Frame P)
  | .empty => none
  | .push stem frame => some (stem, frame)

/-- A list-last observer used only to state the source-order adapter. -/
def sourcePop {A : Type} : List A → Option (List A × A)
  | [] => none
  | head :: tail =>
      match sourcePop tail with
      | none => some ([], head)
      | some (stem, last) => some (head :: stem, last)

private theorem sourcePop_append {A : Type} (stem : List A) (last : A) :
    sourcePop (stem ++ [last]) = some (stem, last) := by
  induction stem with
  | nil => rfl
  | cons head tail ih => simp [sourcePop, ih]

theorem source_adapter_pop (stem : Stack P) (frame : Frame P) :
    sourcePop (view (.push stem frame)) =
      (pop (.push stem frame)).map (fun (rest, top) => (view rest, top)) := by
  simpa only [view, pop, Option.map_some] using sourcePop_append (view stem) frame

structure Config (M P C : Type) where
  memory : M
  stack : Stack P
  context : C

abbrev RConfig (P C : Type) := Config TreeMemory.State P C
abbrev FConfig (P C : Type) := Config TreeFactoredMemory.State P C

structure Selection (P : Type) where
  caller : Frame P
  callee : Frame P
  slot : Local
  target : Option Nat

/-- A structural selector, not a safety or primitive-success test. -/
def pick : Stack P → Option (Selection P)
  | .push (.push .empty caller) callee =>
      match callee.localSlot, callee.action with
      | some slot, .backToCaller target => some ⟨caller, callee, slot, target⟩
      | _, _ => none
  | _ => none

def Selected (stack : Stack P) : Prop :=
  ∃ caller callee slot target,
    stack = .push (.push .empty caller) callee ∧
    callee.localSlot = some slot ∧ callee.action = .backToCaller target

theorem pick_complete (caller callee : Frame P) (slot : Local) (target : Option Nat)
    (slotFound : callee.localSlot = some slot)
    (actionFound : callee.action = .backToCaller target) :
    pick (.push (.push .empty caller) callee) = some ⟨caller, callee, slot, target⟩ := by
  simp [pick, slotFound, actionFound]

theorem pick_sound (stack : Stack P) (chosen : Selection P)
    (observed : pick stack = some chosen) :
    stack = .push (.push .empty chosen.caller) chosen.callee ∧
      chosen.callee.localSlot = some chosen.slot ∧
      chosen.callee.action = .backToCaller chosen.target := by
  cases stack with
  | empty => simp [pick] at observed
  | push below callee =>
      cases below with
      | empty => simp [pick] at observed
      | push bottom caller =>
          cases bottom with
          | push older frame => simp [pick] at observed
          | empty =>
              cases slotFound : callee.localSlot with
              | none => simp [pick, slotFound] at observed
              | some slot =>
                  cases actionFound : callee.action with
                  | bottom => simp [pick, slotFound, actionFound] at observed
                  | backToCaller target =>
                      have same : (⟨caller, callee, slot, target⟩ : Selection P) = chosen := by
                        simpa [pick, slotFound, actionFound] using observed
                      cases same
                      exact ⟨rfl, slotFound, actionFound⟩

theorem selected_iff_pick (stack : Stack P) :
    Selected stack ↔ ∃ chosen, pick stack = some chosen := by
  constructor
  · rintro ⟨caller, callee, slot, target, stackFound, slotFound, actionFound⟩
    refine ⟨⟨caller, callee, slot, target⟩, ?_⟩
    rw [stackFound]
    exact pick_complete caller callee slot target slotFound actionFound
  · rintro ⟨chosen, observed⟩
    exact ⟨chosen.caller, chosen.callee, chosen.slot, chosen.target,
      pick_sound stack chosen observed⟩

structure Snapshot (M P C : Type) where
  config : Config M P C
  /-- Ghost detached progress, never a Config field. -/
  detached : Frame P

inductive PhaseFault where
  | memory (reason : TreeMemory.Fault)
  | missingContinuation
  deriving DecidableEq, Repr

inductive PhaseResult (M P C : Type) where
  | ok (after : Snapshot M P C)
  | ub (fault : PhaseFault) (after : Snapshot M P C)
  | unsupported (reason : TreeMemory.Unsupported) (after : Snapshot M P C)
  | noChoice (after : Snapshot M P C)

def PhaseResult.residual : PhaseResult M P C → Snapshot M P C
  | .ok after => after
  | .ub _ after => after
  | .unsupported _ after => after
  | .noChoice after => after

abbrev RResult (P C : Type) := PhaseResult TreeMemory.State P C
abbrev FResult (P C : Type) := PhaseResult TreeFactoredMemory.State P C

def removeLocal (callee : Frame P) : Frame P := { callee with localSlot := none }

def jumpFrame (caller : Frame P) (target : Nat) : Frame P :=
  { caller with pc := ⟨target, 0⟩ }

/-- Pure explicit residual constructor, not extraction from a result. -/
def stopped (initial : Config M P C) (chosen : Selection P) (memory : M) :
    Snapshot M P C :=
  { config := { memory, stack := .push .empty chosen.caller, context := initial.context }
    detached := removeLocal chosen.callee }

/-- Pure explicit successful residual constructor, preserving other caller data. -/
def completed (initial : Config M P C) (chosen : Selection P) (memory : M)
    (target : Nat) : Snapshot M P C :=
  { config := {
      memory := memory
      stack := .push .empty (jumpFrame chosen.caller target)
      context := initial.context }
    detached := removeLocal chosen.callee }

def finish (initial : Config M P C) (chosen : Selection P) (memory : M) :
    PhaseResult M P C :=
  match chosen.target with
  | none => .ub .missingContinuation (stopped initial chosen memory)
  | some target => .ok (completed initial chosen memory target)

theorem finish_memory (initial : Config M P C) (chosen : Selection P) (memory : M) :
    (finish initial chosen memory).residual.config.memory = memory := by
  cases targetFound : chosen.target <;>
    simp [finish, targetFound, PhaseResult.residual, stopped, completed]

private def executeR (initial : RConfig P C) (chosen : Selection P) : RResult P C :=
  let popped : RConfig P C := { initial with stack := .push .empty chosen.caller }
  match TreeMemory.deallocate popped.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align with
  | .ok () freed =>
      match TreeEndCall.rEndCall freed chosen.callee.extra with
      | .ok () released => finish popped chosen released
      | .ub fault after => .ub (.memory fault) (stopped popped chosen after)
      | .unsupported reason after => .unsupported reason (stopped popped chosen after)
      | .noChoice after => .noChoice (stopped popped chosen after)
  | .ub fault after => .ub (.memory fault) (stopped popped chosen after)
  | .unsupported reason after => .unsupported reason (stopped popped chosen after)
  | .noChoice after => .noChoice (stopped popped chosen after)

/-- The only public reference runner input is the actual configuration. -/
def runR (initial : RConfig P C) : Option (RResult P C) :=
  (pick initial.stack).map (executeR initial)

theorem runR_domain (initial : RConfig P C) :
    (∃ actual, runR initial = some actual) ↔ Selected initial.stack := by
  constructor
  · rintro ⟨actual, observed⟩
    cases picked : pick initial.stack with
    | none => simp [runR, picked] at observed
    | some chosen => exact (selected_iff_pick initial.stack).mpr ⟨chosen, picked⟩
  · intro selected
    rcases (selected_iff_pick initial.stack).mp selected with ⟨chosen, picked⟩
    exact ⟨executeR initial chosen, by simp only [runR, picked, Option.map_some]⟩

/-- Complete equation: no successful operation, validity or NoUB admission. -/
theorem runR_equation (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) :
    runR initial = some
      (match TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
          chosen.slot.size chosen.slot.align with
      | .ok () freed =>
          match TreeEndCall.rEndCall freed chosen.callee.extra with
          | .ok () released => finish initial chosen released
          | .ub fault after => .ub (.memory fault) (stopped initial chosen after)
          | .unsupported reason after => .unsupported reason (stopped initial chosen after)
          | .noChoice after => .noChoice (stopped initial chosen after)
      | .ub fault after => .ub (.memory fault) (stopped initial chosen after)
      | .unsupported reason after => .unsupported reason (stopped initial chosen after)
      | .noChoice after => .noChoice (stopped initial chosen after)) := by
  simp only [runR, picked, Option.map_some, executeR] <;> rfl

theorem runR_deallocate_ub (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (fault : TreeMemory.Fault)
    (after : TreeMemory.State)
    (observed : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .ub fault after) :
    runR initial = some (.ub (.memory fault) (stopped initial chosen after)) := by
  rw [runR_equation initial chosen picked, observed]

theorem runR_deallocate_unsupported (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (reason : TreeMemory.Unsupported)
    (after : TreeMemory.State)
    (observed : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .unsupported reason after) :
    runR initial = some (.unsupported reason (stopped initial chosen after)) := by
  rw [runR_equation initial chosen picked, observed]

theorem runR_deallocate_noChoice (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (after : TreeMemory.State)
    (observed : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .noChoice after) :
    runR initial = some (.noChoice (stopped initial chosen after)) := by
  rw [runR_equation initial chosen picked, observed]

theorem runR_endCall_ub (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (freed after : TreeMemory.State)
    (fault : TreeMemory.Fault)
    (deallocated : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .ok () freed)
    (released : TreeEndCall.rEndCall freed chosen.callee.extra = .ub fault after) :
    runR initial = some (.ub (.memory fault) (stopped initial chosen after)) := by
  rw [runR_equation initial chosen picked]
  simp only [deallocated, released]

theorem runR_endCall_unsupported (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (freed after : TreeMemory.State)
    (reason : TreeMemory.Unsupported)
    (deallocated : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .ok () freed)
    (released : TreeEndCall.rEndCall freed chosen.callee.extra = .unsupported reason after) :
    runR initial = some (.unsupported reason (stopped initial chosen after)) := by
  rw [runR_equation initial chosen picked]
  simp only [deallocated, released]

theorem runR_endCall_noChoice (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (freed after : TreeMemory.State)
    (deallocated : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .ok () freed)
    (released : TreeEndCall.rEndCall freed chosen.callee.extra = .noChoice after) :
    runR initial = some (.noChoice (stopped initial chosen after)) := by
  rw [runR_equation initial chosen picked]
  simp only [deallocated, released]

theorem runR_missingContinuation (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (freed after : TreeMemory.State)
    (deallocated : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .ok () freed)
    (released : TreeEndCall.rEndCall freed chosen.callee.extra = .ok () after)
    (missing : chosen.target = none) :
    runR initial = some (.ub .missingContinuation (stopped initial chosen after)) := by
  rw [runR_equation initial chosen picked]
  simp only [deallocated, released, finish, missing]

theorem runR_success (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (freed after : TreeMemory.State)
    (target : Nat)
    (deallocated : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align = .ok () freed)
    (released : TreeEndCall.rEndCall freed chosen.callee.extra = .ok () after)
    (present : chosen.target = some target) :
    runR initial = some (.ok (completed initial chosen after target)) := by
  rw [runR_equation initial chosen picked]
  simp only [deallocated, released, finish, present]

theorem runR_success_iff (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) :
    (∃ after, runR initial = some (.ok after)) ↔
      ∃ freed released target,
        TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
          chosen.slot.size chosen.slot.align = .ok () freed ∧
        TreeEndCall.rEndCall freed chosen.callee.extra = .ok () released ∧
        chosen.target = some target := by
  rw [runR_equation initial chosen picked]
  cases deallocated : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align with
  | ub fault after => simp
  | unsupported reason after => simp
  | noChoice after => simp
  | ok value freed =>
      cases value
      cases released : TreeEndCall.rEndCall freed chosen.callee.extra with
      | ub fault after => simp [released]
      | unsupported reason after => simp [released]
      | noChoice after => simp [released]
      | ok value after =>
          cases value
          cases targetFound : chosen.target <;>
            simp [finish, released, targetFound]

private theorem executeR_bookkeeping (initial : RConfig P C) (chosen : Selection P) :
    (executeR initial chosen).residual.config.context = initial.context ∧
      (executeR initial chosen).residual.detached = removeLocal chosen.callee := by
  dsimp only [executeR]
  cases deallocated : TreeMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align with
  | ub fault after => exact ⟨rfl, rfl⟩
  | unsupported reason after => exact ⟨rfl, rfl⟩
  | noChoice after => exact ⟨rfl, rfl⟩
  | ok value freed =>
      cases value
      dsimp only
      cases released : TreeEndCall.rEndCall freed chosen.callee.extra with
      | ub fault after => exact ⟨rfl, rfl⟩
      | unsupported reason after => exact ⟨rfl, rfl⟩
      | noChoice after => exact ⟨rfl, rfl⟩
      | ok value after =>
          cases value
          cases targetFound : chosen.target <;>
            simp [finish, targetFound, PhaseResult.residual, stopped, completed]

theorem runR_bookkeeping (initial : RConfig P C) (chosen : Selection P)
    (picked : pick initial.stack = some chosen) (actual : RResult P C)
    (observed : runR initial = some actual) :
    actual.residual.config.context = initial.context ∧
      actual.residual.detached = removeLocal chosen.callee := by
  have same : executeR initial chosen = actual := by
    apply Option.some.inj
    simpa only [runR, picked, Option.map_some] using observed
  rw [← same]
  exact executeR_bookkeeping initial chosen

def mapConfig (mapMemory : M → N) (initial : Config M P C) : Config N P C :=
  { memory := mapMemory initial.memory, stack := initial.stack, context := initial.context }

def mapSnapshot (mapMemory : M → N) (after : Snapshot M P C) : Snapshot N P C :=
  { config := mapConfig mapMemory after.config, detached := after.detached }

def mapResult (mapMemory : M → N) : PhaseResult M P C → PhaseResult N P C
  | .ok after => .ok (mapSnapshot mapMemory after)
  | .ub fault after => .ub fault (mapSnapshot mapMemory after)
  | .unsupported reason after => .unsupported reason (mapSnapshot mapMemory after)
  | .noChoice after => .noChoice (mapSnapshot mapMemory after)

def reifyConfig (initial : FConfig P C) : RConfig P C :=
  mapConfig TreeFactoredMemory.reify initial

def translate (after : FResult P C) : RResult P C :=
  mapResult TreeFactoredMemory.reify after

/-- Independent actual F memory calls; stack/PC constructors are shared. -/
private def executeF (initial : FConfig P C) (chosen : Selection P) : FResult P C :=
  let popped : FConfig P C := { initial with stack := .push .empty chosen.caller }
  match TreeFactoredMemory.deallocate popped.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align with
  | .ok () freed =>
      match TreeEndCall.fEndCall freed chosen.callee.extra with
      | .ok () released => finish popped chosen released
      | .ub fault after => .ub (.memory fault) (stopped popped chosen after)
      | .unsupported reason after => .unsupported reason (stopped popped chosen after)
      | .noChoice after => .noChoice (stopped popped chosen after)
  | .ub fault after => .ub (.memory fault) (stopped popped chosen after)
  | .unsupported reason after => .unsupported reason (stopped popped chosen after)
  | .noChoice after => .noChoice (stopped popped chosen after)

def runF (initial : FConfig P C) : Option (FResult P C) :=
  (pick initial.stack).map (executeF initial)

private theorem execute_agrees (initial : FConfig P C) (chosen : Selection P)
    (sized : TreeFactoredMemory.WellSized initial.memory) :
    executeR (reifyConfig initial) chosen = translate (executeF initial chosen) := by
  dsimp only [executeR, executeF, reifyConfig, mapConfig]
  rw [TreeMemoryOperations.deallocate_agrees initial.memory chosen.slot.pointer .stack
    chosen.slot.size chosen.slot.align sized]
  cases deallocated : TreeFactoredMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align with
  | ub fault after => rfl
  | unsupported reason after => rfl
  | noChoice after => rfl
  | ok value freed =>
      cases value
      have freedSized : TreeFactoredMemory.WellSized freed := by
        simpa only [TreeMemoryDomain.ResultWellSized, deallocated,
          TreeFactoredMemory.Result.residual] using
          TreeMemoryPreservation.deallocate_preserves initial.memory chosen.slot.pointer
            .stack chosen.slot.size chosen.slot.align sized
      simp only [TreeFactoredMemory.translate]
      rw [TreeEndCall.endCall_agrees freed chosen.callee.extra freedSized]
      cases released : TreeEndCall.fEndCall freed chosen.callee.extra with
      | ub fault after => rfl
      | unsupported reason after => rfl
      | noChoice after => rfl
      | ok value after =>
          cases value
          cases targetFound : chosen.target <;>
            simp [TreeFactoredMemory.translate, finish, targetFound, translate,
              mapResult, mapSnapshot, mapConfig, stopped, completed]

/-- Exact full-result equality; nonselected shapes yield outer none on both sides.
No reification injectivity or memory admission beyond width is assumed. -/
theorem run_agrees (initial : FConfig P C)
    (sized : TreeFactoredMemory.WellSized initial.memory) :
    runR (reifyConfig initial) = (runF initial).map translate := by
  cases picked : pick initial.stack with
  | none => simp only [runR, runF, reifyConfig, mapConfig, picked, Option.map_none]
  | some chosen =>
      simpa only [runR, runF, reifyConfig, mapConfig, picked, Option.map_some] using
        congrArg some (execute_agrees initial chosen sized)

def ResultSized (actual : FResult P C) : Prop :=
  TreeFactoredMemory.WellSized actual.residual.config.memory

private theorem executeF_preserves (initial : FConfig P C) (chosen : Selection P)
    (sized : TreeFactoredMemory.WellSized initial.memory) :
    ResultSized (executeF initial chosen) := by
  have afterFree := TreeMemoryPreservation.deallocate_preserves initial.memory
    chosen.slot.pointer .stack chosen.slot.size chosen.slot.align sized
  dsimp only [ResultSized, executeF]
  cases deallocated : TreeFactoredMemory.deallocate initial.memory chosen.slot.pointer .stack
      chosen.slot.size chosen.slot.align with
  | ub fault after =>
      simpa only [TreeMemoryDomain.ResultWellSized, deallocated,
        TreeFactoredMemory.Result.residual, PhaseResult.residual, stopped] using afterFree
  | unsupported reason after =>
      simpa only [TreeMemoryDomain.ResultWellSized, deallocated,
        TreeFactoredMemory.Result.residual, PhaseResult.residual, stopped] using afterFree
  | noChoice after =>
      simpa only [TreeMemoryDomain.ResultWellSized, deallocated,
        TreeFactoredMemory.Result.residual, PhaseResult.residual, stopped] using afterFree
  | ok value freed =>
      cases value
      dsimp only
      have freedSized : TreeFactoredMemory.WellSized freed := by
        simpa only [TreeMemoryDomain.ResultWellSized, deallocated,
          TreeFactoredMemory.Result.residual] using afterFree
      have afterCall := TreeEndCall.fEndCall_preserves freed chosen.callee.extra freedSized
      cases released : TreeEndCall.fEndCall freed chosen.callee.extra with
      | ub fault after =>
          simpa only [TreeMemoryDomain.ResultWellSized, released,
            TreeFactoredMemory.Result.residual, PhaseResult.residual, stopped] using afterCall
      | unsupported reason after =>
          simpa only [TreeMemoryDomain.ResultWellSized, released,
            TreeFactoredMemory.Result.residual, PhaseResult.residual, stopped] using afterCall
      | noChoice after =>
          simpa only [TreeMemoryDomain.ResultWellSized, released,
            TreeFactoredMemory.Result.residual, PhaseResult.residual, stopped] using afterCall
      | ok value after =>
          cases value
          dsimp only
          rw [finish_memory]
          simpa only [TreeMemoryDomain.ResultWellSized, released,
            TreeFactoredMemory.Result.residual] using afterCall

theorem runF_preserves (initial : FConfig P C) (actual : FResult P C)
    (sized : TreeFactoredMemory.WellSized initial.memory)
    (observed : runF initial = some actual) : ResultSized actual := by
  cases picked : pick initial.stack with
  | none => simp [runF, picked] at observed
  | some chosen =>
      have same : executeF initial chosen = actual := by
        apply Option.some.inj
        simpa only [runF, picked, Option.map_some] using observed
      rw [← same]
      exact executeF_preserves initial chosen sized

#print axioms source_adapter_pop
#print axioms pick_complete
#print axioms pick_sound
#print axioms selected_iff_pick
#print axioms finish_memory
#print axioms runR_domain
#print axioms runR_equation
#print axioms runR_deallocate_ub
#print axioms runR_deallocate_unsupported
#print axioms runR_deallocate_noChoice
#print axioms runR_endCall_ub
#print axioms runR_endCall_unsupported
#print axioms runR_endCall_noChoice
#print axioms runR_missingContinuation
#print axioms runR_success
#print axioms runR_success_iff
#print axioms runR_bookkeeping
#print axioms run_agrees
#print axioms runF_preserves

end AnnealResearch.ResumeUnwindPhase
