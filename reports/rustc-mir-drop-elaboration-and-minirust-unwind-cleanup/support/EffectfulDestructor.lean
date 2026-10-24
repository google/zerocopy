import AnnealResearch.MemoryPermissions
import AnnealResearch.Execution

/-!
Common owned destructor engine for the independent controllers in TwoCleanup.
Its explicit policy is read u8, increment modulo 256, write, then return/unwind.
The selected outcome does not assert that real Rust library calls cannot unwind.
Every intermediate kernel failure is terminal and retains its residual state.
engineCost counts engine actions only; caller CFG administration is excluded.
No total execution-time, Rust/ISA, Drop, or full Tree Borrows claim is made.
-/

namespace AnnealResearch.EffectfulDestructor

open MemoryPermissions Execution

inductive Field where | first | second deriving DecidableEq
inductive Mode where | normal | unwinding deriving DecidableEq
inductive Exit where | returned | unwound deriving DecidableEq

def increment (value : Fin 256) : Fin 256 :=
  ⟨(value.val + 1) % 256, Nat.mod_lt _ (by decide)⟩

inductive Phase where
  | read | compute (old : Fin 256) | write (value : Fin 256) | decide
  | returned | unwound | bad (fault : Fault) | unsupported

inductive Event where
  | entered (field : Field)
  | read (field : Field) (value : Fin 256)
  | incremented (field : Field) (old value : Fin 256)
  | written (field : Field) (value : Fin 256)
  | returned (field : Field) | unwound (field : Field)
  | failed (field : Field) (fault : Fault)
  | unsupported (field : Field) | unexpectedReply (field : Field)
  | finished (mode : Mode) | rejectedDoubleUnwind

structure Data (S : Type) where
  memory : S
  events : List Event := []
  engineCost : Nat := 0

def Data.record {S : Type} (data : Data S) (event : Event) : Data S :=
  { data with events := data.events ++ [event] }

def Data.emitWith {S : Type} (data : Data S) (memory : S) (event : Event) : Data S :=
  ⟨memory, data.events ++ [event], data.engineCost + 1⟩

def Data.emit {S : Type} (data : Data S) (event : Event) : Data S :=
  data.emitWith data.memory event

structure State (S : Type) where
  phase : Phase
  data : Data S

def readContinuation (field : Field) : Reply → Phase × Event
  | .number value => (.compute value, .read field value)
  | _ => (.unsupported, .unexpectedReply field)

def writeContinuation (field : Field) (value : Fin 256) : Reply → Phase × Event
  | .unit => (.decide, .written field value)
  | _ => (.unsupported, .unexpectedReply field)

def handle {S : Type} (field : Field) (data : Data S)
    (continuation : Reply → Phase × Event) : Result Reply S → Option (State S)
  | .ok reply memory => some ⟨(continuation reply).1, data.emitWith memory (continuation reply).2⟩
  | .ub fault memory => some ⟨.bad fault, data.emitWith memory (.failed field fault)⟩
  | .unsupported memory => some ⟨.unsupported, data.emitWith memory (.unsupported field)⟩
  | .noChoice _ => none

def exitPhase : Exit → Phase | .returned => .returned | .unwound => .unwound
def exitEvent (field : Field) : Exit → Event
  | .returned => .returned field | .unwound => .unwound field

def next {S : Type} (runner : Command → S → Result Reply S)
    (pointer : MiniRustReference.Ptr) (field : Field) (outcome : Exit)
    (state : State S) : Option (State S) :=
  match state.phase with
  | .read => handle field state.data (readContinuation field)
      (runner (.readU8 pointer 1 1) state.data.memory)
  | .compute old => some ⟨.write (increment old), state.data.emit (.incremented field old (increment old))⟩
  | .write value => handle field state.data (writeContinuation field value)
      (runner (.writeRaw pointer 1 1 (.init value none)) state.data.memory)
  | .decide => some ⟨exitPhase outcome, state.data.emit (exitEvent field outcome)⟩
  | .returned | .unwound | .bad _ | .unsupported => none

def Step {S : Type} (runner : Command → S → Result Reply S)
    (pointer : MiniRustReference.Ptr) (field : Field) (outcome : Exit)
    (before after : State S) : Prop := next runner pointer field outcome before = some after

def Bad {S : Type} (state : State S) : Prop :=
  match state.phase with | .bad _ => True | _ => False

def completedData {S : Type} (data : Data S) (readMemory writtenMemory : S)
    (field : Field) (value : Fin 256) (outcome : Exit) : Data S :=
  (((data.emitWith readMemory (.read field value)).emit
    (.incremented field value (increment value))).emitWith writtenMemory
      (.written field (increment value))).emit (exitEvent field outcome)

/-- Conditional four-step execution over the actual supplied kernel results.
Neither initial initialization nor successful access is inferred from ownership. -/
theorem effectful_call {S : Type} (runner : Command → S → Result Reply S)
    (pointer : MiniRustReference.Ptr) (field : Field) (outcome : Exit)
    (data : Data S) (readMemory writtenMemory : S) (value : Fin 256)
    (readOK : runner (.readU8 pointer 1 1) data.memory = .ok (.number value) readMemory)
    (writeOK : runner (.writeRaw pointer 1 1 (.init (increment value) none)) readMemory =
      .ok .unit writtenMemory) :
    Reach (Step runner pointer field outcome) ⟨.read, data⟩
      ⟨exitPhase outcome, completedData data readMemory writtenMemory field value outcome⟩ := by
  let d1 := data.emitWith readMemory (.read field value)
  let d2 := d1.emit (.incremented field value (increment value))
  let d3 := d2.emitWith writtenMemory (.written field (increment value))
  have first : Step runner pointer field outcome ⟨.read, data⟩ ⟨.compute value, d1⟩ := by
    simp [Step, next, handle, readContinuation, readOK, d1]
  have second : Step runner pointer field outcome ⟨.compute value, d1⟩ ⟨.write (increment value), d2⟩ := rfl
  have third : Step runner pointer field outcome ⟨.write (increment value), d2⟩ ⟨.decide, d3⟩ := by
    simp [Step, next, handle, writeContinuation, writeOK, d2, d1, d3, Data.emit, Data.emitWith]
  have fourth : Step runner pointer field outcome ⟨.decide, d3⟩
      ⟨exitPhase outcome, completedData data readMemory writtenMemory field value outcome⟩ := rfl
  exact Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.refl _) first) second) third) fourth

theorem completed_memory {S : Type} (data : Data S) (readMemory writtenMemory : S)
    (field : Field) (value : Fin 256) (outcome : Exit) :
    (completedData data readMemory writtenMemory field value outcome).memory = writtenMemory := rfl

theorem completed_engineCost {S : Type} (data : Data S) (readMemory writtenMemory : S)
    (field : Field) (value : Fin 256) (outcome : Exit) :
    (completedData data readMemory writtenMemory field value outcome).engineCost = data.engineCost + 4 := by
  simp [completedData, Data.emit, Data.emitWith, Nat.add_assoc]

theorem failure_keeps_residual {S : Type} (field : Field) (data : Data S)
    (continuation : Reply → Phase × Event) (fault : Fault) (memory : S) :
    handle field data continuation (.ub fault memory) =
      some ⟨.bad fault, ⟨memory, data.events ++ [.failed field fault], data.engineCost + 1⟩⟩ := rfl

theorem noChoice_has_no_step {S : Type} (field : Field) (data : Data S)
    (continuation : Reply → Phase × Event) (memory : S) :
    handle field data continuation (.noChoice memory) = none := rfl

namespace Concrete

open MemoryPermissions.Fixtures

def cell (memory : MiniRustReference.State) : Coupled := ⟨memory, allCell⟩

theorem allCell_update (access : BorrowFrame.Access) :
    BorrowFrame.update allCell access .Cell = allCell := by
  funext byte tag
  unfold BorrowFrame.update
  split
  · split
    · rfl
    · cases access.kind <;> rfl
  · rfl

theorem allCell_permission (id offset tag : Nat) (kind : BorrowFrame.AccessKind) :
    permissionStep allCell id offset tag kind = .ok allCell := by
  unfold permissionStep BorrowFrame.perform
  have transitionOK : BorrowFrame.localTransition kind (allCell ⟨id, offset⟩ tag) = .ok .Cell := by
    cases kind <;> rfl
  simp only [transitionOK, allCell_update]

def pairMemory (first second : Fin 256) : MiniRustReference.State := liveMemory (byte first) (byte second)
def pair (first second : Fin 256) : Coupled := cell (pairMemory first second)

def firstAllocation (first second : Fin 256) : MiniRustReference.Allocation :=
  let bytes := [byte (increment first)]
  let allocation := block (byte first) (byte second)
  let writtenData : Nat → MiniRustReference.Byte := fun index =>
    if 0 ≤ index ∧ index < 0 + bytes.length then bytes.getD (index - 0) .uninit
    else allocation.data index
  { allocation with data := writtenData }

def firstMemory (first second : Fin 256) : MiniRustReference.State :=
  MiniRustReference.replace (pairMemory first second) 0 (firstAllocation first second)
def firstWritten (first second : Fin 256) : Coupled := cell (firstMemory first second)

def secondAllocation (first second : Fin 256) : MiniRustReference.Allocation :=
  let bytes := [byte (increment second)]
  let allocation := firstAllocation first second
  let writtenData : Nat → MiniRustReference.Byte := fun index =>
    if 1 ≤ index ∧ index < 1 + bytes.length then bytes.getD (index - 1) .uninit
    else allocation.data index
  { allocation with data := writtenData }

def secondMemory (first second : Fin 256) : MiniRustReference.State :=
  MiniRustReference.replace (firstMemory first second) 0 (secondAllocation first second)
def bothWritten (first second : Fin 256) : Coupled := cell (secondMemory first second)

theorem typed_cell_read {memory : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    {value : Fin 256} {span : MiniRustReference.CheckedSpan}
    (loaded : MiniRustReference.load memory pointer 1 1 = .ok ([byte value], memory))
    (checked : MiniRustReference.checkPtr memory pointer 1 = .ok (some span)) :
    runCoupled (.readU8 pointer 1 1) (cell memory) = .ok (.number value) (cell memory) := by
  simp [runCoupled, readCoupled, cell, loaded, checked, allCell_permission, decodeInitialized, byte]

theorem cell_write {memory after : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    {value : Fin 256} {span : MiniRustReference.CheckedSpan}
    (stored : MiniRustReference.store memory pointer [byte value] 1 = .ok after)
    (checked : MiniRustReference.checkPtr memory pointer 1 = .ok (some span)) :
    runCoupled (.writeRaw pointer 1 1 (byte value)) (cell memory) = .ok .unit (cell after) := by
  simp [runCoupled, writeCoupled, cell, stored, checked, allCell_permission]

theorem first_read (first second : Fin 256) :
    runCoupled (.readU8 pointer0 1 1) (pair first second) =
      .ok (.number first) (pair first second) :=
  typed_cell_read (span := ⟨0, block (byte first) (byte second), 0⟩) rfl rfl

theorem first_write (first second : Fin 256) :
    runCoupled (.writeRaw pointer0 1 1 (byte (increment first))) (pair first second) =
      .ok .unit (firstWritten first second) :=
  cell_write (span := ⟨0, block (byte first) (byte second), 0⟩) rfl rfl

theorem second_read (first second : Fin 256) :
    runCoupled (.readU8 pointer1 1 1) (firstWritten first second) =
      .ok (.number second) (firstWritten first second) :=
  typed_cell_read (span := ⟨0, firstAllocation first second, 1⟩) rfl rfl

theorem second_write (first second : Fin 256) :
    runCoupled (.writeRaw pointer1 1 1 (byte (increment second))) (firstWritten first second) =
      .ok .unit (bothWritten first second) :=
  cell_write (span := ⟨0, firstAllocation first second, 1⟩) rfl rfl

theorem first_write_still_present_at_second_entry (first second : Fin 256) :
    MiniRustReference.load (firstWritten first second).memory pointer0 1 1 =
      .ok ([byte (increment first)], (firstWritten first second).memory) := rfl

theorem both_payloads_updated (first second : Fin 256) :
    MiniRustReference.load (bothWritten first second).memory pointer0 1 1 =
      .ok ([byte (increment first)], (bothWritten first second).memory) ∧
    MiniRustReference.load (bothWritten first second).memory pointer1 1 1 =
      .ok ([byte (increment second)], (bothWritten first second).memory) := ⟨rfl, rfl⟩

end Concrete

#print axioms effectful_call
#print axioms completed_memory
#print axioms completed_engineCost
#print axioms failure_keeps_residual
#print axioms noChoice_has_no_step
#print axioms Concrete.first_read
#print axioms Concrete.first_write
#print axioms Concrete.second_read
#print axioms Concrete.second_write
#print axioms Concrete.first_write_still_present_at_second_entry
#print axioms Concrete.both_payloads_updated

end AnnealResearch.EffectfulDestructor
