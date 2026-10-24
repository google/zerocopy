import AnnealResearch.AtomicMessagePassingControls
import AnnealResearch.Execution

/-!
First checkpoint of the owned atomic-prefix study. The operational subject is
declared here, independently of runCandidate. Raw operations use current memory;
read-from values and raw-load bytes are separate. Raw failures have no RF,
consistency, or future-completion premise. Later modules must establish prefix
invariants and completed-candidate coverage; neither is claimed here.
-/
namespace AnnealResearch.AtomicPrefixExecution

inductive Operand where
  | healthy | noProvenance | misaligned
  deriving DecidableEq, Repr

inductive StoreOp where
  | d | f
  deriving DecidableEq, Repr

inductive Instruction where
  | store (op : StoreOp) | read (op : AtomicMessagePassing.Read)
  deriving DecidableEq, Repr

def instructionEvent : Instruction → AtomicMessagePassing.Event
  | .store .d => .d | .store .f => .f
  | .read .flag => .a | .read .data => .b

def storeWrite : StoreOp → AtomicMessagePassing.Write
  | .d => .dataStore | .f => .flagStore

structure Input where
  mode : AtomicMessagePassing.Mode
  d : Operand
  f : Operand
  a : Operand
  b : Operand
  dLabel : Nat
  fLabel : Nat
  aLabel : Nat
  bLabel : Nat
  deriving DecidableEq, Repr

def basePointer : Instruction → MiniRustReference.Ptr
  | .store .d | .read .data => AtomicMessagePassingControls.dataPointer
  | .store .f | .read .flag => AtomicMessagePassingControls.flagPointer

def operand (input : Input) : Instruction → Operand
  | .store .d => input.d | .store .f => input.f
  | .read .flag => input.a | .read .data => input.b

def label (input : Input) : Instruction → Nat
  | .store .d => input.dLabel | .store .f => input.fLabel
  | .read .flag => input.aLabel | .read .data => input.bLabel

def choosePointer (base : MiniRustReference.Ptr) : Operand → MiniRustReference.Ptr
  | .healthy => base
  | .noProvenance => { base with provenance := none }
  | .misaligned => { base with addr := base.addr + 1 }

def handle (input : Input) (instruction : Instruction) : AtomicMessagePassing.Handle :=
  ⟨choosePointer (basePointer instruction) (operand input instruction), label input instruction⟩

inductive ProducerPC where
  | d | f | done
  deriving DecidableEq, Repr

inductive ConsumerPC where
  | a | b | skipped | done
  deriving DecidableEq, Repr

structure WriteRecord where
  write : AtomicMessagePassing.Write
  location : AtomicMessagePassing.Span
  deriving DecidableEq, Repr

structure ReadRecord where
  location : AtomicMessagePassing.Span
  supplier : AtomicMessagePassing.Write
  rawBytes : List MiniRustReference.Byte
  deriving DecidableEq, Repr

/-- Atomic values are computed from supplier identity, never from rawBytes. -/
def readValue (record : ReadRecord) : Nat := AtomicMessagePassing.writeValue record.supplier

inductive AttemptOutcome where
  | stored (location : AtomicMessagePassing.Span) (write : AtomicMessagePassing.Write)
  | loaded (op : AtomicMessagePassing.Read) (record : ReadRecord)
  | ub (diagnostic : MiniRustReference.UB)
  | unsupported
  deriving DecidableEq, Repr

structure Attempt where
  instruction : Instruction
  handle : AtomicMessagePassing.Handle
  outcome : AttemptOutcome
  deriving DecidableEq, Repr

structure Machine where
  raw : MiniRustReference.State
  producer : ProducerPC
  consumer : ConsumerPC
  trace : List Attempt
  writes : List WriteRecord
  flagRead : Option ReadRecord
  dataRead : Option ReadRecord

def initialMachine : Machine :=
  { raw := AtomicMessagePassingControls.initial
    producer := .d
    consumer := .a
    trace := []
    writes := [⟨.initialData, AtomicMessagePassingControls.dataSpan⟩, ⟨.initialFlag, AtomicMessagePassingControls.flagSpan⟩]
    flagRead := none
    dataRead := none }

inductive Config where
  | running (machine : Machine)
  | normal (machine : Machine)
  | ub (instruction : Instruction) (diagnostic : MiniRustReference.UB) (machine : Machine)
  | unsupported (instruction : Instruction) (machine : Machine)

def root : Config := .running initialMachine

inductive Status where
  | running | normal
  | ub (event : AtomicMessagePassing.Event) (diagnostic : MiniRustReference.UB)
  | unsupported (event : AtomicMessagePassing.Event)
  deriving DecidableEq, Repr

/-- Full owned observer, fixed before any correspondence or mutant. -/
structure Observation where
  status : Status
  raw : MiniRustReference.State
  producer : ProducerPC
  consumer : ConsumerPC
  trace : List Attempt
  writes : List WriteRecord
  flagRead : Option ReadRecord
  dataRead : Option ReadRecord

def observeMachine (status : Status) (machine : Machine) : Observation :=
  ⟨status, machine.raw, machine.producer, machine.consumer, machine.trace,
    machine.writes, machine.flagRead, machine.dataRead⟩

def observe : Config → Observation
  | .running machine => observeMachine .running machine
  | .normal machine => observeMachine .normal machine
  | .ub instruction diagnostic machine =>
      observeMachine (.ub (instructionEvent instruction) diagnostic) machine
  | .unsupported instruction machine =>
      observeMachine (.unsupported (instructionEvent instruction)) machine

def Scheduled (machine : Machine) : Instruction → Prop
  | .store .d => machine.producer = .d
  | .store .f => machine.producer = .f
  | .read .flag => machine.consumer = .a
  | .read .data => machine.consumer = .b

def Finished (machine : Machine) : Prop :=
  machine.producer = .done ∧ (machine.consumer = .skipped ∨ machine.consumer = .done)

def readRecord (machine : Machine) : AtomicMessagePassing.Read → Option ReadRecord
  | .flag => machine.flagRead | .data => machine.dataRead

def ReadAt (machine : Machine) (op : AtomicMessagePassing.Read) (record : ReadRecord) : Prop :=
  readRecord machine op = some record

def WriteAt (machine : Machine) (write : AtomicMessagePassing.Write) (location : AtomicMessagePassing.Span) : Prop :=
  ⟨write, location⟩ ∈ machine.writes

def WritePresent (machine : Machine) (write : AtomicMessagePassing.Write) : Prop :=
  ∃ location, WriteAt machine write location

def ReadPresent (machine : Machine) (op : AtomicMessagePassing.Read) : Prop :=
  ∃ record, ReadAt machine op record

def EventPresent (machine : Machine) (event : AtomicMessagePassing.Event) : Prop :=
  (∃ write, WritePresent machine write ∧ AtomicMessagePassing.writeEvent write = event) ∨
  (∃ op, ReadPresent machine op ∧ AtomicMessagePassing.readEvent op = event)

/-- Only present successful records induce these edges. Issue order is not HB. -/
inductive PrefixHB (machine : Machine) (mode : AtomicMessagePassing.Mode) : AtomicMessagePassing.Event → AtomicMessagePassing.Event → Prop where
  | initialization (initial runtime : AtomicMessagePassing.Event) :
      AtomicMessagePassing.IsInitial initial → EventPresent machine initial →
      AtomicMessagePassing.IsRuntime runtime → EventPresent machine runtime →
      PrefixHB machine mode initial runtime
  | producer : WritePresent machine .dataStore → WritePresent machine .flagStore →
      PrefixHB machine mode .d .f
  | consumer : ReadPresent machine .flag → ReadPresent machine .data →
      PrefixHB machine mode .a .b
  | synchronizes (record : ReadRecord) :
      mode = .releaseAcquire → ReadAt machine .flag record →
      record.supplier = .flagStore → WritePresent machine .flagStore →
      PrefixHB machine mode .f .a
  | trans {first middle last : AtomicMessagePassing.Event} :
      PrefixHB machine mode first middle → PrefixHB machine mode middle last →
      PrefixHB machine mode first last

def PrefixMO (machine : Machine) (first second : AtomicMessagePassing.Write) : Prop :=
  WritePresent machine first ∧ WritePresent machine second ∧ AtomicMessagePassing.MO first second

def PrefixWriteWrite (machine : Machine) (mode : AtomicMessagePassing.Mode) : Prop :=
  ∀ first second firstLocation secondLocation,
    WriteAt machine first firstLocation → WriteAt machine second secondLocation →
    firstLocation = secondLocation →
    PrefixHB machine mode (AtomicMessagePassing.writeEvent first) (AtomicMessagePassing.writeEvent second) →
    PrefixMO machine first second

def PrefixReadRead (machine : Machine) (mode : AtomicMessagePassing.Mode) : Prop :=
  ∀ first second firstRecord secondRecord,
    ReadAt machine first firstRecord → ReadAt machine second secondRecord →
    firstRecord.location = secondRecord.location →
    PrefixHB machine mode (AtomicMessagePassing.readEvent first) (AtomicMessagePassing.readEvent second) →
    firstRecord.supplier = secondRecord.supplier ∨
      PrefixMO machine firstRecord.supplier secondRecord.supplier

def PrefixReadWrite (machine : Machine) (mode : AtomicMessagePassing.Mode) : Prop :=
  ∀ op record write location,
    ReadAt machine op record → WriteAt machine write location →
    record.location = location →
    PrefixHB machine mode (AtomicMessagePassing.readEvent op) (AtomicMessagePassing.writeEvent write) →
    PrefixMO machine record.supplier write

def PrefixWriteRead (machine : Machine) (mode : AtomicMessagePassing.Mode) : Prop :=
  ∀ write location op record,
    WriteAt machine write location → ReadAt machine op record →
    location = record.location →
    PrefixHB machine mode (AtomicMessagePassing.writeEvent write) (AtomicMessagePassing.readEvent op) →
    write = record.supplier ∨ PrefixMO machine write record.supplier

structure PrefixRules (machine : Machine) (mode : AtomicMessagePassing.Mode) : Prop where
  suppliers : ∀ op record, ReadAt machine op record →
    WriteAt machine record.supplier record.location
  atomicRead : ∀ op record, ReadAt machine op record →
    ¬ PrefixHB machine mode (AtomicMessagePassing.readEvent op) (AtomicMessagePassing.writeEvent record.supplier)
  acyclic : ∀ event, ¬ PrefixHB machine mode event event
  writeWrite : PrefixWriteWrite machine mode
  readRead : PrefixReadRead machine mode
  readWrite : PrefixReadWrite machine mode
  writeRead : PrefixWriteRead machine mode

def spanOf (checked : MiniRustReference.CheckedSpan) : AtomicMessagePassing.Span := ⟨checked.id, checked.offset, 2⟩

def commitStore (before : Machine) (input : Input) (op : StoreOp)
    (changed : MiniRustReference.State) (location : AtomicMessagePassing.Span) : Machine :=
  { before with
    raw := changed
    producer := match op with | .d => .f | .f => .done
    trace := before.trace ++
      [⟨.store op, handle input (.store op), .stored location (storeWrite op)⟩]
    writes := before.writes ++ [⟨storeWrite op, location⟩] }

def commitRead (before : Machine) (input : Input) (op : AtomicMessagePassing.Read)
    (record : ReadRecord) : Machine :=
  { before with
    consumer := match op with
      | .flag => if readValue record = 1 then .b else .skipped
      | .data => .done
    trace := before.trace ++ [⟨.read op, handle input (.read op), .loaded op record⟩]
    flagRead := match op with | .flag => some record | .data => before.flagRead
    dataRead := match op with | .flag => before.dataRead | .data => some record }

/-- Eligibility is checked before adding this read; constraints use the actual
tentative prefix. There is no record or constraint for a future B. -/
def ReadGuard (before : Machine) (input : Input) (op : AtomicMessagePassing.Read)
    (record : ReadRecord) : Prop :=
  WriteAt before record.supplier record.location ∧
    PrefixRules (commitRead before input op record) input.mode

def fault (before : Machine) (input : Input) (instruction : Instruction)
    (outcome : AttemptOutcome) : Machine :=
  { before with trace := before.trace ++ [⟨instruction, handle input instruction, outcome⟩] }

def RawUB (input : Input) (before : Machine) (instruction : Instruction)
    (diagnostic : MiniRustReference.UB) : Prop :=
  match instruction with
  | .store _ => MiniRustReference.store before.raw (handle input instruction).pointer AtomicMessagePassing.oneBytes 2 = .ub diagnostic
  | .read _ => MiniRustReference.load before.raw (handle input instruction).pointer 2 2 = .ub diagnostic

def RawUnsupported (input : Input) (before : Machine) (instruction : Instruction) : Prop :=
  match instruction with
  | .store _ => MiniRustReference.store before.raw (handle input instruction).pointer AtomicMessagePassing.oneBytes 2 = .unsupported
  | .read _ => MiniRustReference.load before.raw (handle input instruction).pointer 2 2 = .unsupported

def RawNoChoice (input : Input) (before : Machine) (instruction : Instruction) : Prop :=
  match instruction with
  | .store _ => MiniRustReference.store before.raw (handle input instruction).pointer AtomicMessagePassing.oneBytes 2 = .noChoice
  | .read _ => MiniRustReference.load before.raw (handle input instruction).pointer 2 2 = .noChoice

inductive Action where
  | issue (instruction : Instruction) | finish
  deriving DecidableEq, Repr

/-- The checked span in a successful store is a certificate, not a guard that
may discard success: store_success_checked and scheduled_store_success below
derive it from every actual successful store, with no consistency premise. -/
inductive ActionStep (input : Input) : Action → Config → Config → Prop where
  | store {before : Machine} {op : StoreOp} {changed : MiniRustReference.State} {checked : MiniRustReference.CheckedSpan} :
      Scheduled before (.store op) →
      MiniRustReference.store before.raw (handle input (.store op)).pointer AtomicMessagePassing.oneBytes 2 = .ok changed →
      MiniRustReference.checkPtr before.raw (handle input (.store op)).pointer 2 = .ok (some checked) →
      ActionStep input (.issue (.store op)) (.running before)
        (.running (commitStore before input op changed (spanOf checked)))
  | read {before : Machine} {op : AtomicMessagePassing.Read} {bytes : List MiniRustReference.Byte}
      {checked : MiniRustReference.CheckedSpan} {supplier : AtomicMessagePassing.Write} :
      Scheduled before (.read op) →
      MiniRustReference.load before.raw (handle input (.read op)).pointer 2 2 = .ok (bytes, before.raw) →
      MiniRustReference.checkPtr before.raw (handle input (.read op)).pointer 2 = .ok (some checked) →
      ReadGuard before input op ⟨spanOf checked, supplier, bytes⟩ →
      ActionStep input (.issue (.read op)) (.running before)
        (.running (commitRead before input op ⟨spanOf checked, supplier, bytes⟩))
  | ub {before : Machine} {instruction : Instruction} {diagnostic : MiniRustReference.UB} :
      Scheduled before instruction → RawUB input before instruction diagnostic →
      ActionStep input (.issue instruction) (.running before)
        (.ub instruction diagnostic (fault before input instruction (.ub diagnostic)))
  | unsupported {before : Machine} {instruction : Instruction} :
      Scheduled before instruction → RawUnsupported input before instruction →
      ActionStep input (.issue instruction) (.running before)
        (.unsupported instruction (fault before input instruction .unsupported))
  | finish {before : Machine} : Finished before →
      ActionStep input .finish (.running before) (.normal before)

def Step (input : Input) (before after : Config) : Prop :=
  ∃ action, ActionStep input action before after

def Terminal : Config → Prop
  | .running _ => False | _ => True

def Bad : Config → Prop
  | .ub _ _ _ => True | _ => False

theorem checkPtr_two_not_none (state : MiniRustReference.State) (pointer : MiniRustReference.Ptr) :
    MiniRustReference.checkPtr state pointer 2 ≠ .ok none := by
  intro checked
  cases provenance : pointer.provenance with
  | none => simp [MiniRustReference.checkPtr, provenance] at checked
  | some id =>
    cases found : state.allocations id with
    | none => simp [MiniRustReference.checkPtr, provenance, found] at checked
    | some allocation =>
      by_cases dead : allocation.live = false
      · simp [MiniRustReference.checkPtr, provenance, found, dead] at checked
      by_cases low : pointer.addr < allocation.base
      · simp [MiniRustReference.checkPtr, provenance, found, dead, low] at checked
      by_cases high : allocation.size < pointer.addr - allocation.base + 2
      · simp [MiniRustReference.checkPtr, provenance, found, dead, low, high] at checked
      · simp [MiniRustReference.checkPtr, provenance, found, dead, low, high] at checked

/-- This derives the store certificate from actual success for arbitrary raw
memory/pointer. No validity, geometry, WF or consistency admission is needed. -/
theorem store_success_checked {state changed : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    (stored : MiniRustReference.store state pointer AtomicMessagePassing.oneBytes 2 = .ok changed) :
    ∃ checked, MiniRustReference.checkPtr state pointer 2 = .ok (some checked) := by
  by_cases misaligned : pointer.addr % 2 ≠ 0
  · simp [MiniRustReference.store, misaligned] at stored
  cases checked : MiniRustReference.checkPtr state pointer 2 with
  | ub diagnostic => simp [MiniRustReference.store, AtomicMessagePassing.oneBytes, misaligned, checked] at stored
  | unsupported => simp [MiniRustReference.store, AtomicMessagePassing.oneBytes, misaligned, checked] at stored
  | noChoice => simp [MiniRustReference.store, AtomicMessagePassing.oneBytes, misaligned, checked] at stored
  | ok span =>
    cases span with
    | none => exact False.elim (checkPtr_two_not_none state pointer checked)
    | some span => exact ⟨span, rfl⟩

/-- Positive-size successful loads both resolve a real span and retain the
actual input raw state. Atomic values are not extracted by this theorem. -/
theorem load_success_checked {state after : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    {bytes : List MiniRustReference.Byte} (loaded : MiniRustReference.load state pointer 2 2 = .ok (bytes, after)) :
    after = state ∧ ∃ checked, MiniRustReference.checkPtr state pointer 2 = .ok (some checked) := by
  by_cases misaligned : pointer.addr % 2 ≠ 0
  · simp [MiniRustReference.load, misaligned] at loaded
  cases checked : MiniRustReference.checkPtr state pointer 2 with
  | ub diagnostic => simp [MiniRustReference.load, misaligned, checked] at loaded
  | unsupported => simp [MiniRustReference.load, misaligned, checked] at loaded
  | noChoice => simp [MiniRustReference.load, misaligned, checked] at loaded
  | ok span =>
    cases span with
    | none => exact False.elim (checkPtr_two_not_none state pointer checked)
    | some span =>
      simp only [MiniRustReference.load, ite_eq_right (by decide : ¬ (2 : Nat) = 0),
        ite_eq_right misaligned, checked] at loaded
      exact ⟨(congrArg Prod.snd (MiniRustReference.Result.ok.inj loaded)).symm, span, rfl⟩

/-- No additional successful-store guard exists: every scheduled actual raw
success has an operational successor containing its exact changed raw state. -/
theorem scheduled_store_success {input : Input} {before : Machine} {op : StoreOp}
    {changed : MiniRustReference.State} (scheduled : Scheduled before (.store op))
    (stored : MiniRustReference.store before.raw (handle input (.store op)).pointer AtomicMessagePassing.oneBytes 2 = .ok changed) :
    ∃ checked,
      MiniRustReference.checkPtr before.raw (handle input (.store op)).pointer 2 = .ok (some checked) ∧
      Step input (.running before)
        (.running (commitStore before input op changed (spanOf checked))) ∧
      (commitStore before input op changed (spanOf checked)).raw = changed := by
  obtain ⟨checked, located⟩ := store_success_checked stored
  exact ⟨checked, located,
    ⟨.issue (.store op), ActionStep.store scheduled stored located⟩, rfl⟩

theorem store_step_threads_raw {input : Input} {before after : Machine} {op : StoreOp}
    (edge : ActionStep input (.issue (.store op)) (.running before) (.running after)) :
    MiniRustReference.store before.raw (handle input (.store op)).pointer AtomicMessagePassing.oneBytes 2 = .ok after.raw := by
  cases edge
  assumption

/-- Forward reflection and converse inversion of ordinary UB, with the exact
residual. No RF choice, PrefixRules or future completion occurs here. -/
theorem ub_step_iff (input : Input) (before : Machine) (instruction : Instruction)
    (diagnostic : MiniRustReference.UB) (after : Machine) :
    Step input (.running before) (.ub instruction diagnostic after) ↔
      Scheduled before instruction ∧ RawUB input before instruction diagnostic ∧
        after = fault before input instruction (.ub diagnostic) := by
  constructor
  · rintro ⟨action, edge⟩
    cases edge
    exact ⟨by assumption, by assumption, rfl⟩
  · rintro ⟨scheduled, failed, rfl⟩
    exact ⟨.issue instruction, ActionStep.ub scheduled failed⟩

theorem unsupported_step_iff (input : Input) (before : Machine)
    (instruction : Instruction) (after : Machine) :
    Step input (.running before) (.unsupported instruction after) ↔
      Scheduled before instruction ∧ RawUnsupported input before instruction ∧
        after = fault before input instruction .unsupported := by
  constructor
  · rintro ⟨action, edge⟩
    cases edge
    exact ⟨by assumption, by assumption, rfl⟩
  · rintro ⟨scheduled, failed, rfl⟩
    exact ⟨.issue instruction, ActionStep.unsupported scheduled failed⟩

/-- Rejection of this instruction contributes no issue transition. Another
thread is not excluded by this statement. -/
theorem noChoice_no_issue {input : Input} {before : Machine} {instruction : Instruction}
    {after : Config} (rejected : RawNoChoice input before instruction) :
    ¬ ActionStep input (.issue instruction) (.running before) after := by
  intro edge
  cases instruction <;> cases edge <;>
    simp_all [RawNoChoice, RawUB, RawUnsupported]

theorem terminal_no_step {input : Input} {before after : Config}
    (terminal : Terminal before) : ¬ Step input before after := by
  rintro ⟨action, edge⟩
  cases edge <;> cases terminal

/-- All prior effects and records remain; only the failed attempt is appended. -/
theorem fault_residual (before : Machine) (input : Input) (instruction : Instruction)
    (outcome : AttemptOutcome) :
    (fault before input instruction outcome).raw = before.raw ∧
    (fault before input instruction outcome).producer = before.producer ∧
    (fault before input instruction outcome).consumer = before.consumer ∧
    (fault before input instruction outcome).writes = before.writes ∧
    (fault before input instruction outcome).flagRead = before.flagRead ∧
    (fault before input instruction outcome).dataRead = before.dataRead ∧
    (fault before input instruction outcome).trace =
      before.trace ++ [⟨instruction, handle input instruction, outcome⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem read_value_binary (record : ReadRecord) :
    readValue record = 0 ∨ readValue record = 1 := by
  cases chosen : record.supplier <;> simp [readValue, chosen, AtomicMessagePassing.writeValue]

def healthyInput (mode : AtomicMessagePassing.Mode) : Input :=
  ⟨mode, .healthy, .healthy, .healthy, .healthy, 0, 1, 2, 3⟩

def badDInput (mode : AtomicMessagePassing.Mode) : Input :=
  { healthyInput mode with d := .noProvenance }

def badDTerminal (mode : AtomicMessagePassing.Mode) : Config :=
  .ub (.store .d) .noProvenance
    (fault initialMachine (badDInput mode) (.store .d) (.ub .noProvenance))

theorem badD_first (mode : AtomicMessagePassing.Mode) :
    Execution.Reach (Step (badDInput mode)) root (badDTerminal mode) ∧
    (observe (badDTerminal mode)).status = .ub .d .noProvenance ∧
    (observe (badDTerminal mode)).raw = AtomicMessagePassingControls.initial ∧
    (observe (badDTerminal mode)).flagRead = none ∧
    (observe (badDTerminal mode)).dataRead = none ∧
    (observe (badDTerminal mode)).trace =
      [⟨.store .d, handle (badDInput mode) (.store .d), .ub .noProvenance⟩] ∧
    Terminal (badDTerminal mode) := by
  have scheduled : Scheduled initialMachine (.store .d) := rfl
  have failed : RawUB (badDInput mode) initialMachine (.store .d) .noProvenance := by
    simpa only [RawUB, initialMachine, handle, badDInput, basePointer, operand, choosePointer] using
      (show MiniRustReference.store AtomicMessagePassingControls.initial
        { AtomicMessagePassingControls.dataPointer with provenance := none }
        AtomicMessagePassing.oneBytes 2 = .ub .noProvenance from rfl)
  have edge : Step (badDInput mode) root (badDTerminal mode) :=
    ⟨.issue (.store .d), ActionStep.ub scheduled failed⟩
  exact ⟨Execution.Reach.tail (Execution.Reach.refl _) edge,
    rfl, rfl, rfl, rfl, rfl, True.intro⟩

theorem badD_not_noUB (mode : AtomicMessagePassing.Mode) :
    ¬ Execution.NoUB (Step (badDInput mode)) Bad root :=
  Execution.bad_prefix_not_noUB (badD_first mode).1 True.intro

/-- Independently specified in the raw kernel's exact update form. -/
def writtenDataBlock : MiniRustReference.Allocation :=
  let allocation := AtomicMessagePassingControls.block 16 true
  let writtenData : Nat → MiniRustReference.Byte := fun index =>
    if 0 ≤ index ∧ index < 0 + AtomicMessagePassing.oneBytes.length then
      AtomicMessagePassing.oneBytes.getD (index - 0) .uninit
    else allocation.data index
  { allocation with data := writtenData }

def afterDMemory : MiniRustReference.State := MiniRustReference.replace AtomicMessagePassingControls.initial 0 writtenDataBlock

def afterDMachine (mode : AtomicMessagePassing.Mode) : Machine :=
  commitStore initialMachine (healthyInput mode) .d afterDMemory AtomicMessagePassingControls.dataSpan

def rawByte (state : MiniRustReference.State) (id offset : Nat) : Option MiniRustReference.Byte :=
  (state.allocations id).map (fun allocation => allocation.data offset)

/-- Actual D changes current memory and the operational successor commits it.
Both read observations are raw kernel calls, not RF-supplied values. -/
theorem healthyD_actual (mode : AtomicMessagePassing.Mode) :
    MiniRustReference.store AtomicMessagePassingControls.initial AtomicMessagePassingControls.dataPointer AtomicMessagePassing.oneBytes 2 = .ok afterDMemory ∧
    Step (healthyInput mode) root (.running (afterDMachine mode)) ∧
    MiniRustReference.load afterDMemory AtomicMessagePassingControls.dataPointer 2 2 = .ok (AtomicMessagePassing.oneBytes, afterDMemory) ∧
    MiniRustReference.load afterDMemory AtomicMessagePassingControls.flagPointer 2 2 = .ok (AtomicMessagePassingControls.zeroBytes, afterDMemory) ∧
    afterDMemory ≠ AtomicMessagePassingControls.initial := by
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · have scheduled : Scheduled initialMachine (.store .d) := rfl
    have stored : MiniRustReference.store initialMachine.raw
        (handle (healthyInput mode) (.store .d)).pointer AtomicMessagePassing.oneBytes 2 = .ok afterDMemory := by
      simpa only [initialMachine, handle, healthyInput, basePointer, operand, choosePointer] using
        (show MiniRustReference.store AtomicMessagePassingControls.initial
          AtomicMessagePassingControls.dataPointer AtomicMessagePassing.oneBytes 2 =
            .ok afterDMemory from rfl)
    have checked : MiniRustReference.checkPtr initialMachine.raw
        (handle (healthyInput mode) (.store .d)).pointer 2 =
          .ok (some ⟨0, AtomicMessagePassingControls.block 16 true, 0⟩) := rfl
    exact ⟨.issue (.store .d), ActionStep.store scheduled stored checked⟩
  · intro same
    have different : rawByte afterDMemory 0 0 ≠ rawByte AtomicMessagePassingControls.initial 0 0 := by decide
    exact different (congrArg (fun state => rawByte state 0 0) same)

/- The full-prefix graph invariant and completed soundness/coverage are later
stages. These audits cover only the raw/operational first checkpoint. -/
#print axioms checkPtr_two_not_none
#print axioms store_success_checked
#print axioms load_success_checked
#print axioms scheduled_store_success
#print axioms store_step_threads_raw
#print axioms ub_step_iff
#print axioms unsupported_step_iff
#print axioms noChoice_no_issue
#print axioms terminal_no_step
#print axioms fault_residual
#print axioms badD_first
#print axioms badD_not_noUB
#print axioms healthyD_actual

end AnnealResearch.AtomicPrefixExecution

