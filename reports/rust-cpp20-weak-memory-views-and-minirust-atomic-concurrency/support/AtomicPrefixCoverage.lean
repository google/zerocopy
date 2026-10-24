import AnnealResearch.AtomicPrefixRules

/-!
Completed-observer soundness, producer-first existential coverage, and rooted
branch history for the fixed owned atomic subject. Execution and its guard are
unchanged. Old full-graph theorems are reused after explicit graph/operand bridges;
they do not define new transitions. No general weak-memory adequacy is claimed.
-/
namespace AnnealResearch.AtomicPrefixCoverage

open AtomicPrefixExecution AtomicPrefixRules

def interpretedHandles (input : Input) : AtomicMessagePassing.Handles :=
  ⟨handle input (.store .d), handle input (.store .f),
    handle input (.read .flag), handle input (.read .data)⟩

def Healthy (input : Input) : Prop :=
  input.d = .healthy ∧ input.f = .healthy ∧ input.a = .healthy ∧ input.b = .healthy

theorem healthy_operand {input : Input} (healthy : Healthy input) (instruction : Instruction) :
    operand input instruction = .healthy := by
  cases instruction with
  | store op =>
    cases op with
    | d => exact healthy.1
    | f => exact healthy.2.1
  | read op =>
    cases op with
    | flag => exact healthy.2.2.1
    | data => exact healthy.2.2.2

theorem healthy_pointer {input : Input} (healthy : Healthy input) (instruction : Instruction) :
    (handle input instruction).pointer = basePointer instruction := by
  simp only [handle, healthy_operand healthy instruction, choosePointer]

theorem initial_writeGate (input : Input) (op : StoreOp) :
    AtomicMessagePassing.writeGate AtomicMessagePassingControls.initial (handle input (.store op)) =
      match operand input (.store op) with
      | .healthy => .ok (designated (.store op))
      | .noProvenance => .ub .noProvenance
      | .misaligned => .ub .misalignedStore := by
  cases op with
  | d =>
    cases chosen : input.d <;>
      simp [AtomicMessagePassing.writeGate, AtomicMessagePassing.checkedLocation,
        handle, operand, basePointer, choosePointer, chosen, designated,
        MiniRustReference.store, MiniRustReference.checkPtr,
        AtomicMessagePassing.oneBytes, AtomicMessagePassingControls.initial,
        AtomicMessagePassingControls.raw, AtomicMessagePassingControls.block,
        AtomicMessagePassingControls.dataPointer, AtomicMessagePassingControls.dataSpan]
  | f =>
    cases chosen : input.f <;>
      simp [AtomicMessagePassing.writeGate, AtomicMessagePassing.checkedLocation,
        handle, operand, basePointer, choosePointer, chosen, designated,
        MiniRustReference.store, MiniRustReference.checkPtr,
        AtomicMessagePassing.oneBytes, AtomicMessagePassingControls.initial,
        AtomicMessagePassingControls.raw, AtomicMessagePassingControls.block,
        AtomicMessagePassingControls.flagPointer, AtomicMessagePassingControls.flagSpan]

theorem initial_readGate (input : Input) (op : AtomicMessagePassing.Read) :
    AtomicMessagePassing.readGate AtomicMessagePassingControls.initial (handle input (.read op)) =
      match operand input (.read op) with
      | .healthy => .ok (designated (.read op))
      | .noProvenance => .ub .noProvenance
      | .misaligned => .ub .misalignedLoad := by
  cases op with
  | flag =>
    cases chosen : input.a <;>
      simp [AtomicMessagePassing.readGate, AtomicMessagePassing.checkedLocation,
        handle, operand, basePointer, choosePointer, chosen, designated,
        MiniRustReference.load, MiniRustReference.checkPtr,
        AtomicMessagePassingControls.initial, AtomicMessagePassingControls.raw,
        AtomicMessagePassingControls.block, AtomicMessagePassingControls.flagPointer,
        AtomicMessagePassingControls.flagSpan]
  | data =>
    cases chosen : input.b <;>
      simp [AtomicMessagePassing.readGate, AtomicMessagePassing.checkedLocation,
        handle, operand, basePointer, choosePointer, chosen, designated,
        MiniRustReference.load, MiniRustReference.checkPtr,
        AtomicMessagePassingControls.initial, AtomicMessagePassingControls.raw,
        AtomicMessagePassingControls.block, AtomicMessagePassingControls.dataPointer,
        AtomicMessagePassingControls.dataSpan]

/-- Classifier gate success derives health, rather than assuming it as entry
admission. Labels are arbitrary and never used as location identities. -/
theorem initial_gates_ok {input : Input} {locations : AtomicMessagePassing.Locations}
    (checked : AtomicMessagePassing.gates AtomicMessagePassingControls.initial
      (interpretedHandles input) = .ok locations) :
    Healthy input ∧ locations = AtomicMessagePassingControls.locations := by
  simp only [AtomicMessagePassing.gates, interpretedHandles, initial_writeGate,
    initial_readGate] at checked
  cases d : input.d with
  | noProvenance => simp [operand, d, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
  | misaligned => simp [operand, d, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
  | healthy =>
    cases f : input.f with
    | noProvenance => simp [operand, d, f, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
    | misaligned => simp [operand, d, f, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
    | healthy =>
      cases a : input.a with
      | noProvenance => simp [operand, d, f, a, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
      | misaligned => simp [operand, d, f, a, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
      | healthy =>
        cases b : input.b with
        | noProvenance => simp [operand, d, f, a, b, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
        | misaligned => simp [operand, d, f, a, b, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate] at checked
        | healthy =>
          refine ⟨⟨d, f, a, b⟩, ?_⟩
          have equal : AtomicMessagePassingControls.locations = locations := by
            simpa [operand, d, f, a, b, AtomicMessagePassing.atEvent,
              AtomicMessagePassing.bindGate, designated, AtomicMessagePassingControls.locations] using checked
          exact equal.symm

theorem initial_gates_healthy {input : Input} (healthy : Healthy input) :
    AtomicMessagePassing.gates AtomicMessagePassingControls.initial (interpretedHandles input) =
      .ok AtomicMessagePassingControls.locations := by
  rcases healthy with ⟨d, f, a, b⟩
  simp [AtomicMessagePassing.gates, interpretedHandles, initial_writeGate, initial_readGate,
    operand, d, f, a, b, AtomicMessagePassing.atEvent, AtomicMessagePassing.bindGate,
    designated, AtomicMessagePassingControls.locations]

structure CandidateProjection where
  locations : AtomicMessagePassing.Locations
  rf : AtomicMessagePassing.RF
  values : Nat × Nat
  deriving DecidableEq, Repr

/-- Partial lookup: no absent modification receives a synthetic location. -/
def writtenLocation : List WriteRecord → AtomicMessagePassing.Write → Option AtomicMessagePassing.Span
  | [], _ => none
  | record :: rest, write =>
    if record.write = write then some record.location else writtenLocation rest write

/-- Only a normal, actual A=1 configuration with both real store/read records
has a legacy projection. The full observer remains the one in Execution. -/
def project : Config → Option CandidateProjection
  | .normal machine =>
    match writtenLocation machine.writes .dataStore, writtenLocation machine.writes .flagStore,
        machine.flagRead, machine.dataRead with
    | some dataLocation, some flagLocation, some flag, some data =>
      if readValue flag = 1 then
        some ⟨⟨dataLocation, flagLocation, flag.location, data.location⟩,
          extractedRF flag data, (readValue flag, readValue data)⟩
      else none
    | _, _, _, _ => none
  | _ => none

theorem writtenLocation_complete {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    (write : AtomicMessagePassing.Write) :
    writtenLocation machine.writes write =
      some (AtomicMessagePassing.writeLocation AtomicMessagePassingControls.locations write) := by
  rw [shape.writes, complete.producer]
  cases write <;> rfl

theorem project_complete {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    (one : readValue flag = 1) :
    project (.normal machine) = some ⟨AtomicMessagePassingControls.locations,
      extractedRF flag data, AtomicMessagePassing.returned (extractedRF flag data)⟩ := by
  have flagLocation := shape.readLocations .flag flag complete.flag
  have dataLocation := shape.readLocations .data data complete.data
  simp only [project, writtenLocation_complete shape complete, complete.flag, complete.data]
  rw [ite_eq_left one]
  simp only [flagLocation, dataLocation, AtomicMessagePassing.writeLocation,
    AtomicMessagePassing.readLocation, AtomicMessagePassingControls.locations,
    AtomicMessagePassing.returned, AtomicMessagePassing.flagValue, AtomicMessagePassing.dataValue,
    extractedRF, readValue]

/-- Every actual normal A=1 prefix has an exact old indexed observation.
The comparison observes locations/RF values, not final raw memory or issue order. -/
theorem completed_sound {input : Input} {machine : Machine} {flag : ReadRecord}
    (path : Execution.Reach (Step input) root (.normal machine))
    (read : ReadAt machine .flag flag) (one : readValue flag = 1) :
    ∃ data, Complete machine flag data ∧
      project (.normal machine) = some ⟨AtomicMessagePassingControls.locations,
        extractedRF flag data, AtomicMessagePassing.returned (extractedRF flag data)⟩ ∧
      AtomicMessagePassing.runCandidate AtomicMessagePassingControls.initial
        (interpretedHandles input) input.mode (extractedRF flag data) =
          .observed AtomicMessagePassingControls.locations (AtomicMessagePassing.returned (extractedRF flag data)) := by
  obtain ⟨data, complete, rules, _hb, _mo, healthy⟩ := completed_flag_one_bridge path read one
  have shape := (root_prefix_invariant path).1
  exact ⟨data, complete, project_complete shape complete one,
    AtomicMessagePassing.run_candidate_observed _ _ _ _ _ one
      (initial_gates_healthy healthy) AtomicMessagePassingControls.selected_shape rules⟩

/-- The partial projection itself exposes the normal/A=1 domain. -/
theorem project_has_flag_one {config : Config} {projection : CandidateProjection}
    (projected : project config = some projection) :
    ∃ machine flag, config = .normal machine ∧ ReadAt machine .flag flag ∧ readValue flag = 1 := by
  cases config with
  | running machine => simp [project] at projected
  | ub instruction diagnostic machine => simp [project] at projected
  | unsupported instruction machine => simp [project] at projected
  | normal machine =>
    cases dataLoc : writtenLocation machine.writes .dataStore with
    | none => simp [project, dataLoc] at projected
    | some dataLocation =>
      cases flagLoc : writtenLocation machine.writes .flagStore with
      | none => simp [project, dataLoc, flagLoc] at projected
      | some flagLocation =>
        cases flagRead : machine.flagRead with
        | none => simp [project, dataLoc, flagLoc, flagRead] at projected
        | some flag =>
          cases dataRead : machine.dataRead with
          | none => simp [project, dataLoc, flagLoc, flagRead, dataRead] at projected
          | some data =>
            by_cases one : readValue flag = 1
            · exact ⟨machine, flag, rfl, flagRead, one⟩
            · simp [project, dataLoc, flagLoc, flagRead, dataRead, one] at projected

/-- Universal soundness for every actual defined partial projection. -/
theorem projected_sound {input : Input} {config : Config} {projection : CandidateProjection}
    (path : Execution.Reach (Step input) root config)
    (projected : project config = some projection) :
    AtomicMessagePassing.runCandidate AtomicMessagePassingControls.initial (interpretedHandles input)
      input.mode projection.rf = .observed projection.locations projection.values := by
  obtain ⟨machine, flag, rfl, read, one⟩ := project_has_flag_one projected
  obtain ⟨data, _complete, canonical, observed⟩ := completed_sound path read one
  have equal : (⟨AtomicMessagePassingControls.locations, extractedRF flag data,
      AtomicMessagePassing.returned (extractedRF flag data)⟩ : CandidateProjection) = projection :=
    Option.some.inj (canonical.symm.trans projected)
  cases equal
  exact observed

/-- Guard-free structural builder. The read's bytes are arbitrary, and its
supplier must actually be present at its resolved location. No circular guard. -/
theorem prepare_read {input : Input} {before : Machine} {op : AtomicMessagePassing.Read}
    {bytes : List MiniRustReference.Byte} {checked : MiniRustReference.CheckedSpan}
    {supplier : AtomicMessagePassing.Write} (shape : Structure input before)
    (scheduled : Scheduled before (.read op))
    (located : MiniRustReference.checkPtr before.raw (handle input (.read op)).pointer 2 = .ok (some checked))
    (supplied : WriteAt before supplier (spanOf checked)) :
    Structure input (commitRead before input op ⟨spanOf checked, supplier, bytes⟩) := by
  let record : ReadRecord := ⟨spanOf checked, supplier, bytes⟩
  obtain ⟨healthy, span⟩ := successful_span shape.layout located
  refine ⟨shape.layout, shape.writes, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases op with
    | flag =>
      have both : before.flagRead = none ∧ before.dataRead = none := by
        simpa only [ConsumerSlots, show before.consumer = .a from scheduled] using shape.slots
      change ConsumerSlots (commitRead before input .flag record)
      by_cases one : readValue record = 1
      · simp only [ConsumerSlots, commitRead, ite_eq_left one]
        exact ⟨⟨record, rfl, one⟩, both.2⟩
      · have zero : readValue record = 0 := (read_value_binary record).resolve_right one
        simp only [ConsumerSlots, commitRead, ite_eq_right one]
        exact ⟨⟨record, rfl, zero⟩, both.2⟩
    | data =>
      have both : (∃ flag, before.flagRead = some flag ∧ readValue flag = 1) ∧ before.dataRead = none := by
        simpa only [ConsumerSlots, show before.consumer = .b from scheduled] using shape.slots
      exact ⟨both.1, record, rfl⟩
  · intro write location member
    exact shape.writeLocations _ _ member
  · intro queried other read
    have split := (readAt_commitRead before input op queried record other).mp read
    by_cases same : queried = op
    · subst queried
      have equal : record = other := by simpa using split
      subst other
      cases op <;> simpa only [record, designated, AtomicMessagePassing.readLocation,
        AtomicMessagePassingControls.locations] using span
    · exact shape.readLocations _ _ (by simpa only [ite_eq_right same] using split)
  · intro queried other read
    have split := (readAt_commitRead before input op queried record other).mp read
    by_cases same : queried = op
    · subst queried
      have equal : record = other := by simpa using split
      subst other
      exact supplied
    · exact shape.suppliers _ _ (by simpa only [ite_eq_right same] using split)
  · intro queried present
    exact shape.storeHealthy _ present
  · intro queried other read
    have split := (readAt_commitRead before input op queried record other).mp read
    by_cases same : queried = op
    · subst queried
      exact healthy
    · exact shape.readHealthy _ _ (by simpa only [ite_eq_right same] using split)

theorem agrees_read {input : Input} {before : Machine} {op : AtomicMessagePassing.Read}
    {record : ReadRecord} {rf : AtomicMessagePassing.RF} (old : AgreesRF before rf)
    (chosen : record.supplier = AtomicMessagePassing.source rf op) :
    AgreesRF (commitRead before input op record) rf := by
  intro queried other read
  have split := (readAt_commitRead before input op queried record other).mp read
  by_cases same : queried = op
  · subst queried
    have equal : record = other := by simpa using split
    subst other
    exact chosen
  · exact old _ _ (by simpa only [ite_eq_right same] using split)

theorem guard_from_full {input : Input} {before : Machine} {op : AtomicMessagePassing.Read}
    {bytes : List MiniRustReference.Byte} {checked : MiniRustReference.CheckedSpan}
    {supplier : AtomicMessagePassing.Write} {rf : AtomicMessagePassing.RF}
    (shape : Structure input before) (scheduled : Scheduled before (.read op))
    (located : MiniRustReference.checkPtr before.raw (handle input (.read op)).pointer 2 = .ok (some checked))
    (supplied : WriteAt before supplier (spanOf checked)) (agrees : AgreesRF before rf)
    (chosen : supplier = AtomicMessagePassing.source rf op)
    (rules : AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations input.mode rf) :
    ReadGuard before input op ⟨spanOf checked, supplier, bytes⟩ :=
  ⟨supplied, rules_from_full (prepare_read shape scheduled located supplied)
    (agrees_read agrees chosen) rules⟩

/-- Exact current raw state after F. The existing accepted afterDMemory is
reused as the first actual store result; F's expected block is independently given. -/
def writtenFlagBlock : MiniRustReference.Allocation :=
  let allocation := AtomicMessagePassingControls.block 32 true
  let writtenData : Nat → MiniRustReference.Byte := fun index =>
    if 0 ≤ index ∧ index < 0 + AtomicMessagePassing.oneBytes.length then
      AtomicMessagePassing.oneBytes.getD (index - 0) .uninit
    else allocation.data index
  { allocation with data := writtenData }

def afterDFMemory : MiniRustReference.State := MiniRustReference.replace afterDMemory 1 writtenFlagBlock

def producerD (input : Input) : Machine :=
  commitStore initialMachine input .d afterDMemory AtomicMessagePassingControls.dataSpan

def producerDF (input : Input) : Machine :=
  commitStore (producerD input) input .f afterDFMemory AtomicMessagePassingControls.flagSpan

def flagRecord (rf : AtomicMessagePassing.RF) : ReadRecord :=
  ⟨AtomicMessagePassingControls.flagSpan, rf.flag, AtomicMessagePassing.oneBytes⟩

def dataRecord (rf : AtomicMessagePassing.RF) : ReadRecord :=
  ⟨AtomicMessagePassingControls.dataSpan, rf.data, AtomicMessagePassing.oneBytes⟩

def producerA (input : Input) (rf : AtomicMessagePassing.RF) : Machine :=
  commitRead (producerDF input) input .flag (flagRecord rf)

def producerAB (input : Input) (rf : AtomicMessagePassing.RF) : Machine :=
  commitRead (producerA input rf) input .data (dataRecord rf)

theorem afterDF_raw :
    MiniRustReference.store afterDMemory AtomicMessagePassingControls.flagPointer AtomicMessagePassing.oneBytes 2 = .ok afterDFMemory ∧
    MiniRustReference.load afterDFMemory AtomicMessagePassingControls.flagPointer 2 2 = .ok (AtomicMessagePassing.oneBytes, afterDFMemory) ∧
    MiniRustReference.load afterDFMemory AtomicMessagePassingControls.dataPointer 2 2 = .ok (AtomicMessagePassing.oneBytes, afterDFMemory) ∧
    rawByte afterDFMemory 0 0 = some (.init 1 none) ∧
    rawByte afterDFMemory 1 0 = some (.init 1 none) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem producer_steps {input : Input} (healthy : Healthy input) :
    Step input root (.running (producerD input)) ∧
    Step input (.running (producerD input)) (.running (producerDF input)) := by
  constructor
  · have stored : MiniRustReference.store initialMachine.raw
        (handle input (.store .d)).pointer AtomicMessagePassing.oneBytes 2 = .ok afterDMemory := by
      simpa only [initialMachine, healthy_pointer healthy, basePointer] using
        (show MiniRustReference.store AtomicMessagePassingControls.initial AtomicMessagePassingControls.dataPointer
          AtomicMessagePassing.oneBytes 2 = .ok afterDMemory from rfl)
    have checked : MiniRustReference.checkPtr initialMachine.raw
        (handle input (.store .d)).pointer 2 =
          .ok (some ⟨0, AtomicMessagePassingControls.block 16 true, 0⟩) := by
      simpa only [initialMachine, healthy_pointer healthy, basePointer] using
        (show MiniRustReference.checkPtr AtomicMessagePassingControls.initial AtomicMessagePassingControls.dataPointer 2 =
          .ok (some ⟨0, AtomicMessagePassingControls.block 16 true, 0⟩) from rfl)
    have scheduled : Scheduled initialMachine (.store .d) := rfl
    exact ⟨.issue (.store .d), ActionStep.store scheduled stored checked⟩
  · have stored : MiniRustReference.store (producerD input).raw
        (handle input (.store .f)).pointer AtomicMessagePassing.oneBytes 2 = .ok afterDFMemory := by
      simpa only [producerD, commitStore, healthy_pointer healthy, basePointer] using afterDF_raw.1
    have checked : MiniRustReference.checkPtr (producerD input).raw
        (handle input (.store .f)).pointer 2 = .ok (some ⟨1, AtomicMessagePassingControls.block 32 true, 0⟩) := by
      simpa only [producerD, commitStore, healthy_pointer healthy, basePointer] using
        (show MiniRustReference.checkPtr afterDMemory AtomicMessagePassingControls.flagPointer 2 =
          .ok (some ⟨1, AtomicMessagePassingControls.block 32 true, 0⟩) from rfl)
    have scheduled : Scheduled (producerD input) (.store .f) := rfl
    exact ⟨.issue (.store .f), ActionStep.store scheduled stored checked⟩

theorem producer_path {input : Input} (healthy : Healthy input) :
    Execution.Reach (Step input) root (.running (producerDF input)) :=
  Execution.Reach.tail (Execution.Reach.tail (Execution.Reach.refl _) (producer_steps healthy).1)
    (producer_steps healthy).2

theorem producer_all_writes (input : Input) (write : AtomicMessagePassing.Write) :
    WriteAt (producerDF input) write
      (AtomicMessagePassing.writeLocation AtomicMessagePassingControls.locations write) := by
  cases write <;> simp [WriteAt, producerDF, producerD, commitStore, initialMachine,
    storeWrite, AtomicMessagePassing.writeLocation, AtomicMessagePassingControls.locations]

theorem producer_agrees (input : Input) (rf : AtomicMessagePassing.RF) :
    AgreesRF (producerDF input) rf := by
  intro op record read
  cases op <;> simp [ReadAt, readRecord, producerDF, producerD, commitStore, initialMachine] at read

theorem producer_read_steps {input : Input} {rf : AtomicMessagePassing.RF}
    (healthy : Healthy input) (one : AtomicMessagePassing.flagValue rf = 1)
    (rules : AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations input.mode rf) :
    Step input (.running (producerDF input)) (.running (producerA input rf)) ∧
    Step input (.running (producerA input rf)) (.running (producerAB input rf)) := by
  have shape : Structure input (producerDF input) := (root_prefix_invariant (producer_path healthy)).1
  have aScheduled : Scheduled (producerDF input) (.read .flag) := rfl
  have aLoaded : MiniRustReference.load (producerDF input).raw (handle input (.read .flag)).pointer 2 2 =
      .ok (AtomicMessagePassing.oneBytes, (producerDF input).raw) := by
    simpa only [producerDF, commitStore, healthy_pointer healthy, basePointer] using afterDF_raw.2.1
  have aChecked : MiniRustReference.checkPtr (producerDF input).raw (handle input (.read .flag)).pointer 2 =
      .ok (some ⟨1, writtenFlagBlock, 0⟩) := by
    simpa only [producerDF, commitStore, healthy_pointer healthy, basePointer] using
      (show MiniRustReference.checkPtr afterDFMemory AtomicMessagePassingControls.flagPointer 2 =
        .ok (some ⟨1, writtenFlagBlock, 0⟩) from rfl)
  have aSupplied : WriteAt (producerDF input) rf.flag AtomicMessagePassingControls.flagSpan := by
    have present := producer_all_writes input rf.flag
    rw [rules.suppliers.flagLocation] at present
    change WriteAt (producerDF input) rf.flag AtomicMessagePassingControls.flagSpan at present
    exact present
  have aGuard : ReadGuard (producerDF input) input .flag (flagRecord rf) :=
    guard_from_full shape aScheduled aChecked aSupplied (producer_agrees input rf) rfl rules
  have aEdge : Step input (.running (producerDF input)) (.running (producerA input rf)) :=
    ⟨.issue (.read .flag), ActionStep.read aScheduled aLoaded aChecked aGuard⟩
  have aShape : Structure input (producerA input rf) := prepare_read shape aScheduled aChecked aSupplied
  have aAgrees : AgreesRF (producerA input rf) rf := agrees_read (producer_agrees input rf) rfl
  have bScheduled : Scheduled (producerA input rf) (.read .data) := by
    change (if AtomicMessagePassing.flagValue rf = 1 then ConsumerPC.b else ConsumerPC.skipped) = .b
    simp only [ite_eq_left one]
  have bLoaded : MiniRustReference.load (producerA input rf).raw (handle input (.read .data)).pointer 2 2 =
      .ok (AtomicMessagePassing.oneBytes, (producerA input rf).raw) := by
    simpa only [producerA, producerDF, commitRead, commitStore, healthy_pointer healthy, basePointer] using afterDF_raw.2.2.1
  have bChecked : MiniRustReference.checkPtr (producerA input rf).raw (handle input (.read .data)).pointer 2 =
      .ok (some ⟨0, writtenDataBlock, 0⟩) := by
    simpa only [producerA, producerDF, commitRead, commitStore, healthy_pointer healthy, basePointer] using
      (show MiniRustReference.checkPtr afterDFMemory AtomicMessagePassingControls.dataPointer 2 =
        .ok (some ⟨0, writtenDataBlock, 0⟩) from rfl)
  have bSupplied : WriteAt (producerA input rf) rf.data AtomicMessagePassingControls.dataSpan := by
    have present := producer_all_writes input rf.data
    rw [rules.suppliers.dataLocation] at present
    change WriteAt (producerDF input) rf.data AtomicMessagePassingControls.dataSpan at present
    exact present
  have bGuard : ReadGuard (producerA input rf) input .data (dataRecord rf) :=
    guard_from_full aShape bScheduled bChecked bSupplied aAgrees rfl rules
  exact ⟨aEdge, ⟨.issue (.read .data), ActionStep.read bScheduled bLoaded bChecked bGuard⟩⟩

/-- Actual D,F,A,B issue steps followed by the actual normal finish. This is
one existential schedule, not coverage of every execution/interleaving. -/
theorem producer_first_run {input : Input} {rf : AtomicMessagePassing.RF}
    (healthy : Healthy input) (one : AtomicMessagePassing.flagValue rf = 1)
    (rules : AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations input.mode rf) :
    Execution.Reach (Step input) root (.normal (producerAB input rf)) := by
  obtain ⟨aEdge, bEdge⟩ := producer_read_steps healthy one rules
  have finished : Finished (producerAB input rf) := ⟨rfl, Or.inr rfl⟩
  exact Execution.Reach.tail
    (Execution.Reach.tail (Execution.Reach.tail (producer_path healthy) aEdge) bEdge)
    ⟨.finish, ActionStep.finish finished⟩

/-- Definitional observations of the explicit witness shape. The accompanying
producer_first_run proves it is an actual run under its premises. There RF Idata
still binds atomic zero while raw B reads these one bytes. -/
theorem producer_first_observations (input : Input) (rf : AtomicMessagePassing.RF) :
    (producerAB input rf).raw = afterDFMemory ∧
    (producerAB input rf).flagRead = some (flagRecord rf) ∧
    (producerAB input rf).dataRead = some (dataRecord rf) ∧
    (flagRecord rf).rawBytes = AtomicMessagePassing.oneBytes ∧
    (dataRecord rf).rawBytes = AtomicMessagePassing.oneBytes ∧
    readValue (dataRecord rf) = AtomicMessagePassing.dataValue rf := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem old_observed_facts {input : Input} {rf : AtomicMessagePassing.RF}
    {locations : AtomicMessagePassing.Locations} {values : Nat × Nat}
    (observed : AtomicMessagePassing.runCandidate AtomicMessagePassingControls.initial
      (interpretedHandles input) input.mode rf = .observed locations values) :
    Healthy input ∧ locations = AtomicMessagePassingControls.locations ∧
      AtomicMessagePassing.flagValue rf = 1 ∧ rf.flag = .flagStore ∧
      AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations input.mode rf ∧
      values = AtomicMessagePassing.returned rf := by
  obtain ⟨one, checked, _oldShape, rules, valuesEq⟩ :=
    AtomicMessagePassingControls.observed_sound _ _ _ _ _ _ observed
  obtain ⟨healthy, locationsEq⟩ := initial_gates_ok checked
  subst locations
  exact ⟨healthy, rfl, one, AtomicMessagePassing.flag_one_supplier _
    AtomicMessagePassingControls.selected_shape rf rules.suppliers one, rules, valuesEq⟩

/-- Every actual old observed equation in the admitted handle family has an
explicit producer-first operational witness with exactly that partial projection.
Health, canonical locations and graph rules are derived from the observation. -/
theorem old_observed_covered {input : Input} {rf : AtomicMessagePassing.RF}
    {locations : AtomicMessagePassing.Locations} {values : Nat × Nat}
    (observed : AtomicMessagePassing.runCandidate AtomicMessagePassingControls.initial
      (interpretedHandles input) input.mode rf = .observed locations values) :
    ∃ machine, Execution.Reach (Step input) root (.normal machine) ∧
      project (.normal machine) = some ⟨locations, rf, values⟩ ∧
      machine = producerAB input rf ∧ machine.raw = afterDFMemory := by
  obtain ⟨healthy, locationsEq, one, _flagSupplier, rules, valuesEq⟩ := old_observed_facts observed
  subst locations
  have path := producer_first_run healthy one rules
  have shape : Structure input (producerAB input rf) := (root_prefix_invariant path).1
  have complete : Complete (producerAB input rf) (flagRecord rf) (dataRecord rf) := ⟨rfl, rfl, rfl⟩
  have projected := project_complete shape complete one
  have result : project (.normal (producerAB input rf)) =
      some ⟨AtomicMessagePassingControls.locations, rf, values⟩ := by
    simpa only [flagRecord, dataRecord, extractedRF, valuesEq] using projected
  exact ⟨producerAB input rf, path, result, rfl, rfl⟩

/-- The RA value consequence is derived after the graph bridge. It is not an
RA-specific operational guard or an all-input safety/termination theorem. -/
theorem ra_completed_values {input : Input} {machine : Machine} {flag : ReadRecord}
    (mode : input.mode = .releaseAcquire)
    (path : Execution.Reach (Step input) root (.normal machine))
    (read : ReadAt machine .flag flag) (one : readValue flag = 1) :
    ∃ data, machine.dataRead = some data ∧ (readValue flag, readValue data) = (1, 1) := by
  obtain ⟨data, complete, rules, _hb, _mo, _healthy⟩ := completed_flag_one_bridge path read one
  have raRules : AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations
      .releaseAcquire (extractedRF flag data) := mode ▸ rules
  have dataOne := AtomicMessagePassing.ra_flag_one_data_one _ AtomicMessagePassingControls.selected_shape
    (extractedRF flag data) raRules one
  exact ⟨data, complete.data, Prod.ext one dataOne⟩

/-- Every B attempt, including a failed one, entails current recorded A=1.
This is a trace-membership/current-slot implication, not a trace-position order
statement; its append proof uses the prior A=1 slot at an actual B attempt. -/
def BHistory (machine : Machine) : Prop :=
  ∀ attempt, attempt ∈ machine.trace → attempt.instruction = .read .data →
    ∃ flag, machine.flagRead = some flag ∧ readValue flag = 1

theorem b_scheduled_flag {input : Input} {machine : Machine}
    (shape : Structure input machine) (scheduled : Scheduled machine (.read .data)) :
    ∃ flag, machine.flagRead = some flag ∧ readValue flag = 1 := by
  have both : (∃ flag, machine.flagRead = some flag ∧ readValue flag = 1) ∧ machine.dataRead = none := by
    simpa only [ConsumerSlots, show machine.consumer = .b from scheduled] using shape.slots
  exact both.1

theorem bHistory_store {input : Input} {before : Machine} {op : StoreOp}
    {changed : MiniRustReference.State} {location : AtomicMessagePassing.Span}
    (history : BHistory before) : BHistory (commitStore before input op changed location) := by
  intro attempt member isB
  rcases List.mem_append.mp member with old | new
  · exact history attempt old isB
  · have equal : attempt = ⟨.store op, handle input (.store op), .stored location (storeWrite op)⟩ :=
      List.mem_singleton.mp new
    cases equal
    cases isB

theorem bHistory_read {input : Input} {before : Machine} {op : AtomicMessagePassing.Read}
    {record : ReadRecord} (shape : Structure input before) (history : BHistory before)
    (scheduled : Scheduled before (.read op)) : BHistory (commitRead before input op record) := by
  intro attempt member isB
  rcases List.mem_append.mp member with old | new
  · cases op with
    | flag =>
      have empty : before.flagRead = none := scheduled_read_empty shape scheduled
      obtain ⟨flag, read, _one⟩ := history attempt old isB
      simp [empty] at read
    | data => exact history attempt old isB
  · have equal : attempt = ⟨.read op, handle input (.read op), .loaded op record⟩ :=
      List.mem_singleton.mp new
    cases equal
    cases op with
    | flag => cases isB
    | data =>
      have prior : ∃ flag, before.flagRead = some flag ∧ readValue flag = 1 :=
        b_scheduled_flag (machine := before) shape scheduled
      exact prior

theorem bHistory_fault {input : Input} {before : Machine} {instruction : Instruction}
    {outcome : AttemptOutcome} (shape : Structure input before) (history : BHistory before)
    (scheduled : Scheduled before instruction) : BHistory (fault before input instruction outcome) := by
  intro attempt member isB
  rcases List.mem_append.mp member with old | new
  · exact history attempt old isB
  · have equal : attempt = ⟨instruction, handle input instruction, outcome⟩ := List.mem_singleton.mp new
    cases equal
    have instructionEq : instruction = .read .data := isB
    subst instruction
    have prior : ∃ flag, before.flagRead = some flag ∧ readValue flag = 1 :=
      b_scheduled_flag (machine := before) shape scheduled
    exact prior

def TraceInvariant (input : Input) (config : Config) : Prop :=
  ConfigInvariant input config ∧ BHistory (machineOf config)

theorem trace_step {input : Input} {before after : Config}
    (invariant : TraceInvariant input before) (edge : Step input before after) :
    TraceInvariant input after := by
  have nextInvariant := invariant_step invariant.1 edge
  refine ⟨nextInvariant, ?_⟩
  obtain ⟨action, acted⟩ := edge
  cases acted with
  | store scheduled stored located => exact bHistory_store invariant.2
  | read scheduled loaded located guard => exact bHistory_read invariant.1.1 invariant.2 scheduled
  | ub scheduled failed => exact bHistory_fault invariant.1.1 invariant.2 scheduled
  | unsupported scheduled failed => exact bHistory_fault invariant.1.1 invariant.2 scheduled
  | finish finished => exact invariant.2

theorem root_trace_history {input : Input} {config : Config}
    (path : Execution.Reach (Step input) root config) : BHistory (machineOf config) := by
  have initialHistory : BHistory initialMachine := by
    intro attempt member _
    cases member
  have invariant : TraceInvariant input config := Execution.invariant_reachable
    (show TraceInvariant input root from
      ⟨⟨initial_structure input, initial_coherent input, True.intro⟩, initialHistory⟩)
    (fun invariant edge => trace_step invariant edge) path
  exact invariant.2

/-- Root-derived A=0 leaves B absent as value/RF/success AND as every attempted
instruction, including a potential raw failure. No future completion is required. -/
theorem root_flag_zero_no_B {input : Input} {config : Config} {flag : ReadRecord}
    (path : Execution.Reach (Step input) root config)
    (read : ReadAt (machineOf config) .flag flag) (zero : readValue flag = 0) :
    (machineOf config).consumer = .skipped ∧ (machineOf config).dataRead = none ∧
      (∀ record, ¬ ReadAt (machineOf config) .data record) ∧
      (∀ attempt, attempt ∈ (machineOf config).trace → attempt.instruction ≠ .read .data) := by
  let machine := machineOf config
  change ReadAt machine .flag flag at read
  have shape : Structure input machine := (root_prefix_invariant path).1
  have history : BHistory machine := root_trace_history path
  have skipped : machine.consumer = .skipped := by
    have slots := shape.slots
    cases pc : machine.consumer with
    | a =>
      have both : machine.flagRead = none ∧ machine.dataRead = none := by
        simpa only [ConsumerSlots, pc] using slots
      simp [ReadAt, readRecord, both.1] at read
    | b =>
      have both : (∃ other, machine.flagRead = some other ∧ readValue other = 1) ∧ machine.dataRead = none := by
        simpa only [ConsumerSlots, pc] using slots
      obtain ⟨other, otherRead, one⟩ := both.1
      have equal : other = flag := Option.some.inj (otherRead.symm.trans read)
      subst other
      omega
    | skipped => rfl
    | done =>
      have both : (∃ other, machine.flagRead = some other ∧ readValue other = 1) ∧
          (∃ other, machine.dataRead = some other) := by
        simpa only [ConsumerSlots, pc] using slots
      obtain ⟨other, otherRead, one⟩ := both.1
      have equal : other = flag := Option.some.inj (otherRead.symm.trans read)
      subst other
      omega
  have both : (∃ other, machine.flagRead = some other ∧ readValue other = 0) ∧ machine.dataRead = none := by
    simpa only [ConsumerSlots, skipped] using shape.slots
  refine ⟨skipped, both.2, ?_, ?_⟩
  · intro record present
    change machine.dataRead = some record at present
    simp [both.2] at present
  · intro attempt member isB
    obtain ⟨other, otherRead, one⟩ := history attempt member isB
    have equal : other = flag := Option.some.inj (otherRead.symm.trans read)
    subst other
    omega

#print axioms initial_gates_ok
#print axioms project_complete
#print axioms completed_sound
#print axioms projected_sound
#print axioms prepare_read
#print axioms guard_from_full
#print axioms afterDF_raw
#print axioms producer_read_steps
#print axioms producer_first_run
#print axioms producer_first_observations
#print axioms old_observed_facts
#print axioms old_observed_covered
#print axioms ra_completed_values
#print axioms root_trace_history
#print axioms root_flag_zero_no_B

end AnnealResearch.AtomicPrefixCoverage
