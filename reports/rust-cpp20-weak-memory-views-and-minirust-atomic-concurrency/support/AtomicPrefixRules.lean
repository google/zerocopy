import AnnealResearch.AtomicPrefixExecution

/-!
Rooted structure and graph obligations for the owned finite atomic subject.
The execution relation is imported unchanged. Full-graph theorems below are
proof aids, never store guards, root admissions, or future-completion tests.
Raw layout forgets byte data; successful stores retain their actual new data.
-/
namespace AnnealResearch.AtomicPrefixRules

open AtomicPrefixExecution

structure AllocationInfo where
  base : Nat
  size : Nat
  align : Nat
  kind : MiniRustReference.Kind
  live : Bool
  deriving DecidableEq

def info (allocation : MiniRustReference.Allocation) : AllocationInfo :=
  ⟨allocation.base, allocation.size, allocation.align, allocation.kind, allocation.live⟩

def infoAt (state : MiniRustReference.State) (id : Nat) : Option AllocationInfo :=
  (state.allocations id).map info

structure RawLayout (state : MiniRustReference.State) : Prop where
  next : state.next = AtomicMessagePassingControls.initial.next
  allocations : ∀ id, infoAt state id = infoAt AtomicMessagePassingControls.initial id

/-- Actual positive-size checking identifies the record it used. -/
theorem checked_lookup {state : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    {checked : MiniRustReference.CheckedSpan}
    (located : MiniRustReference.checkPtr state pointer 2 = .ok (some checked)) :
    state.allocations checked.id = some checked.allocation := by
  cases provenance : pointer.provenance with
  | none => simp [MiniRustReference.checkPtr, provenance] at located
  | some id =>
    cases found : state.allocations id with
    | none => simp [MiniRustReference.checkPtr, provenance, found] at located
    | some allocation =>
      by_cases dead : allocation.live = false
      · simp [MiniRustReference.checkPtr, provenance, found, dead] at located
      by_cases low : pointer.addr < allocation.base
      · simp [MiniRustReference.checkPtr, provenance, found, dead, low] at located
      by_cases high : allocation.size < pointer.addr - allocation.base + 2
      · simp [MiniRustReference.checkPtr, provenance, found, dead, low, high] at located
      · have same : (⟨id, allocation, pointer.addr - allocation.base⟩ :
            MiniRustReference.CheckedSpan) = checked := by
          simpa [MiniRustReference.checkPtr, provenance, found, dead, low, high] using located
        cases same
        exact found

/-- No WF/safety admission: this is the exact data-only update of actual store. -/
theorem store_preserves_info {state changed : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    (stored : MiniRustReference.store state pointer AtomicMessagePassing.oneBytes 2 = .ok changed) :
    changed.next = state.next ∧ ∀ id, infoAt changed id = infoAt state id := by
  obtain ⟨checked, located⟩ := store_success_checked stored
  have found := checked_lookup located
  by_cases misaligned : pointer.addr % 2 ≠ 0
  · simp [MiniRustReference.store, misaligned] at stored
  simp only [MiniRustReference.store, AtomicMessagePassing.oneBytes, List.length_cons,
    List.length_nil, Nat.reduceAdd, ite_eq_right (by decide : ¬ (2 : Nat) = 0),
    ite_eq_right misaligned, located] at stored
  cases MiniRustReference.Result.ok.inj stored
  constructor
  · rfl
  · intro id
    by_cases same : id = checked.id
    · subst id
      simp [infoAt, MiniRustReference.replace, found, info]
    · simp [infoAt, MiniRustReference.replace, same]

theorem rawLayout_store {state changed : MiniRustReference.State} {pointer : MiniRustReference.Ptr}
    (layout : RawLayout state)
    (stored : MiniRustReference.store state pointer AtomicMessagePassing.oneBytes 2 = .ok changed) :
    RawLayout changed := by
  obtain ⟨sameNext, sameInfo⟩ := store_preserves_info stored
  exact ⟨sameNext.trans layout.next, fun id => (sameInfo id).trans (layout.allocations id)⟩

theorem layout_record {state : MiniRustReference.State} (layout : RawLayout state)
    (id base : Nat)
    (initial : AtomicMessagePassingControls.initial.allocations id =
      some (AtomicMessagePassingControls.block base true)) :
    ∃ allocation, state.allocations id = some allocation ∧
      info allocation = info (AtomicMessagePassingControls.block base true) := by
  have metadata := layout.allocations id
  cases found : state.allocations id with
  | none => simp [infoAt, found, initial] at metadata
  | some allocation =>
    refine ⟨allocation, rfl, ?_⟩
    simpa only [infoAt, found, initial, Option.map_some, Option.some.injEq] using metadata

/-- The selected operand family can succeed only at its designated full span.
Misaligned operands also exceed this two-byte allocation; no span is invented. -/
theorem check_choice_span {state : MiniRustReference.State} {allocation : MiniRustReference.Allocation}
    {id base : Nat} {choice : Operand} {checked : MiniRustReference.CheckedSpan}
    (found : state.allocations id = some allocation)
    (metadata : info allocation = info (AtomicMessagePassingControls.block base true))
    (located : MiniRustReference.checkPtr state (choosePointer ⟨base, some id⟩ choice) 2 =
      .ok (some checked)) :
    choice = .healthy ∧ spanOf checked = ⟨id, 0, 2⟩ := by
  have baseEq : allocation.base = base := congrArg AllocationInfo.base metadata
  have sizeEq : allocation.size = 2 := congrArg AllocationInfo.size metadata
  have liveEq : allocation.live = true := congrArg AllocationInfo.live metadata
  cases choice with
  | noProvenance => simp [choosePointer, MiniRustReference.checkPtr] at located
  | misaligned =>
    simp [choosePointer, MiniRustReference.checkPtr, found, baseEq, sizeEq, liveEq] at located
  | healthy =>
    have same : ({ id := id, allocation := allocation, offset := 0 } :
        MiniRustReference.CheckedSpan) = checked := by
      simpa [choosePointer, MiniRustReference.checkPtr, found, baseEq, sizeEq, liveEq] using located
    cases same
    exact ⟨rfl, rfl⟩

def designated : Instruction → AtomicMessagePassing.Span
  | .store .d | .read .data => AtomicMessagePassingControls.dataSpan
  | .store .f | .read .flag => AtomicMessagePassingControls.flagSpan

theorem successful_span {input : Input} {machine : Machine} {instruction : Instruction}
    {checked : MiniRustReference.CheckedSpan} (layout : RawLayout machine.raw)
    (located : MiniRustReference.checkPtr machine.raw (handle input instruction).pointer 2 = .ok (some checked)) :
    operand input instruction = .healthy ∧ spanOf checked = designated instruction := by
  obtain ⟨dataBlock, dataFound, dataInfo⟩ := layout_record layout 0 16 rfl
  obtain ⟨flagBlock, flagFound, flagInfo⟩ := layout_record layout 1 32 rfl
  cases instruction with
  | store op =>
    cases op with
    | d =>
      exact check_choice_span dataFound dataInfo located
    | f =>
      exact check_choice_span flagFound flagInfo located
  | read op =>
    cases op with
    | flag => exact check_choice_span flagFound flagInfo located
    | data => exact check_choice_span dataFound dataInfo located

def producerWrites : ProducerPC → List WriteRecord
  | .d => [⟨.initialData, AtomicMessagePassingControls.dataSpan⟩,
      ⟨.initialFlag, AtomicMessagePassingControls.flagSpan⟩]
  | .f => [⟨.initialData, AtomicMessagePassingControls.dataSpan⟩,
      ⟨.initialFlag, AtomicMessagePassingControls.flagSpan⟩,
      ⟨.dataStore, AtomicMessagePassingControls.dataSpan⟩]
  | .done => [⟨.initialData, AtomicMessagePassingControls.dataSpan⟩,
      ⟨.initialFlag, AtomicMessagePassingControls.flagSpan⟩,
      ⟨.dataStore, AtomicMessagePassingControls.dataSpan⟩,
      ⟨.flagStore, AtomicMessagePassingControls.flagSpan⟩]

def ConsumerSlots (machine : Machine) : Prop :=
  match machine.consumer with
  | .a => machine.flagRead = none ∧ machine.dataRead = none
  | .b => (∃ record, machine.flagRead = some record ∧ readValue record = 1) ∧ machine.dataRead = none
  | .skipped => (∃ record, machine.flagRead = some record ∧ readValue record = 0) ∧ machine.dataRead = none
  | .done => (∃ record, machine.flagRead = some record ∧ readValue record = 1) ∧
      ∃ record, machine.dataRead = some record

/-- This is a derived record/PC invariant, not Reach or successful completion
under another name. Raw bytes, global issue order, and faults remain observable. -/
structure Structure (input : Input) (machine : Machine) : Prop where
  layout : RawLayout machine.raw
  writes : machine.writes = producerWrites machine.producer
  slots : ConsumerSlots machine
  writeLocations : ∀ write location, WriteAt machine write location →
    location = AtomicMessagePassing.writeLocation AtomicMessagePassingControls.locations write
  readLocations : ∀ op record, ReadAt machine op record →
    record.location = AtomicMessagePassing.readLocation AtomicMessagePassingControls.locations op
  suppliers : ∀ op record, ReadAt machine op record → WriteAt machine record.supplier record.location
  storeHealthy : ∀ op, WritePresent machine (storeWrite op) → operand input (.store op) = .healthy
  readHealthy : ∀ op record, ReadAt machine op record → operand input (.read op) = .healthy

theorem producerWrites_located (pc : ProducerPC) (write : AtomicMessagePassing.Write)
    (location : AtomicMessagePassing.Span) (member : (⟨write, location⟩ : WriteRecord) ∈ producerWrites pc) :
    location = AtomicMessagePassing.writeLocation AtomicMessagePassingControls.locations write := by
  cases pc <;> cases write <;>
    simp_all [producerWrites, AtomicMessagePassing.writeLocation, AtomicMessagePassingControls.locations]

theorem issued_unique {input : Input} {machine : Machine} (shape : Structure input machine) :
    (machine.writes.map WriteRecord.write).Nodup := by
  rw [shape.writes]
  cases machine.producer <;> decide

/-- The pending instruction has not already issued a successful record. -/
theorem scheduled_store_fresh {input : Input} {machine : Machine} {op : StoreOp}
    (shape : Structure input machine) (scheduled : Scheduled machine (.store op)) :
    ¬ WritePresent machine (storeWrite op) := by
  have writes := shape.writes
  cases op <;> simp_all [Scheduled, WritePresent, WriteAt, producerWrites, storeWrite]

theorem scheduled_read_empty {input : Input} {machine : Machine} {op : AtomicMessagePassing.Read}
    (shape : Structure input machine) (scheduled : Scheduled machine (.read op)) :
    readRecord machine op = none := by
  have slots := shape.slots
  cases op with
  | flag =>
    have both : machine.flagRead = none ∧ machine.dataRead = none := by
      simpa only [ConsumerSlots, show machine.consumer = .a from scheduled] using slots
    exact both.1
  | data =>
    have both : (∃ record, machine.flagRead = some record ∧ readValue record = 1) ∧ machine.dataRead = none := by
      simpa only [ConsumerSlots, show machine.consumer = .b from scheduled] using slots
    exact both.2

theorem flagStore_done {input : Input} {machine : Machine} (shape : Structure input machine)
    (present : WritePresent machine .flagStore) : machine.producer = .done := by
  obtain ⟨location, member⟩ := present
  rw [WriteAt, shape.writes] at member
  cases pc : machine.producer <;> simp_all [producerWrites]

theorem flag_supplier_cases {input : Input} {machine : Machine} (shape : Structure input machine)
    {record : ReadRecord} (read : ReadAt machine .flag record) :
    record.supplier = .initialFlag ∨ record.supplier = .flagStore := by
  have same := (shape.writeLocations _ _ (shape.suppliers _ _ read)).symm.trans (shape.readLocations _ _ read)
  cases chosen : record.supplier <;>
    simp_all [AtomicMessagePassing.writeLocation, AtomicMessagePassing.readLocation,
      AtomicMessagePassingControls.locations, AtomicMessagePassingControls.dataSpan,
      AtomicMessagePassingControls.flagSpan]

theorem flag_one_done {input : Input} {machine : Machine} (shape : Structure input machine)
    {record : ReadRecord} (read : ReadAt machine .flag record) (one : readValue record = 1) :
    machine.producer = .done := by
  rcases flag_supplier_cases shape read with initial | issued
  · simp [readValue, initial, AtomicMessagePassing.writeValue] at one
  · apply flagStore_done shape
    exact ⟨record.location, issued ▸ shape.suppliers _ _ read⟩

/-- The discriminator needed for unguarded stores: no B, and any prior A is
initial-flag supplied. It is false for arbitrary merely coherent Machines. -/
theorem pending_reads {input : Input} {machine : Machine} (shape : Structure input machine)
    (pending : machine.producer ≠ .done) :
    machine.dataRead = none ∧
      ∀ record, ReadAt machine .flag record → record.supplier = .initialFlag := by
  constructor
  · have slots := shape.slots
    cases pc : machine.consumer with
    | a => exact (show machine.flagRead = none ∧ machine.dataRead = none from by
        simpa only [ConsumerSlots, pc] using slots).2
    | b => exact (show (∃ record, machine.flagRead = some record ∧ readValue record = 1) ∧ machine.dataRead = none from by
        simpa only [ConsumerSlots, pc] using slots).2
    | skipped => exact (show (∃ record, machine.flagRead = some record ∧ readValue record = 0) ∧ machine.dataRead = none from by
        simpa only [ConsumerSlots, pc] using slots).2
    | done =>
      obtain ⟨⟨record, read, one⟩, _⟩ := (show
        (∃ record, machine.flagRead = some record ∧ readValue record = 1) ∧
          (∃ record, machine.dataRead = some record) from by
        simpa only [ConsumerSlots, pc] using slots)
      exact False.elim (pending (flag_one_done shape read one))
  · intro record read
    rcases flag_supplier_cases shape read with initial | issued
    · exact initial
    · exact False.elim (pending (flagStore_done shape ⟨record.location, issued ▸ shape.suppliers _ _ read⟩))

theorem readAt_commitRead (before : Machine) (input : Input) (op queried : AtomicMessagePassing.Read)
    (record other : ReadRecord) :
    ReadAt (commitRead before input op record) queried other ↔
      if queried = op then record = other else ReadAt before queried other := by
  cases op <;> cases queried <;> simp [ReadAt, readRecord, commitRead]

theorem writePresent_commitStore (before : Machine) (input : Input) (op : StoreOp)
    (changed : MiniRustReference.State) (location : AtomicMessagePassing.Span)
    (write : AtomicMessagePassing.Write) :
    WritePresent (commitStore before input op changed location) write ↔
      WritePresent before write ∨ write = storeWrite op := by
  constructor
  · rintro ⟨found, member⟩
    have split : (⟨write, found⟩ : WriteRecord) ∈ before.writes ∨
        (⟨write, found⟩ : WriteRecord) = ⟨storeWrite op, location⟩ := by
      simpa only [WriteAt, commitStore, List.mem_append, List.mem_singleton] using member
    rcases split with old | added
    · exact Or.inl ⟨found, old⟩
    · exact Or.inr (congrArg WriteRecord.write added)
  · intro present
    rcases present with ⟨found, member⟩ | same
    · exact ⟨found, List.mem_append_left _ member⟩
    · subst write
      exact ⟨location, List.mem_append_right _ (List.mem_singleton_self _)⟩

theorem storeWrite_injective : Function.Injective storeWrite := by
  intro first second same
  cases first <;> cases second <;> simp_all [storeWrite]

theorem structure_store {input : Input} {before : Machine} {op : StoreOp}
    {changed : MiniRustReference.State} {checked : MiniRustReference.CheckedSpan}
    (shape : Structure input before) (scheduled : Scheduled before (.store op))
    (stored : MiniRustReference.store before.raw (handle input (.store op)).pointer AtomicMessagePassing.oneBytes 2 = .ok changed)
    (located : MiniRustReference.checkPtr before.raw (handle input (.store op)).pointer 2 = .ok (some checked)) :
    Structure input (commitStore before input op changed (spanOf checked)) := by
  obtain ⟨healthy, span⟩ := successful_span shape.layout located
  have oldWrites := shape.writes
  have writes : (commitStore before input op changed (spanOf checked)).writes =
      producerWrites (commitStore before input op changed (spanOf checked)).producer := by
    cases op <;> simp_all [Scheduled, commitStore, designated, producerWrites, storeWrite]
  refine ⟨rawLayout_store shape.layout stored, writes, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ConsumerSlots, commitStore] using shape.slots
  · intro write location member
    apply producerWrites_located _ _ _
    simpa only [WriteAt, writes] using member
  · intro queried record read
    exact shape.readLocations _ _ read
  · intro queried record read
    exact List.mem_append_left _ (shape.suppliers _ _ read)
  · intro queried present
    rcases (writePresent_commitStore _ _ _ _ _ _).mp present with old | added
    · exact shape.storeHealthy queried old
    · have same := storeWrite_injective added
      subst queried
      exact healthy
  · intro queried record read
    exact shape.readHealthy _ _ read

theorem structure_read {input : Input} {before : Machine} {op : AtomicMessagePassing.Read}
    {bytes : List MiniRustReference.Byte} {checked : MiniRustReference.CheckedSpan}
    {supplier : AtomicMessagePassing.Write} (shape : Structure input before)
    (scheduled : Scheduled before (.read op))
    (located : MiniRustReference.checkPtr before.raw (handle input (.read op)).pointer 2 = .ok (some checked))
    (guard : ReadGuard before input op ⟨spanOf checked, supplier, bytes⟩) :
    Structure input (commitRead before input op ⟨spanOf checked, supplier, bytes⟩) := by
  let record : ReadRecord := ⟨spanOf checked, supplier, bytes⟩
  obtain ⟨healthy, span⟩ := successful_span shape.layout located
  refine ⟨shape.layout, shape.writes, ?_, ?_, ?_, guard.2.suppliers, ?_, ?_⟩
  · cases op with
    | flag =>
      have beforeEmpty : before.dataRead = none := by
        have slots := shape.slots
        have both : before.flagRead = none ∧ before.dataRead = none := by
          simpa only [ConsumerSlots, show before.consumer = .a from scheduled] using slots
        exact both.2
      change ConsumerSlots (commitRead before input .flag record)
      by_cases one : readValue record = 1
      · simp only [ConsumerSlots, commitRead, ite_eq_left one]
        exact ⟨⟨record, rfl, one⟩, beforeEmpty⟩
      · have zero : readValue record = 0 := (read_value_binary record).resolve_right one
        simp only [ConsumerSlots, commitRead, ite_eq_right one]
        exact ⟨⟨record, rfl, zero⟩, beforeEmpty⟩
    | data =>
      have previous := shape.slots
      have slots : (∃ flag, before.flagRead = some flag ∧ readValue flag = 1) ∧ before.dataRead = none := by
        simpa only [ConsumerSlots, show before.consumer = .b from scheduled] using previous
      exact ⟨slots.1, record, rfl⟩
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
  · intro queried present
    exact shape.storeHealthy _ present
  · intro queried other read
    have split := (readAt_commitRead before input op queried record other).mp read
    by_cases same : queried = op
    · subst queried
      exact healthy
    · exact shape.readHealthy _ _ (by simpa only [ite_eq_right same] using split)

theorem structure_fault {input : Input} {before : Machine} {instruction : Instruction}
    {outcome : AttemptOutcome} (shape : Structure input before) :
    Structure input (fault before input instruction outcome) := by
  exact ⟨shape.layout, shape.writes, shape.slots, shape.writeLocations,
    shape.readLocations, shape.suppliers, shape.storeHealthy, shape.readHealthy⟩

/-- Equality of the fields that determine the executed graph. Other fields,
including the complete trace and current raw memory, are not quotiented by Step. -/
structure SameGraph (first second : Machine) : Prop where
  writes : first.writes = second.writes
  flag : first.flagRead = second.flagRead
  data : first.dataRead = second.dataRead

theorem sameGraph_read {first second : Machine} (same : SameGraph first second)
    (op : AtomicMessagePassing.Read) (record : ReadRecord) :
    ReadAt first op record ↔ ReadAt second op record := by
  cases op <;> simp only [ReadAt, readRecord, same.flag, same.data]

theorem sameGraph_write {first second : Machine} (same : SameGraph first second)
    (write : AtomicMessagePassing.Write) (location : AtomicMessagePassing.Span) :
    WriteAt first write location ↔ WriteAt second write location := by
  simp only [WriteAt, same.writes]

theorem sameGraph_writePresent {first second : Machine} (same : SameGraph first second)
    (write : AtomicMessagePassing.Write) : WritePresent first write ↔ WritePresent second write := by
  exact exists_congr (fun location => sameGraph_write same write location)

theorem sameGraph_readPresent {first second : Machine} (same : SameGraph first second)
    (op : AtomicMessagePassing.Read) : ReadPresent first op ↔ ReadPresent second op := by
  exact exists_congr (fun record => sameGraph_read same op record)

theorem sameGraph_event {first second : Machine} (same : SameGraph first second)
    (event : AtomicMessagePassing.Event) : EventPresent first event ↔ EventPresent second event := by
  simp only [EventPresent, sameGraph_writePresent same, sameGraph_readPresent same]

theorem sameGraph_hb {first second : Machine} (same : SameGraph first second)
    {mode : AtomicMessagePassing.Mode} {firstEvent lastEvent : AtomicMessagePassing.Event}
    (ordered : PrefixHB first mode firstEvent lastEvent) : PrefixHB second mode firstEvent lastEvent := by
  induction ordered with
  | initialization initial runtime initialIs initialPresent runtimeIs runtimePresent =>
    exact .initialization initial runtime initialIs ((sameGraph_event same _).mp initialPresent)
      runtimeIs ((sameGraph_event same _).mp runtimePresent)
  | producer dataPresent flagPresent =>
    exact .producer ((sameGraph_writePresent same _).mp dataPresent)
      ((sameGraph_writePresent same _).mp flagPresent)
  | consumer flagPresent dataPresent =>
    exact .consumer ((sameGraph_readPresent same _).mp flagPresent)
      ((sameGraph_readPresent same _).mp dataPresent)
  | synchronizes record ra read supplied present =>
    exact .synchronizes record ra ((sameGraph_read same _ _).mp read) supplied
      ((sameGraph_writePresent same _).mp present)
  | trans _ _ left right => exact .trans left right

theorem sameGraph_rules {first second : Machine} (same : SameGraph first second)
    {mode : AtomicMessagePassing.Mode} (rules : PrefixRules first mode) : PrefixRules second mode := by
  have reverse : SameGraph second first := ⟨same.writes.symm, same.flag.symm, same.data.symm⟩
  have mo : ∀ a b, PrefixMO first a b → PrefixMO second a b := by
    intro a b ordered
    exact ⟨(sameGraph_writePresent same _).mp ordered.1,
      (sameGraph_writePresent same _).mp ordered.2.1, ordered.2.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op record read
    exact (sameGraph_write same _ _).mp (rules.suppliers _ _ ((sameGraph_read reverse _ _).mp read))
  · intro op record read ordered
    exact rules.atomicRead _ _ ((sameGraph_read reverse _ _).mp read) (sameGraph_hb reverse ordered)
  · intro event ordered
    exact rules.acyclic event (sameGraph_hb reverse ordered)
  · intro a b al bl aw bw equal ordered
    exact mo _ _ (rules.writeWrite _ _ _ _ ((sameGraph_write reverse _ _).mp aw)
      ((sameGraph_write reverse _ _).mp bw) equal (sameGraph_hb reverse ordered))
  · intro a b ar br aa bb equal ordered
    rcases rules.readRead _ _ _ _ ((sameGraph_read reverse _ _).mp aa)
      ((sameGraph_read reverse _ _).mp bb) equal (sameGraph_hb reverse ordered) with equal | ordered
    · exact Or.inl equal
    · exact Or.inr (mo _ _ ordered)
  · intro op record write location read written equal ordered
    exact mo _ _ (rules.readWrite _ _ _ _ ((sameGraph_read reverse _ _).mp read)
      ((sameGraph_write reverse _ _).mp written) equal (sameGraph_hb reverse ordered))
  · intro write location op record written read equal ordered
    rcases rules.writeRead _ _ _ _ ((sameGraph_write reverse _ _).mp written)
      ((sameGraph_read reverse _ _).mp read) equal (sameGraph_hb reverse ordered) with equal | ordered
    · exact Or.inl equal
    · exact Or.inr (mo _ _ ordered)

theorem fault_coherent {input : Input} {before : Machine} {instruction : Instruction}
    {outcome : AttemptOutcome} {mode : AtomicMessagePassing.Mode}
    (rules : PrefixRules before mode) : PrefixRules (fault before input instruction outcome) mode :=
  sameGraph_rules
    (show SameGraph before (fault before input instruction outcome) from ⟨rfl, rfl, rfl⟩) rules

/-- A proof-only full RF extension agrees with each read actually present.
There is no requirement that the operational prefix eventually complete. -/
def AgreesRF (machine : Machine) (rf : AtomicMessagePassing.RF) : Prop :=
  ∀ op record, ReadAt machine op record → record.supplier = AtomicMessagePassing.source rf op

theorem hb_into_full {machine : Machine} {mode : AtomicMessagePassing.Mode}
    {rf : AtomicMessagePassing.RF} (agrees : AgreesRF machine rf)
    {firstEvent lastEvent : AtomicMessagePassing.Event} (ordered : PrefixHB machine mode firstEvent lastEvent) :
    AtomicMessagePassing.HB mode rf firstEvent lastEvent := by
  induction ordered with
  | initialization initial runtime initialIs _ runtimeIs _ =>
    exact .initialization initial runtime initialIs runtimeIs
  | producer _ _ => exact .producer
  | consumer _ _ => exact .consumer
  | synchronizes record ra read supplied _ =>
    exact .synchronizes ra ((agrees .flag record read).symm.trans supplied)
  | trans _ _ left right => exact .trans left right

/-- Restriction of old graph facts to actually issued records. This is a lemma
about the declared graphs, not a definition of an operational transition. -/
theorem rules_from_full {input : Input} {machine : Machine} {rf : AtomicMessagePassing.RF}
    (shape : Structure input machine) (agrees : AgreesRF machine rf)
    (full : AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations input.mode rf) :
    PrefixRules machine input.mode := by
  refine ⟨shape.suppliers, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op record read ordered
    apply full.atomicRead op
    simpa only [agrees _ _ read] using hb_into_full agrees ordered
  · intro event ordered
    exact full.acyclic event (hb_into_full agrees ordered)
  · intro a b al bl aa bb equal ordered
    exact ⟨⟨al, aa⟩, ⟨bl, bb⟩, full.writeWrite _ _
      ((shape.writeLocations _ _ aa).symm.trans (equal.trans (shape.writeLocations _ _ bb)))
      (hb_into_full agrees ordered)⟩
  · intro a b ar br aa bb equal ordered
    have compared := full.readRead a b
      ((shape.readLocations _ _ aa).symm.trans (equal.trans (shape.readLocations _ _ bb)))
      (hb_into_full agrees ordered)
    rcases compared with equal | mo
    · exact Or.inl ((agrees _ _ aa).trans (equal.trans (agrees _ _ bb).symm))
    · refine Or.inr ⟨⟨ar.location, shape.suppliers _ _ aa⟩,
        ⟨br.location, shape.suppliers _ _ bb⟩, ?_⟩
      simpa only [agrees _ _ aa, agrees _ _ bb] using mo
  · intro op record write location read written equal ordered
    refine ⟨⟨record.location, shape.suppliers _ _ read⟩, ⟨location, written⟩, ?_⟩
    have mo := full.readWrite op write
      ((shape.readLocations _ _ read).symm.trans (equal.trans (shape.writeLocations _ _ written)))
      (hb_into_full agrees ordered)
    simpa only [agrees _ _ read] using mo
  · intro write location op record written read equal ordered
    have compared := full.writeRead write op
      ((shape.writeLocations _ _ written).symm.trans (equal.trans (shape.readLocations _ _ read)))
      (hb_into_full agrees ordered)
    rcases compared with equal | mo
    · exact Or.inl (equal.trans (agrees _ _ read).symm)
    · refine Or.inr ⟨⟨location, written⟩, ⟨record.location, shape.suppliers _ _ read⟩, ?_⟩
      simpa only [agrees _ _ read] using mo

def zeroRF : AtomicMessagePassing.RF := ⟨.initialFlag, .initialData⟩

theorem zero_cut {mode : AtomicMessagePassing.Mode} {firstEvent lastEvent : AtomicMessagePassing.Event}
    (ordered : AtomicMessagePassing.HB mode zeroRF firstEvent lastEvent) :
    AtomicMessagePassing.producerCut firstEvent ≤ AtomicMessagePassing.producerCut lastEvent := by
  induction ordered with
  | initialization initial runtime initialIs runtimeIs =>
    cases initial <;> cases runtime <;>
      simp_all [AtomicMessagePassing.IsInitial, AtomicMessagePassing.IsRuntime, AtomicMessagePassing.producerCut]
  | producer => decide
  | consumer => decide
  | synchronizes _ impossible => simp [zeroRF] at impossible
  | trans _ _ left right => exact Nat.le_trans left right

theorem zero_rules (mode : AtomicMessagePassing.Mode) :
    AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations mode zeroRF := by
  apply AtomicMessagePassing.rules_of_write_read _ AtomicMessagePassingControls.selected_shape
  · exact ⟨rfl, rfl⟩
  · intro write op same ordered
    have cut := zero_cut ordered
    cases write <;> cases op <;>
      simp_all [AtomicMessagePassing.writeLocation, AtomicMessagePassing.readLocation,
        AtomicMessagePassingControls.locations, AtomicMessagePassingControls.dataSpan,
        AtomicMessagePassingControls.flagSpan, AtomicMessagePassing.source, zeroRF,
        AtomicMessagePassing.MO, AtomicMessagePassing.writeEvent, AtomicMessagePassing.readEvent,
        AtomicMessagePassing.producerCut]

/-- Every scheduled successful store preserves coherence from the derived
structure alone. No incoming-coherence, RF, or future-completion premise is used. -/
theorem store_coherent {input : Input} {before : Machine} {op : StoreOp}
    {changed : MiniRustReference.State} {checked : MiniRustReference.CheckedSpan}
    (shape : Structure input before) (scheduled : Scheduled before (.store op))
    (stored : MiniRustReference.store before.raw (handle input (.store op)).pointer AtomicMessagePassing.oneBytes 2 = .ok changed)
    (located : MiniRustReference.checkPtr before.raw (handle input (.store op)).pointer 2 = .ok (some checked)) :
    PrefixRules (commitStore before input op changed (spanOf checked)) input.mode := by
  have pending : before.producer ≠ .done := by
    cases op <;> simp_all [Scheduled]
  obtain ⟨noB, priorA⟩ := pending_reads shape pending
  apply rules_from_full (structure_store shape scheduled stored located) (rf := zeroRF)
  · intro read record present
    cases read with
    | flag => exact priorA record present
    | data => simp [ReadAt, readRecord, commitStore, noB] at present
  · exact zero_rules input.mode

/-- Certificate-free public store-addition statement: actual raw success is
sufficient for a real successor with coherent records and the exact new memory. -/
theorem scheduled_store_coherent {input : Input} {before : Machine} {op : StoreOp}
    {changed : MiniRustReference.State} (shape : Structure input before)
    (scheduled : Scheduled before (.store op))
    (stored : MiniRustReference.store before.raw (handle input (.store op)).pointer AtomicMessagePassing.oneBytes 2 = .ok changed) :
    ∃ checked, MiniRustReference.checkPtr before.raw (handle input (.store op)).pointer 2 = .ok (some checked) ∧
      Step input (.running before) (.running (commitStore before input op changed (spanOf checked))) ∧
      Structure input (commitStore before input op changed (spanOf checked)) ∧
      PrefixRules (commitStore before input op changed (spanOf checked)) input.mode ∧
      (commitStore before input op changed (spanOf checked)).raw = changed := by
  obtain ⟨checked, located⟩ := store_success_checked stored
  exact ⟨checked, located, ⟨.issue (.store op), ActionStep.store scheduled stored located⟩,
    structure_store shape scheduled stored located, store_coherent shape scheduled stored located, rfl⟩

theorem initial_structure (input : Input) : Structure input initialMachine := by
  refine ⟨⟨rfl, fun _ => rfl⟩, rfl, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro write location member
    exact producerWrites_located .d _ _ member
  · intro op record read
    cases op <;> simp [ReadAt, readRecord, initialMachine] at read
  · intro op record read
    cases op <;> simp [ReadAt, readRecord, initialMachine] at read
  · intro op present
    obtain ⟨location, member⟩ := present
    cases op <;> simp [WriteAt, initialMachine, storeWrite] at member
  · intro op record read
    cases op <;> simp [ReadAt, readRecord, initialMachine] at read

theorem initial_coherent (input : Input) : PrefixRules initialMachine input.mode := by
  apply rules_from_full (initial_structure input) (rf := zeroRF)
  · intro op record read
    cases op <;> simp [ReadAt, readRecord, initialMachine] at read
  · exact zero_rules input.mode

def machineOf : Config → Machine
  | .running machine | .normal machine | .ub _ _ machine | .unsupported _ machine => machine

def ConfigInvariant (input : Input) (config : Config) : Prop :=
  Structure input (machineOf config) ∧ PrefixRules (machineOf config) input.mode ∧
    match config with | .normal machine => Finished machine | _ => True

theorem invariant_step {input : Input} {before after : Config}
    (invariant : ConfigInvariant input before) (edge : Step input before after) :
    ConfigInvariant input after := by
  obtain ⟨action, edge⟩ := edge
  cases edge with
  | store scheduled stored located =>
    exact ⟨structure_store invariant.1 scheduled stored located,
      store_coherent invariant.1 scheduled stored located, True.intro⟩
  | read scheduled loaded located guard =>
    exact ⟨structure_read invariant.1 scheduled located guard, guard.2, True.intro⟩
  | ub scheduled failed =>
    exact ⟨structure_fault invariant.1,
      fault_coherent invariant.2.1, True.intro⟩
  | unsupported scheduled failed =>
    exact ⟨structure_fault invariant.1,
      fault_coherent invariant.2.1, True.intro⟩
  | finish finished => exact ⟨invariant.1, invariant.2.1, finished⟩

/-- Includes running, normal and ordinary terminal residuals; it is not NoUB. -/
theorem root_prefix_invariant {input : Input} {config : Config}
    (path : Execution.Reach (Step input) root config) : ConfigInvariant input config := by
  exact Execution.invariant_reachable
    (show ConfigInvariant input root from ⟨initial_structure input, initial_coherent input, True.intro⟩)
    (fun invariant edge => invariant_step invariant edge) path

theorem root_prefix_coherent {input : Input} {config : Config}
    (path : Execution.Reach (Step input) root config) :
    PrefixRules (machineOf config) input.mode :=
  (root_prefix_invariant path).2.1

/-- Exactly the records needed for the full selected graph, not a gate that
operational prefixes must satisfy before executing. -/
structure Complete (machine : Machine) (flag data : ReadRecord) : Prop where
  producer : machine.producer = .done
  flag : machine.flagRead = some flag
  data : machine.dataRead = some data

def extractedRF (flag data : ReadRecord) : AtomicMessagePassing.RF :=
  ⟨flag.supplier, data.supplier⟩

def recordFor (flag data : ReadRecord) : AtomicMessagePassing.Read → ReadRecord
  | .flag => flag | .data => data

theorem complete_read {machine : Machine} {flag data : ReadRecord}
    (complete : Complete machine flag data) (op : AtomicMessagePassing.Read) :
    ReadAt machine op (recordFor flag data op) := by
  cases op with
  | flag => exact complete.flag
  | data => exact complete.data

theorem complete_agrees {machine : Machine} {flag data : ReadRecord}
    (complete : Complete machine flag data) : AgreesRF machine (extractedRF flag data) := by
  intro op record read
  have equal : recordFor flag data op = record :=
    Option.some.inj ((complete_read complete op).symm.trans read)
  subst record
  cases op <;> rfl

theorem complete_write {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    (write : AtomicMessagePassing.Write) :
    WriteAt machine write (AtomicMessagePassing.writeLocation AtomicMessagePassingControls.locations write) := by
  rw [WriteAt, shape.writes, complete.producer]
  cases write <;> simp [producerWrites, AtomicMessagePassing.writeLocation,
    AtomicMessagePassingControls.locations]

theorem complete_events {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    (event : AtomicMessagePassing.Event) : EventPresent machine event := by
  cases event with
  | initData => exact Or.inl ⟨.initialData, ⟨_, complete_write shape complete .initialData⟩, rfl⟩
  | initFlag => exact Or.inl ⟨.initialFlag, ⟨_, complete_write shape complete .initialFlag⟩, rfl⟩
  | d => exact Or.inl ⟨.dataStore, ⟨_, complete_write shape complete .dataStore⟩, rfl⟩
  | f => exact Or.inl ⟨.flagStore, ⟨_, complete_write shape complete .flagStore⟩, rfl⟩
  | a => exact Or.inr ⟨.flag, ⟨flag, complete.flag⟩, rfl⟩
  | b => exact Or.inr ⟨.data, ⟨data, complete.data⟩, rfl⟩

theorem hb_from_full {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    {firstEvent lastEvent : AtomicMessagePassing.Event}
    (ordered : AtomicMessagePassing.HB input.mode (extractedRF flag data) firstEvent lastEvent) :
    PrefixHB machine input.mode firstEvent lastEvent := by
  induction ordered with
  | initialization initial runtime initialIs runtimeIs =>
    exact .initialization initial runtime initialIs (complete_events shape complete initial)
      runtimeIs (complete_events shape complete runtime)
  | producer =>
    exact .producer ⟨_, complete_write shape complete .dataStore⟩
      ⟨_, complete_write shape complete .flagStore⟩
  | consumer => exact .consumer ⟨flag, complete.flag⟩ ⟨data, complete.data⟩
  | synchronizes ra supplied =>
    exact .synchronizes flag ra complete.flag supplied ⟨_, complete_write shape complete .flagStore⟩
  | trans _ _ left right => exact .trans left right

theorem complete_hb_iff {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    (firstEvent lastEvent : AtomicMessagePassing.Event) :
    PrefixHB machine input.mode firstEvent lastEvent ↔
      AtomicMessagePassing.HB input.mode (extractedRF flag data) firstEvent lastEvent :=
  ⟨hb_into_full (complete_agrees complete), hb_from_full shape complete⟩

theorem complete_mo_iff {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    (a b : AtomicMessagePassing.Write) :
    PrefixMO machine a b ↔ AtomicMessagePassing.MO a b := by
  constructor
  · exact fun ordered => ordered.2.2
  · intro ordered
    exact ⟨⟨_, complete_write shape complete a⟩, ⟨_, complete_write shape complete b⟩, ordered⟩

/-- Reverse graph bridge uses the actual recorded RF identities. Automatic
old clauses are reused openly; write-read coherence is transported from the
executed graph through the proved reverse HB bridge. -/
theorem complete_selected_rules {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data)
    (rules : PrefixRules machine input.mode) :
    AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations input.mode
      (extractedRF flag data) := by
  have agrees := complete_agrees complete
  apply AtomicMessagePassing.rules_of_write_read _ AtomicMessagePassingControls.selected_shape
  · constructor
    · exact (shape.writeLocations _ _ (shape.suppliers .flag flag complete.flag)).symm.trans
        (shape.readLocations .flag flag complete.flag)
    · exact (shape.writeLocations _ _ (shape.suppliers .data data complete.data)).symm.trans
        (shape.readLocations .data data complete.data)
  · intro write op same ordered
    let record := recordFor flag data op
    have read : ReadAt machine op record := complete_read complete op
    have written := complete_write shape complete write
    have equal : AtomicMessagePassing.writeLocation AtomicMessagePassingControls.locations write = record.location :=
      same.trans (shape.readLocations op record read).symm
    have compared := rules.writeRead write _ op record written read equal (hb_from_full shape complete ordered)
    rcases compared with equal | mo
    · exact Or.inl (equal.trans (agrees op record read))
    · exact Or.inr (by simpa only [agrees op record read] using mo.2.2)

theorem normal_flag_one_complete {input : Input} {machine : Machine} {flag : ReadRecord}
    (path : Execution.Reach (Step input) root (.normal machine))
    (read : ReadAt machine .flag flag) (one : readValue flag = 1) :
    ∃ data, Complete machine flag data := by
  have invariant := root_prefix_invariant path
  have finished : Finished machine := invariant.2.2
  have slots : ConsumerSlots machine := invariant.1.slots
  rcases finished.2 with skipped | done
  · have both : (∃ record, machine.flagRead = some record ∧ readValue record = 0) ∧ machine.dataRead = none := by
      simpa only [ConsumerSlots, skipped] using slots
    obtain ⟨other, otherRead, zero⟩ := both.1
    have equal : other = flag := Option.some.inj (otherRead.symm.trans read)
    subst other
    omega
  · have both : (∃ record, machine.flagRead = some record ∧ readValue record = 1) ∧
        (∃ record, machine.dataRead = some record) := by
      simpa only [ConsumerSlots, done] using slots
    obtain ⟨data, dataRead⟩ := both.2
    exact ⟨data, finished.1, read, dataRead⟩

/-- Canonical span and operand health are derived from actual successful
history. This will justify the old snapshot gates in the next module; it does
not identify the current raw data with that snapshot. -/
theorem completed_operands {input : Input} {machine : Machine} {flag data : ReadRecord}
    (shape : Structure input machine) (complete : Complete machine flag data) :
    input.d = .healthy ∧ input.f = .healthy ∧ input.a = .healthy ∧ input.b = .healthy := by
  exact ⟨shape.storeHealthy .d ⟨_, complete_write shape complete .dataStore⟩,
    shape.storeHealthy .f ⟨_, complete_write shape complete .flagStore⟩,
    shape.readHealthy .flag flag complete.flag, shape.readHealthy .data data complete.data⟩

/-- Completed A=1 projection is a theorem about actual prefixes, not an
admission of arbitrary predictions or a full-prefix equivalence to runCandidate. -/
theorem completed_flag_one_bridge {input : Input} {machine : Machine} {flag : ReadRecord}
    (path : Execution.Reach (Step input) root (.normal machine))
    (read : ReadAt machine .flag flag) (one : readValue flag = 1) :
    ∃ data, Complete machine flag data ∧
      AtomicMessagePassing.SelectedRules AtomicMessagePassingControls.locations input.mode (extractedRF flag data) ∧
      (∀ firstEvent lastEvent, PrefixHB machine input.mode firstEvent lastEvent ↔
        AtomicMessagePassing.HB input.mode (extractedRF flag data) firstEvent lastEvent) ∧
      (∀ a b, PrefixMO machine a b ↔ AtomicMessagePassing.MO a b) ∧
      (input.d = .healthy ∧ input.f = .healthy ∧ input.a = .healthy ∧ input.b = .healthy) := by
  obtain ⟨data, complete⟩ := normal_flag_one_complete path read one
  have invariant := root_prefix_invariant path
  exact ⟨data, complete, complete_selected_rules invariant.1 complete invariant.2.1,
    complete_hb_iff invariant.1 complete, complete_mo_iff invariant.1 complete,
    completed_operands invariant.1 complete⟩

#print axioms checked_lookup
#print axioms store_preserves_info
#print axioms successful_span
#print axioms issued_unique
#print axioms scheduled_store_fresh
#print axioms scheduled_read_empty
#print axioms pending_reads
#print axioms structure_store
#print axioms structure_read
#print axioms sameGraph_rules
#print axioms rules_from_full
#print axioms store_coherent
#print axioms scheduled_store_coherent
#print axioms root_prefix_invariant
#print axioms root_prefix_coherent
#print axioms complete_hb_iff
#print axioms complete_mo_iff
#print axioms complete_selected_rules
#print axioms completed_operands
#print axioms completed_flag_one_bridge

end AnnealResearch.AtomicPrefixRules
