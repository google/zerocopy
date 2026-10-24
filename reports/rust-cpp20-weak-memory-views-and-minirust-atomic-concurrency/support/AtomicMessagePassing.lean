import AnnealResearch.MiniRustReference

/-!
An owned six-event candidate interface for the selected completed A=1 branch.
This is mathematical compatibility with the listed atomic rules, not a Rust,
C++20, compiler, target or full weak-memory adequacy theorem. The two initial
zero modifications and their publication edges are explicit history premises.
Ordinary gates use a fixed raw validity snapshot; their bytes do not determine
the atomic return values. Failed gates produce no resolved location.
-/
namespace AnnealResearch.AtomicMessagePassing

inductive Event where
  | initData | initFlag | d | f | a | b
  deriving DecidableEq, Repr

inductive Write where
  | initialData | initialFlag | dataStore | flagStore
  deriving DecidableEq, Repr

inductive Read where
  | flag | data
  deriving DecidableEq, Repr

inductive Mode where
  | releaseAcquire | relaxed
  deriving DecidableEq, Repr

def writeEvent : Write → Event
  | .initialData => .initData
  | .initialFlag => .initFlag
  | .dataStore => .d
  | .flagStore => .f

def readEvent : Read → Event
  | .flag => .a
  | .data => .b

def writeValue : Write → Nat
  | .initialData | .initialFlag => 0
  | .dataStore | .flagStore => 1

structure RF where
  flag : Write
  data : Write
  deriving DecidableEq, Repr

def source (rf : RF) : Read → Write
  | .flag => rf.flag
  | .data => rf.data

def flagValue (rf : RF) : Nat := writeValue rf.flag
def dataValue (rf : RF) : Nat := writeValue rf.data
def returned (rf : RF) : Nat × Nat := (flagValue rf, dataValue rf)

structure Span where
  allocation : Nat
  offset : Nat
  width : Nat
  deriving DecidableEq, Repr

/-- Allocation identity and actual byte extent, never a handle label. -/
def Disjoint (first second : Span) : Prop :=
  first.allocation ≠ second.allocation ∨
    first.offset + first.width ≤ second.offset ∨
    second.offset + second.width ≤ first.offset

structure Locations where
  data : Span
  flag : Span
  observedFlag : Span
  observedData : Span
  deriving DecidableEq, Repr

/-- Selected geometry, not a successful consistency or safety premise. -/
structure Shape (locations : Locations) : Prop where
  sameFlag : locations.observedFlag = locations.flag
  sameData : locations.observedData = locations.data
  dataWidth : locations.data.width = 2
  flagWidth : locations.flag.width = 2
  separate : locations.data ≠ locations.flag
  disjoint : Disjoint locations.data locations.flag

def writeLocation (locations : Locations) : Write → Span
  | .initialData | .dataStore => locations.data
  | .initialFlag | .flagStore => locations.flag

def readLocation (locations : Locations) : Read → Span
  | .flag => locations.observedFlag
  | .data => locations.observedData

structure RFValid (locations : Locations) (rf : RF) : Prop where
  flagLocation : writeLocation locations rf.flag = locations.observedFlag
  dataLocation : writeLocation locations rf.data = locations.observedData

/-- Exactly two modifications per location; this is not a global write order. -/
def MO : Write → Write → Prop
  | .initialData, .dataStore => True
  | .initialFlag, .flagStore => True
  | _, _ => False

theorem mo_irreflexive (write : Write) : ¬ MO write write := by
  cases write <;> simp [MO]

theorem mo_transitive (first middle last : Write)
    (left : MO first middle) (right : MO middle last) : MO first last := by
  cases first <;> cases middle <;> cases last <;> simp_all [MO]

theorem mo_same_location (locations : Locations) (first second : Write)
    (ordered : MO first second) :
    writeLocation locations first = writeLocation locations second := by
  cases first <;> cases second <;> simp_all [MO, writeLocation]

theorem mo_total_per_location (locations : Locations) (shape : Shape locations)
    (first second : Write) (same : writeLocation locations first = writeLocation locations second)
    (different : first ≠ second) : MO first second ∨ MO second first := by
  have apart := shape.separate
  have reverse := Ne.symm apart
  cases first <;> cases second <;> simp_all [MO, writeLocation]

def IsInitial : Event → Prop
  | .initData | .initFlag => True
  | _ => False

def IsRuntime : Event → Prop
  | .d | .f | .a | .b => True
  | _ => False

/-- Transitive closure of only the declared initial, SB and SW edges.
There is no constructor for an arbitrary RF edge or for D HB B. -/
inductive HB (mode : Mode) (rf : RF) : Event → Event → Prop where
  | initialization (initial runtime : Event) :
      IsInitial initial → IsRuntime runtime → HB mode rf initial runtime
  | producer : HB mode rf .d .f
  | consumer : HB mode rf .a .b
  | synchronizes : mode = .releaseAcquire → rf.flag = .flagStore → HB mode rf .f .a
  | trans {first middle last : Event} :
      HB mode rf first middle → HB mode rf middle last → HB mode rf first last

def rank : Event → Nat
  | .initData | .initFlag => 0
  | .d => 1
  | .f => 2
  | .a => 3
  | .b => 4

theorem hb_rank {mode : Mode} {rf : RF} {first last : Event}
    (ordered : HB mode rf first last) : rank first < rank last := by
  induction ordered with
  | initialization initial runtime initialIs runtimeIs =>
      cases initial <;> cases runtime <;> simp_all [IsInitial, IsRuntime, rank]
  | producer => decide
  | consumer => decide
  | synchronizes _ _ => decide
  | trans _ _ left right => exact Nat.lt_trans left right

theorem hb_acyclic (mode : Mode) (rf : RF) (event : Event) : ¬ HB mode rf event event := by
  intro ordered
  exact Nat.lt_irrefl _ (hb_rank ordered)

theorem no_read_hb_write (mode : Mode) (rf : RF) (read : Read) (write : Write) :
    ¬ HB mode rf (readEvent read) (writeEvent write) := by
  intro ordered
  have increasing := hb_rank ordered
  cases read <;> cases write <;> simp [readEvent, writeEvent, rank] at increasing

def producerCut : Event → Nat
  | .d | .f => 1
  | _ => 0

/-- A separate monotonic observer proves absence of producer→consumer HB
in relaxed mode, without enumerating transitive paths. -/
theorem relaxed_cut {rf : RF} {first last : Event}
    (ordered : HB .relaxed rf first last) : producerCut first ≤ producerCut last := by
  induction ordered with
  | initialization initial runtime initialIs runtimeIs =>
      cases initial <;> cases runtime <;> simp_all [IsInitial, IsRuntime, producerCut]
  | producer => decide
  | consumer => decide
  | synchronizes impossible _ => cases impossible
  | trans _ _ left right => exact Nat.le_trans left right

theorem data_hb_read {rf : RF} (supplied : rf.flag = .flagStore) :
    HB .releaseAcquire rf .d .b := by
  exact .trans .producer (.trans (.synchronizes rfl supplied) .consumer)

def WriteWrite (locations : Locations) (mode : Mode) (rf : RF) : Prop :=
  ∀ first second, writeLocation locations first = writeLocation locations second →
    HB mode rf (writeEvent first) (writeEvent second) → MO first second

def ReadRead (locations : Locations) (mode : Mode) (rf : RF) : Prop :=
  ∀ first second, readLocation locations first = readLocation locations second →
    HB mode rf (readEvent first) (readEvent second) →
    source rf first = source rf second ∨ MO (source rf first) (source rf second)

def ReadWrite (locations : Locations) (mode : Mode) (rf : RF) : Prop :=
  ∀ read write, readLocation locations read = writeLocation locations write →
    HB mode rf (readEvent read) (writeEvent write) → MO (source rf read) write

def WriteRead (locations : Locations) (mode : Mode) (rf : RF) : Prop :=
  ∀ write read, writeLocation locations write = readLocation locations read →
    HB mode rf (writeEvent write) (readEvent read) →
    write = source rf read ∨ MO write (source rf read)

/-- Supplier type fixes modifying side effects; RFValid fixes their actual
location, and returned computes their values. atomicRead is a separate rule. -/
structure SelectedRules (locations : Locations) (mode : Mode) (rf : RF) : Prop where
  suppliers : RFValid locations rf
  atomicRead : ∀ read, ¬ HB mode rf (readEvent read) (writeEvent (source rf read))
  acyclic : ∀ event, ¬ HB mode rf event event
  writeWrite : WriteWrite locations mode rf
  readRead : ReadRead locations mode rf
  readWrite : ReadWrite locations mode rf
  writeRead : WriteRead locations mode rf

theorem flag_supplier (locations : Locations) (shape : Shape locations) (rf : RF)
    (valid : RFValid locations rf) : rf.flag = .initialFlag ∨ rf.flag = .flagStore := by
  have located := valid.flagLocation
  cases chosen : rf.flag with
  | initialData =>
      have wrong : locations.data = locations.flag := by
        simpa only [chosen, writeLocation, shape.sameFlag] using located
      exact False.elim (shape.separate wrong)
  | initialFlag => exact Or.inl rfl
  | dataStore =>
      have wrong : locations.data = locations.flag := by
        simpa only [chosen, writeLocation, shape.sameFlag] using located
      exact False.elim (shape.separate wrong)
  | flagStore => exact Or.inr rfl

theorem data_supplier (locations : Locations) (shape : Shape locations) (rf : RF)
    (valid : RFValid locations rf) : rf.data = .initialData ∨ rf.data = .dataStore := by
  have located := valid.dataLocation
  cases chosen : rf.data with
  | initialData => exact Or.inl rfl
  | initialFlag =>
      have wrong : locations.flag = locations.data := by
        simpa only [chosen, writeLocation, shape.sameData] using located
      exact False.elim (shape.separate wrong.symm)
  | dataStore => exact Or.inr rfl
  | flagStore =>
      have wrong : locations.flag = locations.data := by
        simpa only [chosen, writeLocation, shape.sameData] using located
      exact False.elim (shape.separate wrong.symm)

theorem flag_one_supplier (locations : Locations) (shape : Shape locations) (rf : RF)
    (valid : RFValid locations rf) (one : flagValue rf = 1) : rf.flag = .flagStore := by
  rcases flag_supplier locations shape rf valid with initial | stored
  · simp [flagValue, initial, writeValue] at one
  · exact stored

private theorem write_write_automatic (locations : Locations) (shape : Shape locations)
    (mode : Mode) (rf : RF) : WriteWrite locations mode rf := by
  intro first second same ordered
  have increasing := hb_rank ordered
  have apart := shape.separate
  have reverse := Ne.symm apart
  cases first <;> cases second <;> simp_all [writeLocation, writeEvent, rank, MO]

private theorem read_read_automatic (locations : Locations) (shape : Shape locations)
    (mode : Mode) (rf : RF) : ReadRead locations mode rf := by
  intro first second same ordered
  have apart : locations.observedFlag ≠ locations.observedData := by
    intro equal
    exact shape.separate (shape.sameData.symm.trans (equal.symm.trans shape.sameFlag))
  have reverse := Ne.symm apart
  have increasing := hb_rank ordered
  cases first <;> cases second <;> simp_all [readLocation, readEvent, rank]

private theorem read_write_automatic (locations : Locations) (mode : Mode) (rf : RF) :
    ReadWrite locations mode rf := by
  intro read write _ ordered
  exact False.elim (no_read_hb_write mode rf read write ordered)

theorem rules_of_write_read (locations : Locations) (shape : Shape locations)
    (mode : Mode) (rf : RF) (valid : RFValid locations rf)
    (coherent : WriteRead locations mode rf) : SelectedRules locations mode rf :=
  { suppliers := valid
    atomicRead := fun read => no_read_hb_write mode rf read (source rf read)
    acyclic := hb_acyclic mode rf
    writeWrite := write_write_automatic locations shape mode rf
    readRead := read_read_automatic locations shape mode rf
    readWrite := read_write_automatic locations mode rf
    writeRead := coherent }

theorem ra_flag_one_data_one (locations : Locations) (shape : Shape locations) (rf : RF)
    (rules : SelectedRules locations .releaseAcquire rf) (one : flagValue rf = 1) :
    dataValue rf = 1 := by
  have supplied := flag_one_supplier locations shape rf rules.suppliers one
  have ordered := data_hb_read supplied
  have coherent := rules.writeRead .dataStore .data shape.sameData.symm ordered
  rcases data_supplier locations shape rf rules.suppliers with initial | stored
  · simp [source, initial, MO] at coherent
  · simp [dataValue, stored, writeValue]

def bothStores : RF := ⟨.flagStore, .dataStore⟩
def staleData : RF := ⟨.flagStore, .initialData⟩

theorem both_stores_rules (locations : Locations) (shape : Shape locations) (mode : Mode) :
    SelectedRules locations mode bothStores := by
  apply rules_of_write_read locations shape mode bothStores
  · exact ⟨shape.sameFlag.symm, shape.sameData.symm⟩
  · intro write read same _ordered
    have apart := shape.separate
    have reverse := Ne.symm apart
    cases write <;> cases read <;>
      simp_all [writeLocation, readLocation, source, bothStores, MO,
        shape.sameFlag, shape.sameData]

theorem relaxed_stale_rules (locations : Locations) (shape : Shape locations) :
    SelectedRules locations .relaxed staleData := by
  apply rules_of_write_read locations shape .relaxed staleData
  · exact ⟨shape.sameFlag.symm, shape.sameData.symm⟩
  · intro write read same ordered
    have monotone := relaxed_cut ordered
    have apart := shape.separate
    have reverse := Ne.symm apart
    cases write <;> cases read <;>
      simp_all [writeLocation, readLocation, source, staleData, MO,
        shape.sameFlag, shape.sameData, writeEvent, readEvent, producerCut]

theorem witness_values : returned bothStores = (1, 1) ∧ returned staleData = (1, 0) := by
  exact ⟨rfl, rfl⟩

/-- Distinct ranks impose a total relative schedule on all six events. Gaps in
Nat ranks are irrelevant; no event or write is added by this alternative. -/
structure Schedule where
  position : Event → Nat
  distinct : Function.Injective position
  initialization : ∀ initial runtime, IsInitial initial → IsRuntime runtime →
    position initial < position runtime
  producer : position .d < position .f
  consumer : position .a < position .b

structure LatestOnly (locations : Locations) (rf : RF) (schedule : Schedule) : Prop where
  suppliers : RFValid locations rf
  before : ∀ read,
    schedule.position (writeEvent (source rf read)) < schedule.position (readEvent read)
  latest : ∀ read write, writeLocation locations write = readLocation locations read →
    schedule.position (writeEvent (source rf read)) < schedule.position (writeEvent write) →
    schedule.position (writeEvent write) < schedule.position (readEvent read) → False

theorem latest_flag_one_data_one (locations : Locations) (shape : Shape locations)
    (rf : RF) (schedule : Schedule) (latest : LatestOnly locations rf schedule)
    (one : flagValue rf = 1) : dataValue rf = 1 := by
  have supplied := flag_one_supplier locations shape rf latest.suppliers one
  have flagBefore := latest.before .flag
  have fBeforeA : schedule.position .f < schedule.position .a := by
    simpa only [source, supplied, writeEvent, readEvent] using flagBefore
  have dBeforeB : schedule.position .d < schedule.position .b :=
    Nat.lt_trans schedule.producer (Nat.lt_trans fBeforeA schedule.consumer)
  rcases data_supplier locations shape rf latest.suppliers with initial | stored
  · apply False.elim
    apply latest.latest .data .dataStore shape.sameData.symm
    · simpa only [source, initial, writeEvent] using
        schedule.initialization .initData .d trivial trivial
    · exact dBeforeB
  · simp [dataValue, stored, writeValue]

theorem stale_not_latest (locations : Locations) (shape : Shape locations)
    (schedule : Schedule) : ¬ LatestOnly locations staleData schedule := by
  intro latest
  have impossible := latest_flag_one_data_one locations shape staleData schedule latest rfl
  simp [dataValue, staleData, writeValue] at impossible

def sequentialPosition : Event → Nat
  | .initData => 0
  | .initFlag => 1
  | .d => 2
  | .f => 3
  | .a => 4
  | .b => 5

/-- A concrete total schedule makes the named alternative nonvacuous. -/
def sequentialSchedule : Schedule :=
  { position := sequentialPosition
    distinct := by
      intro first second same
      cases first <;> cases second <;> simp_all [sequentialPosition]
    initialization := by
      intro initial runtime initialIs runtimeIs
      cases initial <;> cases runtime <;>
        simp_all [IsInitial, IsRuntime, sequentialPosition]
    producer := by decide
    consumer := by decide }

theorem sequential_both_stores_latest (locations : Locations) (shape : Shape locations) :
    LatestOnly locations bothStores sequentialSchedule := by
  refine ⟨⟨shape.sameFlag.symm, shape.sameData.symm⟩, ?_, ?_⟩
  · intro read
    cases read <;> decide
  · intro read write same afterSource beforeRead
    have apart := shape.separate
    have reverse := Ne.symm apart
    cases read <;> cases write <;>
      simp_all [writeLocation, readLocation, source, bothStores,
        shape.sameFlag, shape.sameData, sequentialSchedule, sequentialPosition,
        writeEvent]

structure Handle where
  pointer : MiniRustReference.Ptr
  label : Nat
  deriving DecidableEq, Repr

structure Handles where
  dataStore : Handle
  flagStore : Handle
  flagLoad : Handle
  dataLoad : Handle
  deriving DecidableEq, Repr

def oneBytes : List MiniRustReference.Byte := [.init 1 none, .init 0 none]

/-- Only actual checkPtr success creates a location; no fallback span exists. -/
def checkedLocation (state : MiniRustReference.State) (pointer : MiniRustReference.Ptr) : MiniRustReference.Result Span :=
  match MiniRustReference.checkPtr state pointer 2 with
  | .ok (some checked) => .ok ⟨checked.id, checked.offset, 2⟩
  | .ok none => .unsupported
  | .ub diagnostic => .ub diagnostic
  | .unsupported => .unsupported
  | .noChoice => .noChoice

def readGate (state : MiniRustReference.State) (handle : Handle) : MiniRustReference.Result Span :=
  match MiniRustReference.load state handle.pointer 2 2 with
  | .ok _ => checkedLocation state handle.pointer
  | .ub diagnostic => .ub diagnostic
  | .unsupported => .unsupported
  | .noChoice => .noChoice

def writeGate (state : MiniRustReference.State) (handle : Handle) : MiniRustReference.Result Span :=
  match MiniRustReference.store state handle.pointer oneBytes 2 with
  | .ok _ => checkedLocation state handle.pointer
  | .ub diagnostic => .ub diagnostic
  | .unsupported => .unsupported
  | .noChoice => .noChoice

inductive Gate (α : Type) where
  | ok (value : α)
  | ub (event : Event) (diagnostic : MiniRustReference.UB)
  | unsupported (event : Event)
  | noChoice (event : Event)

def atEvent (event : Event) (result : MiniRustReference.Result α) : Gate α :=
  match result with
  | .ok value => .ok value
  | .ub diagnostic => .ub event diagnostic
  | .unsupported => .unsupported event
  | .noChoice => .noChoice event

def bindGate (result : Gate α) (next : α → Gate β) : Gate β :=
  match result with
  | .ok value => next value
  | .ub event diagnostic => .ub event diagnostic
  | .unsupported event => .unsupported event
  | .noChoice event => .noChoice event

/-- Validation order on one fixed snapshot, not a concurrent store/load replay.
No updated writeGate state is passed to another operation. -/
def gates (state : MiniRustReference.State) (handles : Handles) : Gate Locations :=
  bindGate (atEvent .d (writeGate state handles.dataStore)) fun data =>
  bindGate (atEvent .f (writeGate state handles.flagStore)) fun flag =>
  bindGate (atEvent .a (readGate state handles.flagLoad)) fun observedFlag =>
  bindGate (atEvent .b (readGate state handles.dataLoad)) fun observedData =>
  .ok ⟨data, flag, observedFlag, observedData⟩

inductive CandidateResult where
  | observed (locations : Locations) (values : Nat × Nat)
  | outsideBranch (flagValue : Nat)
  | outsideGeometry (locations : Locations)
  | inconsistent (locations : Locations)
  | ordinaryUB (event : Event) (diagnostic : MiniRustReference.UB)
  | unsupported (event : Event)
  | noChoice (event : Event)

/-- Mathematical selected-candidate classifier. The A=0 case is filtered before
the four-event gates: it is not a model of that branch and does not execute B.
The fixed zero-initialization history is not established by arbitrary gate success.
Classical decisions avoid pretending that this is a checked source evaluator. -/
noncomputable def runCandidate (state : MiniRustReference.State) (handles : Handles)
    (mode : Mode) (rf : RF) : CandidateResult := by
  classical
  exact if flagValue rf = 1 then
    match gates state handles with
    | .ub event diagnostic => .ordinaryUB event diagnostic
    | .unsupported event => .unsupported event
    | .noChoice event => .noChoice event
    | .ok locations =>
        if Shape locations then
          if SelectedRules locations mode rf then .observed locations (returned rf)
          else .inconsistent locations
        else .outsideGeometry locations
    else .outsideBranch (flagValue rf)

theorem run_candidate_observed (state : MiniRustReference.State) (handles : Handles) (mode : Mode) (rf : RF)
    (locations : Locations) (one : flagValue rf = 1)
    (validated : gates state handles = .ok locations) (shape : Shape locations)
    (rules : SelectedRules locations mode rf) :
    runCandidate state handles mode rf = .observed locations (returned rf) := by
  simp [runCandidate, one, validated, shape, rules]

theorem run_candidate_ordinary_ub (state : MiniRustReference.State) (handles : Handles) (mode : Mode) (rf : RF)
    (event : Event) (diagnostic : MiniRustReference.UB) (one : flagValue rf = 1)
    (failed : gates state handles = .ub event diagnostic) :
    runCandidate state handles mode rf = .ordinaryUB event diagnostic := by
  simp [runCandidate, one, failed]

theorem run_candidate_unsupported (state : MiniRustReference.State) (handles : Handles) (mode : Mode) (rf : RF)
    (event : Event) (one : flagValue rf = 1)
    (failed : gates state handles = .unsupported event) :
    runCandidate state handles mode rf = .unsupported event := by
  simp [runCandidate, one, failed]

theorem flag_zero_outside (state : MiniRustReference.State) (handles : Handles) (mode : Mode) (rf : RF)
    (zero : flagValue rf = 0) : runCandidate state handles mode rf = .outsideBranch 0 := by
  simp [runCandidate, zero]

theorem ordinary_ub_mode_independent (state : MiniRustReference.State) (handles : Handles) (rf : RF)
    (event : Event) (diagnostic : MiniRustReference.UB) (one : flagValue rf = 1)
    (failed : gates state handles = .ub event diagnostic) (first second : Mode) :
    runCandidate state handles first rf = runCandidate state handles second rf := by
  rw [run_candidate_ordinary_ub state handles first rf event diagnostic one failed,
    run_candidate_ordinary_ub state handles second rf event diagnostic one failed]

def relabel (handles : Handles) (label : Nat → Nat) : Handles :=
  ⟨⟨handles.dataStore.pointer, label handles.dataStore.label⟩,
    ⟨handles.flagStore.pointer, label handles.flagStore.label⟩,
    ⟨handles.flagLoad.pointer, label handles.flagLoad.label⟩,
    ⟨handles.dataLoad.pointer, label handles.dataLoad.label⟩⟩

theorem gates_relabel (state : MiniRustReference.State) (handles : Handles) (label : Nat → Nat) :
    gates state (relabel handles label) = gates state handles := by
  rfl

theorem run_candidate_relabel (state : MiniRustReference.State) (handles : Handles) (label : Nat → Nat)
    (mode : Mode) (rf : RF) :
    runCandidate state (relabel handles label) mode rf = runCandidate state handles mode rf := by
  rfl

#print axioms mo_irreflexive
#print axioms mo_transitive
#print axioms mo_same_location
#print axioms mo_total_per_location
#print axioms hb_rank
#print axioms hb_acyclic
#print axioms no_read_hb_write
#print axioms relaxed_cut
#print axioms data_hb_read
#print axioms flag_supplier
#print axioms data_supplier
#print axioms flag_one_supplier
#print axioms rules_of_write_read
#print axioms ra_flag_one_data_one
#print axioms both_stores_rules
#print axioms relaxed_stale_rules
#print axioms witness_values
#print axioms latest_flag_one_data_one
#print axioms stale_not_latest
#print axioms sequentialSchedule
#print axioms sequential_both_stores_latest
#print axioms run_candidate_observed
#print axioms run_candidate_ordinary_ub
#print axioms run_candidate_unsupported
#print axioms flag_zero_outside
#print axioms ordinary_ub_mode_independent
#print axioms gates_relabel
#print axioms run_candidate_relabel

end AnnealResearch.AtomicMessagePassing
