import AnnealResearch.MiniRustReference

/-!
Independent factored implementation of the admitted raw BasicMemory subset.
Metadata and byte cells live in separate maps. The target evaluators do not call
the reference pointer checker, evaluators, overlap test, or update functions.
Only the data types, result/error tags, constants, and ordinary list operations
are shared. Correspondence proves agreement with an audited transcription; it
does not establish that either transcription is adequate for Rust or MiniRust.

No global well-formedness assumption is used. Unsupported representations and
all error precedence are compared too. Allocation quantifies every candidate
base; an invalid candidate is noChoice, and contributes no allocation branch.
-/

namespace AnnealResearch.MiniRustFactored

open MiniRustReference (Byte Ptr Kind UB Result ExitResult addressLimit sizeLimit)

structure Metadata where
  base : Nat
  size : Nat
  align : Nat
  kind : Kind
  live : Bool

structure State where
  next : Nat
  metadata : Nat → Option Metadata
  cells : Nat → Nat → Byte

def empty : State :=
  { next := 0, metadata := fun _ => none, cells := fun _ _ => .uninit }

def resultMap (f : α → β) : Result α → Result β
  | .ok value => .ok (f value)
  | .ub error => .ub error
  | .noChoice => .noChoice
  | .unsupported => .unsupported

@[simp] theorem resultMap_ok (f : α → β) (value : α) :
    resultMap f (.ok value) = .ok (f value) := rfl
@[simp] theorem resultMap_ub (f : α → β) (error : UB) :
    resultMap f (.ub error) = .ub error := rfl
@[simp] theorem resultMap_noChoice (f : α → β) :
    resultMap f .noChoice = .noChoice := rfl
@[simp] theorem resultMap_unsupported (f : α → β) :
    resultMap f .unsupported = .unsupported := rfl
@[simp] theorem resultMap_ite (f : α → β) (condition : Prop) [Decidable condition]
    (yes no : Result α) :
    resultMap f (if condition then yes else no) =
      if condition then resultMap f yes else resultMap f no := by
  split <;> rfl

def materialize (metadata : Metadata) (cells : Nat → Byte) :
    MiniRustReference.Allocation :=
  { base := metadata.base, size := metadata.size, align := metadata.align
    kind := metadata.kind, live := metadata.live, data := cells }

def metadataOf (allocation : MiniRustReference.Allocation) : Metadata :=
  { base := allocation.base, size := allocation.size, align := allocation.align
    kind := allocation.kind, live := allocation.live }

def reify (state : State) : MiniRustReference.State :=
  { next := state.next
    allocations := fun id => (state.metadata id).map fun metadata =>
      materialize metadata (state.cells id) }

def encode (state : MiniRustReference.State) : State :=
  { next := state.next
    metadata := fun id => (state.allocations id).map metadataOf
    cells := fun id =>
      match state.allocations id with
      | none => fun _ => .uninit
      | some allocation => allocation.data }

def Related (source : MiniRustReference.State) (target : State) : Prop :=
  source = reify target

private theorem reference_ext {first second : MiniRustReference.State}
    (nextEq : first.next = second.next)
    (entries : ∀ id, first.allocations id = second.allocations id) : first = second := by
  cases first with
  | mk firstNext firstAllocations =>
    cases second with
    | mk secondNext secondAllocations =>
      change firstNext = secondNext at nextEq
      change ∀ id, firstAllocations id = secondAllocations id at entries
      cases nextEq
      exact congrArg (MiniRustReference.State.mk firstNext) (funext entries)

theorem reify_encode (state : MiniRustReference.State) : reify (encode state) = state := by
  refine reference_ext ?_ ?_
  · rfl
  · intro id
    cases found : state.allocations id with
    | none => simp [reify, encode, found]
    | some allocation =>
      cases allocation
      simp [reify, encode, found, materialize, metadataOf]

@[simp] theorem reify_next (state : State) : (reify state).next = state.next := rfl

theorem reify_lookup (state : State) (id : Nat) :
    (reify state).allocations id =
      (state.metadata id).map (fun metadata => materialize metadata (state.cells id)) := rfl

/-- Metadata-only resolution keeps byte storage out of access validation. -/
structure Span where
  id : Nat
  metadata : Metadata
  offset : Nat

def resolve (state : State) (pointer : Ptr) (length : Nat) : Result (Option Span) :=
  if length = 0 then .ok none
  else
    match pointer.provenance with
    | none => .ub .noProvenance
    | some id =>
      match state.metadata id with
      | none => .unsupported
      | some metadata =>
        if metadata.live = false then .ub .dead
        else if pointer.addr < metadata.base then .ub .bounds
        else
          let offset := pointer.addr - metadata.base
          if metadata.size < offset + length then .ub .bounds
          else .ok (some { id, metadata, offset })

def readCells (state : State) (id offset length : Nat) : List Byte :=
  List.ofFn fun i : Fin length => state.cells id (offset + i.val)

def writeCells (state : State) (id offset : Nat) (bytes : List Byte) : State :=
  { state with cells := fun current index =>
      if current = id then
        if offset ≤ index ∧ index < offset + bytes.length then
          bytes.getD (index - offset) .uninit
        else state.cells current index
      else state.cells current index }

def setMetadata (state : State) (id : Nat) (metadata : Metadata) : State :=
  { state with metadata := fun current =>
      if current = id then some metadata else state.metadata current }

/-- Fresh IDs are the old count, including when dead records remain present. -/
def append (state : State) (metadata : Metadata) : State :=
  { next := state.next + 1
    metadata := fun id => if id = state.next then some metadata else state.metadata id
    cells := fun id => if id = state.next then fun _ => .uninit else state.cells id }

def load (state : State) (pointer : Ptr) (length align : Nat) :
    Result (List Byte × State) :=
  if align = 0 then .unsupported
  else if pointer.addr % align ≠ 0 then .ub .misalignedLoad
  else
    match resolve state pointer length with
    | .ok none => .ok ([], state)
    | .ok (some span) => .ok (readCells state span.id span.offset length, state)
    | .ub error => .ub error
    | .noChoice => .noChoice
    | .unsupported => .unsupported

def store (state : State) (pointer : Ptr) (bytes : List Byte) (align : Nat) :
    Result State :=
  if align = 0 then .unsupported
  else if pointer.addr % align ≠ 0 then .ub .misalignedStore
  else
    match resolve state pointer bytes.length with
    | .ok none => .ok state
    | .ok (some span) => .ok (writeCells state span.id span.offset bytes)
    | .ub error => .ub error
    | .noChoice => .noChoice
    | .unsupported => .unsupported

def free (state : State) (pointer : Ptr) (kind : Kind) (size align : Nat) : Result State :=
  match pointer.provenance with
  | none => .ub .freeNoProvenance
  | some id =>
    match state.metadata id with
    | none => .unsupported
    | some metadata =>
      if metadata.live = false then .ub .doubleFree
      else if pointer.addr ≠ metadata.base then .ub .freeNotBase
      else if kind ≠ metadata.kind then .ub .freeKind
      else if size ≠ metadata.size then .ub .freeSize
      else if align ≠ metadata.align then .ub .freeAlign
      else .ok (setMetadata state id { metadata with live := false })

def overlaps (metadata : Metadata) (base size : Nat) : Prop :=
  metadata.base = base ∨
    ¬ (metadata.base + metadata.size ≤ base ∨ base + size ≤ metadata.base)

instance (metadata : Metadata) (base size : Nat) : Decidable (overlaps metadata base size) := by
  unfold overlaps
  infer_instance

def liveOverlap (state : State) (base size : Nat) : Bool :=
  (List.range state.next).any fun id =>
    match state.metadata id with
    | none => false
    | some metadata => metadata.live && decide (overlaps metadata base size)

def AllocationCandidate (state : State) (size align address : Nat) : Prop :=
  0 < address ∧ address % align = 0 ∧ address + size < addressLimit ∧
    liveOverlap state address size = false

instance (state : State) (size align address : Nat) :
    Decidable (AllocationCandidate state size align address) := by
  unfold AllocationCandidate
  infer_instance

def allocateAt (state : State) (kind : Kind) (size align address : Nat) :
    Result (Ptr × State) :=
  if sizeLimit ≤ size then .ub .allocationTooLarge
  else if align = 0 then .unsupported
  else if AllocationCandidate state size align address then
    .ok ({ addr := address, provenance := some state.next },
      append state { base := address, size, align, kind, live := true })
  else .noChoice

def Allocate (state : State) (kind : Kind) (size align : Nat)
    (result : Result (Ptr × State)) : Prop :=
  result ≠ .noChoice ∧ ∃ address, allocateAt state kind size align address = result

def dereferenceable (state : State) (pointer : Ptr) (length : Nat) : Result Unit :=
  match resolve state pointer length with
  | .ok _ => .ok ()
  | .ub error => .ub error
  | .noChoice => .noChoice
  | .unsupported => .unsupported

def exit (state : State) : ExitResult :=
  if (List.range state.next).any (fun id =>
      match state.metadata id with
      | none => false
      | some metadata => metadata.live && decide (metadata.kind = .heap)) then
    .memoryLeak
  else .machineStop

def reifySpan (state : State) (span : Span) : MiniRustReference.CheckedSpan :=
  { id := span.id, allocation := materialize span.metadata (state.cells span.id)
    offset := span.offset }

theorem resolve_reify (state : State) (pointer : Ptr) (length : Nat) :
    MiniRustReference.checkPtr (reify state) pointer length =
      resultMap (Option.map (reifySpan state)) (resolve state pointer length) := by
  by_cases zero : length = 0
  · simp [MiniRustReference.checkPtr, resolve, zero]
  · cases provenance : pointer.provenance with
    | none => simp [MiniRustReference.checkPtr, resolve, zero, provenance]
    | some id =>
      cases found : state.metadata id with
      | none => simp [MiniRustReference.checkPtr, resolve, zero, provenance, reify_lookup, found]
      | some metadata =>
        by_cases dead : metadata.live = false <;>
          by_cases below : pointer.addr < metadata.base <;>
          by_cases beyond : metadata.size < pointer.addr - metadata.base + length <;>
          simp [MiniRustReference.checkPtr, resolve, zero, provenance, reify_lookup,
            found, materialize, dead, below, beyond, reifySpan]

theorem resolve_metadata {state : State} {pointer : Ptr} {length : Nat} {span : Span}
    (resolved : resolve state pointer length = .ok (some span)) :
    state.metadata span.id = some span.metadata := by
  by_cases zero : length = 0
  · simp [resolve, zero] at resolved
  · cases provenance : pointer.provenance with
    | none => simp [resolve, zero, provenance] at resolved
    | some id =>
      cases found : state.metadata id with
      | none => simp [resolve, zero, provenance, found] at resolved
      | some metadata =>
        by_cases dead : metadata.live = false
        · simp [resolve, zero, provenance, found, dead] at resolved
        · by_cases below : pointer.addr < metadata.base
          · simp [resolve, zero, provenance, found, dead, below] at resolved
          · by_cases beyond : metadata.size < pointer.addr - metadata.base + length
            · simp [resolve, zero, provenance, found, dead, below, beyond] at resolved
            · have same : span = { id, metadata, offset := pointer.addr - metadata.base } := by
                simpa [resolve, zero, provenance, found, dead, below, beyond] using resolved.symm
              cases same
              exact found

theorem reify_writeCells (state : State) (id : Nat) (metadata : Metadata)
    (offset : Nat) (bytes : List Byte) (found : state.metadata id = some metadata) :
    reify (writeCells state id offset bytes) =
      MiniRustReference.replace (reify state) id
        { materialize metadata (state.cells id) with data := (fun index =>
            if offset ≤ index ∧ index < offset + bytes.length then
              bytes.getD (index - offset) .uninit
            else state.cells id index) } := by
  refine reference_ext ?_ ?_
  · rfl
  · intro current
    by_cases same : current = id
    · subst current
      simp [reify, writeCells, MiniRustReference.replace, found, materialize]
    · simp [reify, writeCells, MiniRustReference.replace, same, materialize]

theorem reify_setMetadata (state : State) (id : Nat) (metadata : Metadata) :
    reify (setMetadata state id metadata) =
      MiniRustReference.replace (reify state) id (materialize metadata (state.cells id)) := by
  refine reference_ext ?_ ?_
  · rfl
  · intro current
    by_cases same : current = id
    · subst current
      simp [reify, setMetadata, MiniRustReference.replace]
    · simp [reify, setMetadata, MiniRustReference.replace, same]

theorem reify_append (state : State) (metadata : Metadata) :
    reify (append state metadata) =
      MiniRustReference.append (reify state) (materialize metadata (fun _ => .uninit)) := by
  refine reference_ext ?_ ?_
  · rfl
  · intro id
    by_cases same : id = state.next
    · simp [reify, append, MiniRustReference.append, same]
    · simp [reify, append, MiniRustReference.append, same]

theorem load_reify (state : State) (pointer : Ptr) (length align : Nat) :
    MiniRustReference.load (reify state) pointer length align =
      resultMap (fun value : List Byte × State => (value.1, reify value.2))
        (load state pointer length align) := by
  by_cases invalid : align = 0
  · simp [MiniRustReference.load, load, invalid]
  · by_cases misaligned : pointer.addr % align ≠ 0
    · simp [MiniRustReference.load, load, invalid, misaligned]
    · simp only [MiniRustReference.load, load, ite_eq_right invalid, ite_eq_right misaligned]
      rw [resolve_reify]
      cases resolved : resolve state pointer length with
      | ok optional => cases optional <;> rfl
      | ub error => rfl
      | noChoice => rfl
      | unsupported => rfl

theorem store_reify (state : State) (pointer : Ptr) (bytes : List Byte) (align : Nat) :
    MiniRustReference.store (reify state) pointer bytes align =
      resultMap reify (store state pointer bytes align) := by
  by_cases invalid : align = 0
  · simp [MiniRustReference.store, store, invalid]
  · by_cases misaligned : pointer.addr % align ≠ 0
    · simp [MiniRustReference.store, store, invalid, misaligned]
    · simp only [MiniRustReference.store, store, ite_eq_right invalid, ite_eq_right misaligned]
      rw [resolve_reify]
      cases resolved : resolve state pointer bytes.length with
      | ok optional =>
        cases optional with
        | none => rfl
        | some span =>
          have found := resolve_metadata resolved
          exact congrArg Result.ok
            (reify_writeCells state span.id span.metadata span.offset bytes found).symm
      | ub error => rfl
      | noChoice => rfl
      | unsupported => rfl

theorem free_reify (state : State) (pointer : Ptr) (kind : Kind) (size align : Nat) :
    MiniRustReference.free (reify state) pointer kind size align =
      resultMap reify (free state pointer kind size align) := by
  cases provenance : pointer.provenance with
  | none => simp [MiniRustReference.free, free, provenance]
  | some id =>
    cases found : state.metadata id with
    | none => simp [MiniRustReference.free, free, provenance, reify_lookup, found]
    | some metadata =>
      simp [MiniRustReference.free, free, provenance, reify_lookup, found,
        materialize, reify_setMetadata]

theorem liveOverlap_reify (state : State) (base size : Nat) :
    MiniRustReference.liveOverlap (reify state) base size = liveOverlap state base size := by
  unfold MiniRustReference.liveOverlap liveOverlap
  apply congrArg (fun test => (List.range state.next).any test)
  funext id
  cases found : state.metadata id <;>
    simp [reify_lookup, found, MiniRustReference.overlaps, overlaps, materialize]

theorem allocationCandidate_reify (state : State) (size align address : Nat) :
    MiniRustReference.AllocationCandidate (reify state) size align address ↔
      AllocationCandidate state size align address := by
  simp [MiniRustReference.AllocationCandidate, AllocationCandidate, liveOverlap_reify]

theorem allocateAt_reify (state : State) (kind : Kind) (size align address : Nat) :
    MiniRustReference.allocateAt (reify state) kind size align address =
      resultMap (fun value : Ptr × State => (value.1, reify value.2))
        (allocateAt state kind size align address) := by
  simp [MiniRustReference.allocateAt, allocateAt, allocationCandidate_reify,
    reify_append, materialize]

theorem dereferenceable_reify (state : State) (pointer : Ptr) (length : Nat) :
    MiniRustReference.dereferenceable (reify state) pointer length =
      dereferenceable state pointer length := by
  unfold MiniRustReference.dereferenceable dereferenceable
  rw [resolve_reify]
  cases resolved : resolve state pointer length with
  | ok optional => cases optional <;> rfl
  | ub error => rfl
  | noChoice => rfl
  | unsupported => rfl

theorem exit_reify (state : State) : MiniRustReference.exit (reify state) = exit state := by
  have tests :
      (List.range (reify state).next).any (fun id =>
        match (reify state).allocations id with
        | none => false
        | some allocation => allocation.live && decide (allocation.kind = .heap)) =
      (List.range state.next).any (fun id =>
        match state.metadata id with
        | none => false
        | some metadata => metadata.live && decide (metadata.kind = .heap)) := by
    rw [reify_next]
    apply congrArg (fun test => (List.range state.next).any test)
    funext id
    cases found : state.metadata id <;> simp [reify_lookup, found, materialize]
  unfold MiniRustReference.exit exit
  split
  · rename_i sourceLeaks
    have targetLeaks := tests.symm.trans sourceLeaks
    simp only [ite_eq_left targetLeaks]
  · rename_i sourceNoLeaks
    have targetNoLeaks := fun targetLeaks => sourceNoLeaks (tests.trans targetLeaks)
    simp only [ite_eq_right targetNoLeaks]

@[simp] theorem resultMap_eq_noChoice (f : α → β) (result : Result α) :
    resultMap f result = .noChoice ↔ result = .noChoice := by
  cases result <;> simp [resultMap]

theorem Allocate_reify {state : State} {kind : Kind} {size align : Nat}
    {result : Result (Ptr × State)} (branch : Allocate state kind size align result) :
    MiniRustReference.Allocate (reify state) kind size align
      (resultMap (fun value : Ptr × State => (value.1, reify value.2)) result) := by
  obtain ⟨present, address, selected⟩ := branch
  refine ⟨?_, address, ?_⟩
  · intro absent
    exact present ((resultMap_eq_noChoice _ result).mp absent)
  · rw [allocateAt_reify, selected]

theorem Allocate_coverage {state : State} {kind : Kind} {size align : Nat}
    {result : Result (Ptr × MiniRustReference.State)}
    (branch : MiniRustReference.Allocate (reify state) kind size align result) :
    ∃ targetResult, Allocate state kind size align targetResult ∧
      result = resultMap (fun value : Ptr × State => (value.1, reify value.2)) targetResult := by
  obtain ⟨present, address, selected⟩ := branch
  refine ⟨allocateAt state kind size align address, ⟨?_, address, rfl⟩, ?_⟩
  · intro absent
    apply present
    rw [← selected, allocateAt_reify, absent, resultMap_noChoice]
  · exact selected.symm.trans (allocateAt_reify state kind size align address)

theorem append_fresh (state : State) (metadata : Metadata) :
    (append state metadata).next = state.next + 1 ∧
    (append state metadata).metadata state.next = some metadata := by
  simp [append]

#print axioms reify_encode
#print axioms resolve_reify
#print axioms load_reify
#print axioms store_reify
#print axioms free_reify
#print axioms allocateAt_reify
#print axioms dereferenceable_reify
#print axioms exit_reify
#print axioms Allocate_reify
#print axioms Allocate_coverage

end AnnealResearch.MiniRustFactored
