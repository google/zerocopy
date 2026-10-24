import AnnealResearch.MiniRustFactored
import AnnealResearch.ReferenceInvariants

/-!
Coarse dead-data correspondence for the selected raw BasicMemory API only.
Same preserves next, the entire metadata map (including dead tombstones), and
every cell at every live allocation offset. Dead contents are ignored. Absent
cells are also ignored by Same: they were already unobservable through metadata
and reification. The normalizer itself changes ONLY explicitly dead entries.

No StateWF/access-success premise is used in primitive congruence. The normalizer
does not justify forgetting bytes after a Rust destructor, erasing a live secret,
changing permissions, removing a tombstone, or reusing an allocation ID. This
function-valued model gives no physical storage or running-time savings claim.
-/

namespace AnnealResearch.DeadData

open MiniRustReference (Byte Ptr Kind UB Result ExitResult)

abbrev State := MiniRustFactored.State
abbrev Metadata := MiniRustFactored.Metadata

structure Same (first second : State) : Prop where
  next_eq : first.next = second.next
  metadata_eq : first.metadata = second.metadata
  live_cells : ∀ id metadata, first.metadata id = some metadata → metadata.live = true →
    ∀ offset, first.cells id offset = second.cells id offset

theorem Same.refl (state : State) : Same state state := ⟨rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem Same.symm {first second : State} (same : Same first second) : Same second first := by
  refine ⟨same.next_eq.symm, same.metadata_eq.symm, ?_⟩
  intro id metadata found live offset
  have firstFound : first.metadata id = some metadata := by rw [same.metadata_eq]; exact found
  exact (same.live_cells id metadata firstFound live offset).symm

theorem Same.trans {first middle last : State} (one : Same first middle) (two : Same middle last) :
    Same first last := by
  refine ⟨one.next_eq.trans two.next_eq, one.metadata_eq.trans two.metadata_eq, ?_⟩
  intro id metadata found live offset
  have middleFound : middle.metadata id = some metadata := by rw [← one.metadata_eq]; exact found
  exact (one.live_cells id metadata found live offset).trans
    (two.live_cells id metadata middleFound live offset)

def normalize (state : State) : State :=
  { state with cells := fun id offset =>
      match state.metadata id with
      | none => state.cells id offset
      | some metadata => if metadata.live = false then .uninit else state.cells id offset }

theorem normalize_preserves_next (state : State) : (normalize state).next = state.next := rfl
theorem normalize_preserves_metadata (state : State) : (normalize state).metadata = state.metadata := rfl

theorem normalize_dead_cell (state : State) (id : Nat) (metadata : Metadata)
    (found : state.metadata id = some metadata) (dead : metadata.live = false) (offset : Nat) :
    (normalize state).cells id offset = .uninit := by simp [normalize, found, dead]

theorem normalize_absent_cell (state : State) (id : Nat) (absent : state.metadata id = none) (offset : Nat) :
    (normalize state).cells id offset = state.cells id offset := by simp [normalize, absent]

theorem normalize_same (state : State) : Same state (normalize state) := by
  refine ⟨rfl, rfl, ?_⟩
  intro id metadata found live offset
  simp [normalize, found, live]

inductive ResultRel {A B : Type} (values : A → B → Prop) : Result A → Result B → Prop where
  | ok {first second} (related : values first second) : ResultRel values (.ok first) (.ok second)
  | ub (error : UB) : ResultRel values (.ub error) (.ub error)
  | unsupported : ResultRel values .unsupported .unsupported
  | noChoice : ResultRel values .noChoice .noChoice

theorem resultRel_ite {A B : Type} {values : A → B → Prop} (condition : Prop) [Decidable condition]
    {firstYes firstNo : Result A} {secondYes secondNo : Result B}
    (yes : ResultRel values firstYes secondYes) (no : ResultRel values firstNo secondNo) :
    ResultRel values (if condition then firstYes else firstNo) (if condition then secondYes else secondNo) := by
  by_cases selected : condition <;> simp [selected] <;> assumption

theorem resultRel_map_right {A B C : Type} {values : A → B → Prop} {mapped : A → C → Prop}
    (f : B → C) (preserves : ∀ first second, values first second → mapped first (f second))
    {first : Result A} {second : Result B} (related : ResultRel values first second) :
    ResultRel mapped first (MiniRustFactored.resultMap f second) := by
  cases related with
  | ok related => exact ResultRel.ok (preserves _ _ related)
  | ub error => exact ResultRel.ub error
  | unsupported => exact ResultRel.unsupported
  | noChoice => exact ResultRel.noChoice

def BytesAndState (first second : List Byte × State) : Prop := first.1 = second.1 ∧ Same first.2 second.2
def PointerAndState (first second : Ptr × State) : Prop := first.1 = second.1 ∧ Same first.2 second.2

theorem resolve_same {first second : State} (same : Same first second) (pointer : Ptr) (length : Nat) :
    MiniRustFactored.resolve first pointer length = MiniRustFactored.resolve second pointer length := by
  simp only [MiniRustFactored.resolve, same.metadata_eq]

theorem resolved_live {state : State} {pointer : Ptr} {length : Nat} {span : MiniRustFactored.Span}
    (resolved : MiniRustFactored.resolve state pointer length = .ok (some span)) : span.metadata.live = true := by
  by_cases zero : length = 0
  · simp [MiniRustFactored.resolve, zero] at resolved
  · cases provenance : pointer.provenance with
    | none => simp [MiniRustFactored.resolve, zero, provenance] at resolved
    | some id =>
      cases found : state.metadata id with
      | none => simp [MiniRustFactored.resolve, zero, provenance, found] at resolved
      | some metadata =>
        by_cases dead : metadata.live = false
        · simp [MiniRustFactored.resolve, zero, provenance, found, dead] at resolved
        · by_cases below : pointer.addr < metadata.base
          · simp [MiniRustFactored.resolve, zero, provenance, found, dead, below] at resolved
          · by_cases beyond : metadata.size < pointer.addr - metadata.base + length
            · simp [MiniRustFactored.resolve, zero, provenance, found, dead, below, beyond] at resolved
            · have same : span = ⟨id, metadata, pointer.addr - metadata.base⟩ := by
                simpa [MiniRustFactored.resolve, zero, provenance, found, dead, below, beyond] using resolved.symm
              cases same
              cases live : metadata.live <;> simp_all

theorem readCells_same {first second : State} (same : Same first second)
    (id offset length : Nat) (metadata : Metadata)
    (found : first.metadata id = some metadata) (live : metadata.live = true) :
    MiniRustFactored.readCells first id offset length = MiniRustFactored.readCells second id offset length := by
  apply congrArg (fun cells : Fin length → Byte => List.ofFn cells)
  funext index
  exact same.live_cells id metadata found live (offset + index.val)

theorem writeCells_same {first second : State} (same : Same first second)
    (id offset : Nat) (bytes : List Byte) :
    Same (MiniRustFactored.writeCells first id offset bytes) (MiniRustFactored.writeCells second id offset bytes) := by
  refine ⟨same.next_eq, same.metadata_eq, ?_⟩
  intro current metadata found live index
  change first.metadata current = some metadata at found
  by_cases selected : current = id
  · by_cases inside : offset ≤ index ∧ index < offset + bytes.length
    · simp [MiniRustFactored.writeCells, selected, inside]
    · simpa [MiniRustFactored.writeCells, selected, inside] using
        same.live_cells current metadata found live index
  · simpa [MiniRustFactored.writeCells, selected] using same.live_cells current metadata found live index

theorem setDeadMetadata_same {first second : State} (same : Same first second)
    (id : Nat) (metadata : Metadata) (dead : metadata.live = false) :
    Same (MiniRustFactored.setMetadata first id metadata) (MiniRustFactored.setMetadata second id metadata) := by
  refine ⟨same.next_eq, ?_, ?_⟩
  · simp only [MiniRustFactored.setMetadata, same.metadata_eq]
  · intro current observed found live offset
    by_cases selected : current = id
    · subst current
      have equal : metadata = observed := by simpa [MiniRustFactored.setMetadata] using found
      subst observed
      rw [dead] at live
      cases live
    · have original : first.metadata current = some observed := by
        simpa [MiniRustFactored.setMetadata, selected] using found
      exact same.live_cells current observed original live offset

theorem append_same {first second : State} (same : Same first second) (metadata : Metadata) :
    Same (MiniRustFactored.append first metadata) (MiniRustFactored.append second metadata) := by
  refine ⟨by simp [MiniRustFactored.append, same.next_eq], ?_, ?_⟩
  · simp only [MiniRustFactored.append, same.next_eq, same.metadata_eq]
  · intro current observed found live offset
    by_cases selected : current = first.next
    · simp [MiniRustFactored.append, selected, same.next_eq]
    · have otherAbsent : current ≠ second.next := by rw [← same.next_eq]; exact selected
      have original : first.metadata current = some observed := by
        simpa [MiniRustFactored.append, selected] using found
      simpa [MiniRustFactored.append, selected, otherAbsent] using
        same.live_cells current observed original live offset

theorem load_same {first second : State} (same : Same first second) (pointer : Ptr) (length align : Nat) :
    ResultRel BytesAndState (MiniRustFactored.load first pointer length align)
      (MiniRustFactored.load second pointer length align) := by
  unfold MiniRustFactored.load
  apply resultRel_ite
  · exact ResultRel.unsupported
  · apply resultRel_ite
    · exact ResultRel.ub _
    · rw [resolve_same same pointer length]
      cases resolved : MiniRustFactored.resolve second pointer length with
      | ub error => exact ResultRel.ub error
      | unsupported => exact ResultRel.unsupported
      | noChoice => exact ResultRel.noChoice
      | ok optional =>
        cases optional with
        | none => exact ResultRel.ok ⟨rfl, same⟩
        | some span =>
          have found : first.metadata span.id = some span.metadata := by
            rw [same.metadata_eq]
            exact MiniRustFactored.resolve_metadata resolved
          exact ResultRel.ok ⟨readCells_same same _ _ _ _ found (resolved_live resolved), same⟩

theorem store_same {first second : State} (same : Same first second) (pointer : Ptr) (bytes : List Byte) (align : Nat) :
    ResultRel Same (MiniRustFactored.store first pointer bytes align)
      (MiniRustFactored.store second pointer bytes align) := by
  unfold MiniRustFactored.store
  apply resultRel_ite
  · exact ResultRel.unsupported
  · apply resultRel_ite
    · exact ResultRel.ub _
    · rw [resolve_same same pointer bytes.length]
      cases resolved : MiniRustFactored.resolve second pointer bytes.length with
      | ub error => exact ResultRel.ub error
      | unsupported => exact ResultRel.unsupported
      | noChoice => exact ResultRel.noChoice
      | ok optional =>
        cases optional with
        | none => exact ResultRel.ok same
        | some span => exact ResultRel.ok (writeCells_same same _ _ _)

theorem free_same {first second : State} (same : Same first second) (pointer : Ptr)
    (kind : Kind) (size align : Nat) :
    ResultRel Same (MiniRustFactored.free first pointer kind size align)
      (MiniRustFactored.free second pointer kind size align) := by
  unfold MiniRustFactored.free
  rw [← same.metadata_eq]
  cases provenance : pointer.provenance with
  | none => exact ResultRel.ub _
  | some id =>
    cases found : first.metadata id with
    | none =>
      simp only [found]
      exact ResultRel.unsupported
    | some metadata =>
      simp only [found]
      apply resultRel_ite
      · exact ResultRel.ub _
      · apply resultRel_ite
        · exact ResultRel.ub _
        · apply resultRel_ite
          · exact ResultRel.ub _
          · apply resultRel_ite
            · exact ResultRel.ub _
            · apply resultRel_ite
              · exact ResultRel.ub _
              · exact ResultRel.ok (setDeadMetadata_same same id { metadata with live := false } rfl)

theorem liveOverlap_same {first second : State} (same : Same first second) (base size : Nat) :
    MiniRustFactored.liveOverlap first base size = MiniRustFactored.liveOverlap second base size := by
  simp only [MiniRustFactored.liveOverlap, same.next_eq, same.metadata_eq]

theorem allocationCandidate_same {first second : State} (same : Same first second) (size align address : Nat) :
    MiniRustFactored.AllocationCandidate first size align address ↔
      MiniRustFactored.AllocationCandidate second size align address := by
  simp only [MiniRustFactored.AllocationCandidate, liveOverlap_same same]

theorem allocateAt_same {first second : State} (same : Same first second)
    (kind : Kind) (size align address : Nat) :
    ResultRel PointerAndState (MiniRustFactored.allocateAt first kind size align address)
      (MiniRustFactored.allocateAt second kind size align address) := by
  unfold MiniRustFactored.allocateAt
  apply resultRel_ite
  · exact ResultRel.ub _
  · apply resultRel_ite
    · exact ResultRel.unsupported
    · by_cases candidate : MiniRustFactored.AllocationCandidate first size align address
      · have otherCandidate : MiniRustFactored.AllocationCandidate second size align address :=
          (allocationCandidate_same same size align address).mp candidate
        simp only [ite_eq_left candidate, ite_eq_left otherCandidate]
        exact ResultRel.ok ⟨by simp [same.next_eq], append_same same _⟩
      · have otherCandidate : ¬ MiniRustFactored.AllocationCandidate second size align address :=
          fun observed => candidate ((allocationCandidate_same same size align address).mpr observed)
        simp only [ite_eq_right candidate, ite_eq_right otherCandidate]
        exact ResultRel.noChoice

theorem dereferenceable_same {first second : State} (same : Same first second) (pointer : Ptr) (length : Nat) :
    MiniRustFactored.dereferenceable first pointer length = MiniRustFactored.dereferenceable second pointer length := by
  simp only [MiniRustFactored.dereferenceable, resolve_same same]

theorem exit_same {first second : State} (same : Same first second) :
    MiniRustFactored.exit first = MiniRustFactored.exit second := by
  simp only [MiniRustFactored.exit, same.next_eq, same.metadata_eq]

/-- The erasing target executes the actual factored primitives and normalizes
only successful resulting states. Error categories and absent choices are kept. -/
def load (state : State) (pointer : Ptr) (length align : Nat) : Result (List Byte × State) :=
  MiniRustFactored.resultMap (fun value => (value.1, normalize value.2))
    (MiniRustFactored.load state pointer length align)
def store (state : State) (pointer : Ptr) (bytes : List Byte) (align : Nat) : Result State :=
  MiniRustFactored.resultMap normalize (MiniRustFactored.store state pointer bytes align)
def free (state : State) (pointer : Ptr) (kind : Kind) (size align : Nat) : Result State :=
  MiniRustFactored.resultMap normalize (MiniRustFactored.free state pointer kind size align)
def allocateAt (state : State) (kind : Kind) (size align address : Nat) : Result (Ptr × State) :=
  MiniRustFactored.resultMap (fun value => (value.1, normalize value.2))
    (MiniRustFactored.allocateAt state kind size align address)

theorem load_agreement {first second : State} (same : Same first second) (pointer : Ptr) (length align : Nat) :
    ResultRel BytesAndState (MiniRustFactored.load first pointer length align) (load second pointer length align) :=
  resultRel_map_right (values := BytesAndState) (mapped := BytesAndState)
    (fun value : List Byte × State => (value.1, normalize value.2))
    (fun _ _ related => ⟨related.1, related.2.trans (normalize_same _)⟩)
    (load_same same pointer length align)

theorem store_agreement {first second : State} (same : Same first second) (pointer : Ptr) (bytes : List Byte) (align : Nat) :
    ResultRel Same (MiniRustFactored.store first pointer bytes align) (store second pointer bytes align) :=
  resultRel_map_right (values := Same) (mapped := Same) normalize
    (fun _ _ related => related.trans (normalize_same _)) (store_same same pointer bytes align)

theorem free_agreement {first second : State} (same : Same first second) (pointer : Ptr) (kind : Kind) (size align : Nat) :
    ResultRel Same (MiniRustFactored.free first pointer kind size align) (free second pointer kind size align) :=
  resultRel_map_right (values := Same) (mapped := Same) normalize
    (fun _ _ related => related.trans (normalize_same _)) (free_same same pointer kind size align)

theorem allocateAt_agreement {first second : State} (same : Same first second) (kind : Kind) (size align address : Nat) :
    ResultRel PointerAndState (MiniRustFactored.allocateAt first kind size align address) (allocateAt second kind size align address) :=
  resultRel_map_right (values := PointerAndState) (mapped := PointerAndState)
    (fun value : Ptr × State => (value.1, normalize value.2))
    (fun _ _ related => ⟨related.1, related.2.trans (normalize_same _)⟩)
    (allocateAt_same same kind size align address)

#print axioms normalize_same
#print axioms load_same
#print axioms store_same
#print axioms free_same
#print axioms allocateAt_same
#print axioms dereferenceable_same
#print axioms exit_same
#print axioms load_agreement
#print axioms store_agreement
#print axioms free_agreement
#print axioms allocateAt_agreement

end AnnealResearch.DeadData
