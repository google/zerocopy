import AnnealResearch.ProgramCostCommon

/-!
Shared raw-memory facts for the program-specific proof-cost pilot.
Live support ranges over every actual ID, independently of next. ByteAt is a
description of one raw heap record, not Rust ownership or a permission assertion.
No theorem here proves a Plan safe or proves a whole program's resource clause.
-/
namespace AnnealResearch.ProgramCostPrimitives

open MiniRustReference ProgramCostCommon

/-- Every actual live record has an ID in support, including records above next. -/
def LiveOnly (memory : State) (support : Nat → Prop) : Prop :=
  ∀ id allocation, memory.allocations id = some allocation →
    allocation.live = true → support id

/-- This is separate bookkeeping, not a claim that the raw map has no other records. -/
def SupportBelow (memory : State) (support : Nat → Prop) : Prop :=
  ∀ id, support id → id < memory.next

theorem noLive_iff_liveOnly_empty (memory : State) :
    NoLive memory ↔ LiveOnly memory (fun _ => False) := by
  constructor
  · intro dead id allocation found live
    have notLive := dead id allocation found
    rw [notLive] at live
    cases live
  · intro supported id allocation found
    cases live : allocation.live with
    | false => rfl
    | true => exact False.elim (supported id allocation found live)

theorem empty_liveOnly : LiveOnly empty (fun _ => False) := by
  intro id allocation found
  simp [empty] at found

theorem liveOnly_mono {memory : State} {first second : Nat → Prop}
    (supported : LiveOnly memory first) (included : ∀ id, first id → second id) :
    LiveOnly memory second := by
  intro id allocation found live
  exact included id (supported id allocation found live)

theorem append_liveOnly {memory : State} {support : Nat → Prop}
    (supported : LiveOnly memory support) (fresh : Allocation) :
    LiveOnly (append memory fresh) (fun id => id = memory.next ∨ support id) := by
  intro id allocation found live
  by_cases selected : id = memory.next
  · exact Or.inl selected
  · exact Or.inr (supported id allocation (by simpa [append, selected] using found) live)

theorem replace_liveOnly_same_live {memory : State} {support : Nat → Prop}
    {id : Nat} {old fresh : Allocation} (supported : LiveOnly memory support)
    (found : memory.allocations id = some old) (sameLive : fresh.live = old.live) :
    LiveOnly (replace memory id fresh) support := by
  intro current allocation selectedFound live
  by_cases selected : current = id
  · subst current
    have same : fresh = allocation := Option.some.inj (by simpa [replace] using selectedFound)
    subst allocation
    rw [sameLive] at live
    exact supported id old found live
  · exact supported current allocation
      (by simpa [replace, selected] using selectedFound) live

/-- Both zero-length identity and positive-length data replacement are covered. -/
theorem store_preserves_liveOnly {before after : State} {support : Nat → Prop}
    {p : Ptr} {bytes : List Byte} {align : Nat}
    (supported : LiveOnly before support)
    (success : store before p bytes align = .ok after) : LiveOnly after support := by
  by_cases zeroAlign : align = 0
  · simp [store, zeroAlign] at success
  by_cases misaligned : p.addr % align ≠ 0
  · simp [store, zeroAlign, misaligned] at success
  simp only [store, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
  cases checked : checkPtr before p bytes.length with
  | ub error => simp [checked] at success
  | noChoice => simp [checked] at success
  | unsupported => simp [checked] at success
  | ok span =>
    cases span with
    | none =>
      simp only [checked] at success
      have same := Result.ok.inj success
      rw [← same]
      exact supported
    | some span =>
      have found := checkPtr_some_lookup checked
      simp only [checked] at success
      have same := Result.ok.inj success
      rw [← same]
      exact replace_liveOnly_same_live supported found rfl

/-- The successful raw load carries its unchanged input state, for every length. -/
theorem load_success_memory {before after : State} {p : Ptr} {len align : Nat}
    {bytes : List Byte} (success : load before p len align = .ok (bytes, after)) :
    after = before := by
  by_cases zeroAlign : align = 0
  · simp [load, zeroAlign] at success
  by_cases misaligned : p.addr % align ≠ 0
  · simp [load, zeroAlign, misaligned] at success
  simp only [load, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
  cases checked : checkPtr before p len with
  | ub error => simp [checked] at success
  | noChoice => simp [checked] at success
  | unsupported => simp [checked] at success
  | ok span =>
    cases span <;> simp only [checked] at success <;>
      exact (congrArg Prod.snd (Result.ok.inj success)).symm

theorem load_preserves_liveOnly {before after : State} {support : Nat → Prop}
    {p : Ptr} {len align : Nat} {bytes : List Byte}
    (supported : LiveOnly before support)
    (success : load before p len align = .ok (bytes, after)) : LiveOnly after support := by
  rw [load_success_memory success]
  exact supported

/-- Known provenance identifies the record killed by the actual successful free. -/
theorem free_selected_shape {before after : State} {p : Ptr}
    {id size align : Nat} {kind : Kind} (provenance : p.provenance = some id)
    (success : free before p kind size align = .ok after) :
    ∃ allocation, before.allocations id = some allocation ∧
      after = replace before id { allocation with live := false } := by
  cases found : before.allocations id with
  | none => simp [free, provenance, found] at success
  | some allocation =>
    simp only [free, provenance, found] at success
    split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · cases success
          · split at success
            · cases success
            · exact ⟨allocation, rfl, (Result.ok.inj success).symm⟩

theorem free_removes_liveOnly {before after : State} {support : Nat → Prop}
    {p : Ptr} {id size align : Nat} {kind : Kind}
    (supported : LiveOnly before support) (provenance : p.provenance = some id)
    (success : free before p kind size align = .ok after) :
    LiveOnly after (fun current => support current ∧ current ≠ id) := by
  obtain ⟨old, _, rfl⟩ := free_selected_shape provenance success
  intro current allocation found live
  by_cases selected : current = id
  · subst current
    have same : { old with live := false } = allocation :=
      Option.some.inj (by simpa [replace] using found)
    subst allocation
    cases live
  · exact ⟨supported current allocation (by simpa [replace, selected] using found) live,
      selected⟩

theorem empty_supportBelow : SupportBelow empty (fun _ => False) := by
  intro id impossible
  exact False.elim impossible

theorem append_supportBelow {memory : State} {support : Nat → Prop}
    (bounded : SupportBelow memory support) (fresh : Allocation) :
    SupportBelow (append memory fresh) (fun id => id = memory.next ∨ support id) := by
  intro id member
  rcases member with same | old
  · subst id
    exact Nat.lt_succ_self memory.next
  · exact Nat.lt_trans (bounded id old) (Nat.lt_succ_self memory.next)

theorem store_preserves_supportBelow {before after : State} {support : Nat → Prop}
    {p : Ptr} {bytes : List Byte} {align : Nat}
    (bounded : SupportBelow before support)
    (success : store before p bytes align = .ok after) : SupportBelow after support := by
  intro id member
  rw [ProofCostFrames.store_preserves_next success]
  exact bounded id member

theorem free_preserves_supportBelow {before after : State} {support : Nat → Prop}
    {p : Ptr} {kind : Kind} {size align : Nat}
    (bounded : SupportBelow before support)
    (success : free before p kind size align = .ok after) : SupportBelow after support := by
  intro id member
  rw [free_preserves_next success]
  exact bounded id member

theorem supported_ne_next {memory : State} {support : Nat → Prop} {id : Nat}
    (bounded : SupportBelow memory support) (member : support id) : id ≠ memory.next :=
  Nat.ne_of_lt (bounded id member)

/-- Raw metadata and the byte at offset zero; no global memory WF is asserted. -/
def ByteAt (memory : State) (p : Ptr) (id : Nat) (value : Byte) : Prop :=
  p.provenance = some id ∧ ∃ allocation,
    memory.allocations id = some allocation ∧ p.addr = allocation.base ∧
    allocation.kind = .heap ∧ allocation.size = 1 ∧ allocation.align = 1 ∧
    allocation.live = true ∧ allocation.data 0 = value

/-- Written in the raw kernel's data-update form, retaining every other offset. -/
def writeByte (allocation : Allocation) (value : Byte) : Allocation :=
  { allocation with data := fun index =>
      if 0 ≤ index ∧ index < 0 + [value].length then
        [value].getD (index - 0) .uninit
      else allocation.data index }

theorem oneByte_check {memory : State} {p : Ptr} {id : Nat} {allocation : Allocation}
    (provenance : p.provenance = some id)
    (found : memory.allocations id = some allocation) (base : p.addr = allocation.base)
    (live : allocation.live = true) (size : allocation.size = 1) :
    checkPtr memory p 1 = .ok (some ⟨id, allocation, 0⟩) := by
  simp [checkPtr, provenance, found, base, live, size]

theorem oneByte_store {memory : State} {p : Ptr} {id : Nat} {allocation : Allocation}
    (provenance : p.provenance = some id)
    (found : memory.allocations id = some allocation) (base : p.addr = allocation.base)
    (live : allocation.live = true) (size : allocation.size = 1) (value : Byte) :
    store memory p [value] 1 = .ok (replace memory id (writeByte allocation value)) := by
  have checked := oneByte_check provenance found base live size
  simp [store, Nat.mod_one, checked, writeByte]

theorem oneByte_load {memory : State} {p : Ptr} {id : Nat} {allocation : Allocation}
    {value : Byte} (provenance : p.provenance = some id)
    (found : memory.allocations id = some allocation) (base : p.addr = allocation.base)
    (live : allocation.live = true) (size : allocation.size = 1)
    (byte : allocation.data 0 = value) :
    load memory p 1 1 = .ok ([value], memory) := by
  have checked := oneByte_check provenance found base live size
  have observed : List.ofFn (fun i : Fin 1 => allocation.data (0 + i.val)) = [value] := by
    have pointwise : (fun i : Fin 1 => allocation.data (0 + i.val)) =
        (fun i : Fin 1 => [value].getD i.val .uninit) := by
      funext i
      simp [byte]
    rw [pointwise]
    exact MemoryExamples.readback_exact [value]
  simpa [load, Nat.mod_one, checked] using
    congrArg (fun bytes => Result.ok (bytes, memory)) observed

theorem oneByte_free {memory : State} {p : Ptr} {id : Nat} {allocation : Allocation}
    (provenance : p.provenance = some id)
    (found : memory.allocations id = some allocation) (base : p.addr = allocation.base)
    (kind : allocation.kind = .heap) (size : allocation.size = 1)
    (align : allocation.align = 1) (live : allocation.live = true) :
    free memory p .heap 1 1 = .ok (replace memory id { allocation with live := false }) := by
  simp [free, provenance, found, base, kind, size, align, live]

theorem byteAt_fresh (memory : State) (addr : Nat) :
    ByteAt (append memory (freshAllocation .heap 1 1 addr))
      ⟨addr, some memory.next⟩ memory.next .uninit := by
  refine ⟨rfl, freshAllocation .heap 1 1 addr, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [append]

theorem byteAt_frame {first second : State} {p : Ptr} {id : Nat} {value : Byte}
    (atByte : ByteAt first p id value)
    (same : second.allocations id = first.allocations id) : ByteAt second p id value := by
  rcases atByte with ⟨provenance, allocation, found, base, kind, size, align, live, byte⟩
  exact ⟨provenance, allocation, same.trans found, base, kind, size, align, live, byte⟩

theorem byteAt_append_other {memory : State} {p : Ptr} {id : Nat} {value : Byte}
    (atByte : ByteAt memory p id value) (different : id ≠ memory.next)
    (fresh : Allocation) : ByteAt (append memory fresh) p id value := by
  exact byteAt_frame atByte (by simp [append, different])

theorem byteAt_store_other {before after : State} {kept written : Ptr}
    {keptId writtenId align : Nat} {value : Byte} {bytes : List Byte}
    (atByte : ByteAt before kept keptId value)
    (provenance : written.provenance = some writtenId) (different : keptId ≠ writtenId)
    (success : store before written bytes align = .ok after) : ByteAt after kept keptId value := by
  exact byteAt_frame atByte (ProofCostFrames.store_preserves_other provenance different success)

theorem byteAt_free_other {before after : State} {kept freed : Ptr}
    {keptId freedId size align : Nat} {kind : Kind} {value : Byte}
    (atByte : ByteAt before kept keptId value)
    (provenance : freed.provenance = some freedId) (different : keptId ≠ freedId)
    (success : free before freed kind size align = .ok after) : ByteAt after kept keptId value := by
  exact byteAt_frame atByte (ProofCostFrames.free_preserves_other provenance different success)

theorem byteAt_store {memory : State} {p : Ptr} {id : Nat} {old : Byte}
    (atByte : ByteAt memory p id old) (value : Byte) :
    ∃ written, store memory p [value] 1 = .ok written ∧ ByteAt written p id value := by
  rcases atByte with ⟨provenance, allocation, found, base, kind, size, align, live, _⟩
  refine ⟨replace memory id (writeByte allocation value),
    oneByte_store provenance found base live size value, provenance,
    writeByte allocation value, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [replace]
  · exact base
  · exact kind
  · exact size
  · exact align
  · exact live
  · simp [writeByte]

theorem byteAt_load {memory : State} {p : Ptr} {id : Nat} {value : Byte}
    (atByte : ByteAt memory p id value) : load memory p 1 1 = .ok ([value], memory) := by
  rcases atByte with ⟨provenance, allocation, found, base, _, size, _, live, byte⟩
  exact oneByte_load provenance found base live size byte

theorem byteAt_free {memory : State} {p : Ptr} {id : Nat} {value : Byte}
    (atByte : ByteAt memory p id value) :
    ∃ freed, free memory p .heap 1 1 = .ok freed ∧
      ∃ allocation, freed.allocations id = some allocation ∧ allocation.live = false := by
  rcases atByte with ⟨provenance, allocation, found, base, kind, size, align, live, _⟩
  refine ⟨replace memory id { allocation with live := false },
    oneByte_free provenance found base kind size align live,
    { allocation with live := false }, ?_, rfl⟩
  simp [replace]

/- Audit substantive transport and actual-operation facts once. Straightforward
predicate weakening, lookup framing and bookkeeping projections stay unaudited. -/
#print axioms noLive_iff_liveOnly_empty
#print axioms append_liveOnly
#print axioms replace_liveOnly_same_live
#print axioms store_preserves_liveOnly
#print axioms load_success_memory
#print axioms free_selected_shape
#print axioms free_removes_liveOnly
#print axioms append_supportBelow
#print axioms oneByte_check
#print axioms oneByte_store
#print axioms oneByte_load
#print axioms oneByte_free
#print axioms byteAt_fresh
#print axioms byteAt_store

end AnnealResearch.ProgramCostPrimitives
