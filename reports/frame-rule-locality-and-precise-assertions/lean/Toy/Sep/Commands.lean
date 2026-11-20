import Toy.Sep.Heap

/-!
# Heap commands

Commands over the heap model, as relations `Heap V → Outcome (Heap V) → Prop`.

Local (intended) commands: `assertAlloc`, `lookup`, `mutate`, `alloc`,
`allocInto`, `free`, and `allocAtBlock` (fixed-address allocation that blocks when
the address is taken).

Plausible but non-local commands: `allocAt` (allocate at a fixed address,
faulting if it is taken), `allocLeast` (deterministic allocation of the least free
address), `isAllocTest` (test whether a cell is allocated and record the answer),
`detAlloc` and `detAllocInto` (deterministic allocation policies).
-/

namespace Toy.Sep

open SepStruct

variable {V : Type}

/-- Guard "cell `k` is allocated": faults if `k` is unallocated, otherwise leaves
the heap unchanged. This is the heap footprint of a read `x := [k]` whose result
goes to a program variable outside the heap. -/
def assertAlloc (k : Nat) : Cmd (Heap V) := fun h o =>
  (h.val k = none ∧ o = .fault) ∨ (h.val k ≠ none ∧ o = .ok h)

/-- Lookup `[r] := [k]`: copy the contents of cell `k` into cell `r`; faults if
either cell is unallocated. (The read value is observable because it is stored in
the heap cell `r`.) -/
def lookup (k r : Nat) : Cmd (Heap V) := fun h o =>
  ((h.val k = none ∨ h.val r = none) ∧ o = .fault) ∨
  (h.val k ≠ none ∧ h.val r ≠ none ∧ o = .ok (h.set r (h.val k)))

/-- Mutation `[k] := v`: faults if `k` is unallocated. -/
def mutate (k : Nat) (v : V) : Cmd (Heap V) := fun h o =>
  (h.val k = none ∧ o = .fault) ∨ (h.val k ≠ none ∧ o = .ok (h.set k (some v)))

/-- Allocation of one cell holding `v` at a *nondeterministically chosen* fresh
address. Never faults. The chosen address is not recorded (heap footprint of
`x := cons(v)` with `x` outside the heap); see `allocInto` for the variant that
records it. -/
def alloc (v : V) : Cmd (Heap V) := fun h o =>
  ∃ k, h.val k = none ∧ o = .ok (h.set k (some v))

/-- Allocation that records the chosen address: faults if cell `r` is
unallocated; otherwise picks any fresh address `k`, stores `v` at `k` and the
address `k` in cell `r` (`[r] := cons(v)`). -/
def allocInto (r : Nat) (v : Nat) : Cmd (Heap Nat) := fun h o =>
  (h.val r = none ∧ o = .fault) ∨
  (h.val r ≠ none ∧ ∃ k, h.val k = none ∧ o = .ok ((h.set k (some v)).set r (some k)))

/-- Deallocation `free k`: faults if `k` is unallocated, otherwise removes it. -/
def free (k : Nat) : Cmd (Heap V) := fun h o =>
  (h.val k = none ∧ o = .fault) ∨ (h.val k ≠ none ∧ o = .ok (h.set k none))

/-- Allocation at a *fixed* address `k`: faults if `k` is already allocated,
otherwise stores `v` there. (Not local: violates safety monotonicity.) -/
def allocAt (k : Nat) (v : V) : Cmd (Heap V) := fun h o =>
  (h.val k ≠ none ∧ o = .fault) ∨ (h.val k = none ∧ o = .ok (h.set k (some v)))

/-- *Deterministic* allocation: always uses the least free address. Never faults.
(Not local: violates the frame property.) -/
def allocLeast (v : V) : Cmd (Heap V) := fun h o =>
  ∃ k, h.val k = none ∧ (∀ j, j < k → h.val j ≠ none) ∧ o = .ok (h.set k (some v))

/-- Allocation test "is cell `k` allocated?", recording the answer in cell `r`
(`1` = allocated, `0` = not allocated); faults if `r` is unallocated.
(Not local when `k ≠ r`: violates the frame property.) -/
def isAllocTest (k r : Nat) : Cmd (Heap Nat) := fun h o =>
  (h.val r = none ∧ o = .fault) ∨
  (h.val r ≠ none ∧ h.val k ≠ none ∧ o = .ok (h.set r (some 1))) ∨
  (h.val r ≠ none ∧ h.val k = none ∧ o = .ok (h.set r (some 0)))

/-- A *deterministic, total, non-faulting* single-cell writer: from every heap `h`
it terminates normally in exactly one state, `h` with address `f h` set to `v`.
With `f h` fresh in `h` this is a deterministic allocation policy that does not
record the chosen address (e.g. "least free address"). It does not cover
allocators that record the address in a cell (see `detAllocInto`), or that fault
or block on some heaps; the general impossibility
`Toy.Sep.not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied` covers those. -/
def detAlloc (f : Heap V → Nat) (v : V) : Cmd (Heap V) := fun h o =>
  o = .ok (h.set (f h) (some v))

/-- Deterministic pointer-recording allocation `[r] := det_cons(v)`: faults if
cell `r` is unallocated; otherwise stores `v` at the address `f h` chosen
deterministically from the current heap, and stores that address in cell `r`. -/
def detAllocInto (f : Heap Nat → Nat) (r v : Nat) : Cmd (Heap Nat) := fun h o =>
  (h.val r = none ∧ o = .fault) ∨
  (h.val r ≠ none ∧ o = .ok ((h.set (f h) (some v)).set r (some (f h))))

/-- A deterministic allocator that is *partial*: it only runs from the empty heap
(where it allocates address `0`) and has no outcome from any other heap. -/
def detAllocOnEmp (v : V) : Cmd (Heap V) := fun h o =>
  h = Heap.emp ∧ o = .ok (Heap.pt 0 v)

/-- Allocation at a fixed address `k` that *blocks* (has no outcome) when `k` is
already allocated, instead of faulting as `allocAt` does. -/
def allocAtBlock (k : Nat) (v : V) : Cmd (Heap V) := fun h o =>
  h.val k = none ∧ o = .ok (h.set k (some v))

/-! ## Safety characterizations (proved helper lemmas) -/

theorem safe_skip {S : Type _} (h : S) : Safe (skip : Cmd S) h := by
  intro hf; cases hf

theorem safe_lookup_iff (k r : Nat) (h : Heap V) :
    Safe (lookup k r) h ↔ h.val k ≠ none ∧ h.val r ≠ none := by
  unfold Safe lookup
  constructor
  · intro hs
    exact ⟨fun hk => hs (Or.inl ⟨Or.inl hk, rfl⟩), fun hr => hs (Or.inl ⟨Or.inr hr, rfl⟩)⟩
  · rintro ⟨hk, hr⟩ (⟨h1 | h1, _⟩ | ⟨_, _, h2⟩)
    · exact hk h1
    · exact hr h1
    · cases h2

theorem safe_alloc (v : V) (h : Heap V) : Safe (alloc v) h := by
  rintro ⟨_, _, hf⟩; cases hf

theorem safe_allocInto_iff (r v : Nat) (h : Heap Nat) :
    Safe (allocInto r v) h ↔ h.val r ≠ none := by
  unfold Safe allocInto
  constructor
  · intro hs hr; exact hs (Or.inl ⟨hr, rfl⟩)
  · rintro hr (⟨h1, _⟩ | ⟨_, _, _, h2⟩)
    · exact hr h1
    · cases h2

theorem safe_free_iff (k : Nat) (h : Heap V) :
    Safe (free k) h ↔ h.val k ≠ none := by
  unfold Safe free
  constructor
  · intro hs hk; exact hs (Or.inl ⟨hk, rfl⟩)
  · rintro hk (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact hk h1
    · cases h2

theorem safe_detAlloc (f : Heap V → Nat) (v : V) (h : Heap V) : Safe (detAlloc f v) h := by
  intro hf; cases hf

theorem safe_detAllocInto_iff (f : Heap Nat → Nat) (r v : Nat) (h : Heap Nat) :
    Safe (detAllocInto f r v) h ↔ h.val r ≠ none := by
  unfold Safe detAllocInto
  constructor
  · intro hs hr; exact hs (Or.inl ⟨hr, rfl⟩)
  · rintro hr (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact hr h1
    · cases h2

theorem safe_detAllocOnEmp (v : V) (h : Heap V) : Safe (detAllocOnEmp v) h := by
  rintro ⟨_, hf⟩; cases hf

theorem safe_allocAtBlock (k : Nat) (v : V) (h : Heap V) : Safe (allocAtBlock k v) h := by
  rintro ⟨_, hf⟩; cases hf

theorem safe_assertAlloc_iff (k : Nat) (h : Heap V) :
    Safe (assertAlloc k) h ↔ h.val k ≠ none := by
  unfold Safe assertAlloc
  constructor
  · intro hs hk; exact hs (Or.inl ⟨hk, rfl⟩)
  · intro hk hf
    rcases hf with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hk h1
    · cases h2

theorem safe_mutate_iff (k : Nat) (v : V) (h : Heap V) :
    Safe (mutate k v) h ↔ h.val k ≠ none := by
  unfold Safe mutate
  constructor
  · intro hs hk; exact hs (Or.inl ⟨hk, rfl⟩)
  · intro hk hf
    rcases hf with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hk h1
    · cases h2

theorem safe_allocAt_iff (k : Nat) (v : V) (h : Heap V) :
    Safe (allocAt k v) h ↔ h.val k = none := by
  unfold Safe allocAt
  constructor
  · intro hs
    cases e : h.val k with
    | none => rfl
    | some w => exact absurd (Or.inl ⟨by simp [e], rfl⟩) hs
  · intro hk hf
    rcases hf with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1 hk
    · cases h2

theorem safe_allocLeast (v : V) (h : Heap V) : Safe (allocLeast v) h := by
  intro ⟨_, _, _, he⟩; cases he

theorem safe_isAllocTest_iff (k r : Nat) (h : Heap Nat) :
    Safe (isAllocTest k r) h ↔ h.val r ≠ none := by
  unfold Safe isAllocTest
  constructor
  · intro hs hr; exact hs (Or.inl ⟨hr, rfl⟩)
  · intro hr hf
    rcases hf with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩
    · exact hr h1
    · cases h2
    · cases h2

end Toy.Sep
