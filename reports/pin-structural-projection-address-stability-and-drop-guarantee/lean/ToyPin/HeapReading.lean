import ToyPin.Companions

/-!
# Reading the heap at out-of-range addresses and field indices

`State.leafAt`, `State.width`, `State.isLive`, `State.isPinned`, `State.isLeaked` and
`State.isPinnedLoc` first look up the object at an address. At an address that holds no object
(`st.heap.length ≤ b`) they return `none`, `0` or `false`, whatever the field index.

At an address that holds an object, a field index at or beyond the object's number of fields
makes `Obj.leaf` and `State.leafAt` return `none`. `State.isPinnedLoc` does not check the field
index against the number of fields: it tests membership of the index in the object's
`pinnedFields` list, which `Act.pinField` extends without a bounds check. So `isPinnedLoc` can be
`true` at a field index that has no field location; `PinnedNonUnpin` is still `false` there,
because it also requires a leaf at the location.
-/

namespace Toy.Pin

/-- At an address that holds no object (`st.heap.length ≤ l.1`), `leafAt` is `none`, `width` is
`0`, and `isLive`, `isPinned`, `isLeaked` and `isPinnedLoc` are `false`, whatever the field index
`l.2`. -/
theorem heap_reads_at_out_of_range_address (st : State) (l : Loc) (h : st.heap.length ≤ l.1) :
    st.leafAt l = none ∧ st.width l.1 = 0 ∧ st.isLive l.1 = false ∧ st.isPinned l.1 = false ∧
      st.isLeaked l.1 = false ∧ st.isPinnedLoc l = false := by
  have hb : st.heap[l.1]? = none := List.getElem?_eq_none_iff.mpr h
  simp [State.leafAt, State.width, State.isLive, State.isPinned, State.isLeaked,
    State.isPinnedLoc, hb]

/-- The empty machine has the empty heap, so every address is out of range in it: no location
holds a leaf, every width is `0`, and the four flags are `false`. -/
theorem heap_reads_in_init (l : Loc) :
    State.init.leafAt l = none ∧ State.init.width l.1 = 0 ∧ State.init.isLive l.1 = false ∧
      State.init.isPinned l.1 = false ∧ State.init.isLeaked l.1 = false ∧
      State.init.isPinnedLoc l = false :=
  heap_reads_at_out_of_range_address State.init l (Nat.zero_le _)

/-- A field index at or beyond the number of fields of an object gives no leaf. -/
theorem Obj.leaf_of_out_of_range (o : Obj) (i : Nat) (h : o.fields.length ≤ i) :
    o.leaf i = none := by
  simp [Obj.leaf, List.getElem?_eq_none_iff.mpr h]

/-- A field index at or beyond the width of the object at address `l.1` gives no leaf. (At an
address that holds no object the width is `0`, so this covers every field index there.) -/
theorem leafAt_of_out_of_range_field (st : State) (l : Loc) (h : st.width l.1 ≤ l.2) :
    st.leafAt l = none := by
  cases hl : st.leafAt l with
  | none => rfl
  | some v =>
    have := (State.leafAt_some_bounds hl).2
    omega

/-- A location protected by the pinning contract is an existing field location: its address
holds an object and its field index is below that object's number of fields. -/
theorem pinnedNonUnpin_in_range (st : State) (l : Loc) (h : PinnedNonUnpin st l) :
    l.1 < st.heap.length ∧ l.2 < st.width l.1 := by
  obtain ⟨_, h2⟩ := h
  cases hl : st.leafAt l with
  | none => simp [hl] at h2
  | some v => exact State.leafAt_some_bounds hl

/-- `isPinnedLoc` can be `true` at a field index that has no field location. On the zero-field
declaration `dZeroOutOfBounds`, the safe program `[.new, .pin 0, .projPin 0 0]` ends in a state
where object 0 has width `0` and location `(0, 0)` holds no leaf, yet `isPinnedLoc (0, 0)` is
`true`; `PinnedNonUnpin` is `false` at `(0, 0)`. -/
theorem isPinnedLoc_at_out_of_range_field :
    SafeProgram dZeroOutOfBounds State.init [.new, .pin 0, .projPin 0 0] ∧
      (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])).width 0 = 0 ∧
      (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])).leafAt
        (0, 0) = none ∧
      (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])).isPinnedLoc
        (0, 0) = true ∧
      ¬ PinnedNonUnpin
        (runActs State.init (compile dZeroOutOfBounds [.new, .pin 0, .projPin 0 0])) (0, 0) := by
  decide

end Toy.Pin
