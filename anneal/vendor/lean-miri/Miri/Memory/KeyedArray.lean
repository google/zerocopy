import Std

/-! Ordered metadata arrays with an exact key-to-row index.

The index stores only row positions, never values. Payloads therefore occur
once in the ordered rows. A certificate ties each index to those exact rows;
constructors and mutations rebuild both together. Iteration retains source
array order and duplicate-key lookup semantics. -/
namespace Miri.Memory

private def indexStep [BEq K] [Hashable K]
    (state : Nat × Std.HashMap K (Array Nat)) (key : K) : Nat × Std.HashMap K (Array Nat) :=
  (state.1 + 1, state.2.insert key ((state.2.getD key #[]).push state.1))

private def canonicalIndex [BEq K] [Hashable K] (keys : Array K) :
    Nat × Std.HashMap K (Array Nat) :=
  keys.foldl indexStep (0, {})

structure KeyedArray (K V : Type) (keyFn : V → K) [BEq K] [Hashable K] where
  private mk ::
  private keys : Array K
  private rows : Array V
  private indexState : Nat × Std.HashMap K (Array Nat)
  private exact : indexState = canonicalIndex keys
  private aligned : keys.size = rows.size
  private keysMatchRows : keys = rows.map keyFn

namespace KeyedArray

variable {K V : Type} [BEq K] [Hashable K] {keyFn : V → K}

def empty (keyFn : V → K) : KeyedArray K V keyFn :=
  ⟨#[], #[], (0, {}), by rfl, by rfl, by simp⟩

def ofArray (keyFn : V → K) (rows : Array V) : KeyedArray K V keyFn :=
  let keys := rows.map keyFn
  let indexState := canonicalIndex keys
  ⟨keys, rows, indexState, by rfl, by simp [keys], by rfl⟩

def keyOf (_table : KeyedArray K V keyFn) : V → K := keyFn

def toArray (table : KeyedArray K V keyFn) : Array V := table.rows

def toPairs (table : KeyedArray K V keyFn) : Array (K × V) := table.keys.zip table.rows

def find? (table : KeyedArray K V keyFn) (key : K) : Option V := do
  let indices ← table.indexState.2.get? key
  let rowIndex ← indices[0]?
  table.rows[rowIndex]?

/-- Test every same-key row, preserving the historical `Array.any` behavior
for deliberately constructed duplicate metadata keys. -/
def any? (table : KeyedArray K V keyFn) (key : K) (p : V → Bool) : Bool := Id.run do
  let some indices := table.indexState.2.get? key | return false
  for rowIndex in indices do
    if let some value := table.rows[rowIndex]? then
      if p value then return true
  return false

def valuesFor (table : KeyedArray K V keyFn) (key : K) : Array V := Id.run do
  let some indices := table.indexState.2.get? key | return #[]
  let mut values := #[]
  for rowIndex in indices do
    if let some value := table.rows[rowIndex]? then values := values.push value
  return values

def contains (table : KeyedArray K V keyFn) (key : K) : Bool := table.indexState.2.contains key

def isEmpty (table : KeyedArray K V keyFn) : Bool := table.rows.isEmpty

def size (table : KeyedArray K V keyFn) : Nat := table.rows.size

/-- Append while preserving first-row lookup and source iteration order. -/
def push (table : KeyedArray K V keyFn) (value : V) : KeyedArray K V keyFn :=
  let key := keyFn value
  let indexState := indexStep table.indexState key
  ⟨table.keys.push key, table.rows.push value, indexState, by
    dsimp [indexState]
    rw [table.exact]
    simp [canonicalIndex, indexStep]
  , by simpa using table.aligned, by simp [table.keysMatchRows, key]⟩

/-- Filter and reindex a cold metadata table. -/
def filter (table : KeyedArray K V keyFn) (keep : K → V → Bool) : KeyedArray K V keyFn :=
  ofArray keyFn (table.rows.filter fun row => keep (keyFn row) row)

/-- Map rows in source order and rebuild the index, allowing key changes. -/
def mapValues (table : KeyedArray K V keyFn) (f : V → V) : KeyedArray K V keyFn :=
  ofArray keyFn (table.rows.map f)

/-- Map row payloads, reusing the certified index when the mapped rows retain
the exact key sequence. A map that changes keys falls back to a full reindex,
so this preserves the unrestricted semantics of `mapValues`. -/
def mapValuesChecked [DecidableEq K] (table : KeyedArray K V keyFn) (f : V → V) :
    KeyedArray K V keyFn := Id.run do
  let rows := table.rows.map f
  let keys := rows.map keyFn
  if h : keys = table.keys then
    return ⟨table.keys, rows, table.indexState, table.exact,
      by simpa [rows] using table.aligned, h.symm⟩
  else
    return ofArray keyFn rows

private theorem map_modify_preserves (rows : Array V) (i : Nat) (f : V → V)
    (preserves : ∀ row, keyFn (f row) = keyFn row) :
    (rows.modify i f).map keyFn = rows.map keyFn := by
  rw [Array.map_eq_iff]
  intro j
  rw [Array.getElem?_modify]
  by_cases h : i = j
  · subst j
    cases hrow : rows[i]? with
    | none => simp [hrow]
    | some row => simp [hrow, preserves]
  · simp [h]

/-- Apply a key-preserving row update while retaining the certified key
sequence and index. The proof obligation is local to the update function. -/
def modifyAt (table : KeyedArray K V keyFn) (i : Nat) (f : V → V)
    (preserves : ∀ row, keyFn (f row) = keyFn row) : KeyedArray K V keyFn :=
  ⟨table.keys, table.rows.modify i f, table.indexState, table.exact,
    by simpa using table.aligned,
    by rw [map_modify_preserves table.rows i f preserves, table.keysMatchRows]⟩

/-- Update every row at a key's certified positions, retaining the existing
index. -/
def mapValuesForKey (table : KeyedArray K V keyFn) (key : K) (f : V → V)
    (preserves : ∀ row, keyFn (f row) = keyFn row) : KeyedArray K V keyFn := Id.run do
  let some indices := table.indexState.2.get? key | return table
  let mut result := table
  for rowIndex in indices do
    result := result.modifyAt rowIndex f preserves
  return result

private theorem index_contains [LawfulBEq K] [LawfulHashable K]
    (keys : Array K) (initial : Nat × Std.HashMap K (Array Nat)) (key : K) :
    (keys.foldl indexStep initial).2.contains key =
      (initial.2.contains key || keys.contains key) := by
  rw [←Array.foldl_toList,←Array.contains_toList]
  generalize keys.toList = rows
  induction rows generalizing initial with
  | nil => simp
  | cons first rest ih =>
    have swap : (first == key) = (key == first) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact eq_comm
    simp [List.foldl_cons,indexStep,ih,Std.HashMap.contains_insert,
      Bool.or_assoc,Bool.or_comm,Bool.or_left_comm,swap]

/-- The certified hash index contains precisely the keys of current rows. -/
theorem contains_rows [LawfulBEq K] [LawfulHashable K]
    (table : KeyedArray K V keyFn) (key : K) :
    table.contains key = (table.toArray.map keyFn).contains key := by
  simp only [contains,table.exact,canonicalIndex,index_contains]
  simp [table.keysMatchRows,toArray]

end KeyedArray
end Miri.Memory

namespace Miri.Memory.KeyedArray
variable {K V : Type} [BEq K] [Hashable K] [LawfulBEq K] [LawfulHashable K]
private def indexValid (state : Nat × Std.HashMap K (Array Nat)) : Prop :=
  ∀ (key : K) (positions : Array Nat), state.2[key]? = some positions →
    0 < positions.size ∧ ∀ index ∈ positions, index < state.1
private theorem indexStep_valid (state : Nat × Std.HashMap K (Array Nat))
    (key : K) (valid : indexValid state) : indexValid (indexStep state key) := by
  intro query positions found
  change 0 < positions.size ∧ ∀ index ∈ positions, index < state.1+1
  simp only [indexStep,Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    cases found
    constructor
    · simp
    · intro index member
      rcases Array.mem_push.mp member with old | rfl
      · cases previous : state.2[key]? with
        | none => simp [Std.HashMap.getD_eq_getD_getElem?,previous] at old
        | some rows =>
          have oldValid := valid key rows previous
          have before : index < state.1 := oldValid.2 index (by simpa [Std.HashMap.getD_eq_getD_getElem?,previous] using old)
          omega
      · omega
  · have oldValid := valid query positions found
    exact ⟨oldValid.1,fun index member => by have bound := oldValid.2 index member; omega⟩
private theorem canonical_valid (keys : Array K) : indexValid (canonicalIndex keys) := by
  have fold : ∀ (rows : List K) state, indexValid state →
      indexValid (rows.foldl indexStep state) := by
    intro rows
    induction rows with
    | nil => intro state valid; exact valid
    | cons first rest ih => intro state valid; exact ih _ (indexStep_valid state first valid)
  change indexValid (keys.foldl indexStep (0,{}))
  rw [←Array.foldl_toList]
  apply fold keys.toList (0,{})
  intro key positions found
  simp at found
private theorem canonical_size (keys : Array K) : (canonicalIndex keys).1 = keys.size := by
  have fold : ∀ (rows : List K) state, (rows.foldl indexStep state).1 = state.1+rows.length := by
    intro rows
    induction rows with
    | nil => intro state; simp
    | cons first rest ih => intro state; simp [List.foldl_cons,ih,indexStep]; omega
  simpa [canonicalIndex,Array.foldl_toList] using fold keys.toList (0,{})
/-- A certified present key always selects a real row, including duplicate keys. -/
theorem find_of_contains {keyFn : V → K} (table : KeyedArray K V keyFn) (key : K)
    (present : table.contains key = true) : ∃ row, table.find? key = some row := by
  have existsPositions : ∃ positions, table.indexState.2[key]? = some positions := by
    cases query : table.indexState.2[key]? with
    | none => simp only [contains,Std.HashMap.contains_eq_isSome_getElem?,query,Option.isSome_none,Bool.false_eq_true] at present
    | some positions => exact ⟨positions,rfl⟩
  obtain ⟨positions,found⟩ := existsPositions
  have good := canonical_valid table.keys key positions (by simpa only [←table.exact] using found)
  have first : 0 < positions.size := good.1
  have bound : positions[0] < table.rows.size := by
    have small := good.2 positions[0] (Array.getElem_mem first)
    rw [canonical_size,table.aligned] at small
    exact small
  refine ⟨table.rows[positions[0]],?_⟩
  simp [find?,found,Array.getElem?_eq_getElem first,Array.getElem?_eq_getElem bound]
/-- Missing lookup excludes index membership, without an additional coherence law. -/
theorem contains_false_of_find_none {keyFn : V → K} (table : KeyedArray K V keyFn) (key : K)
    (missing : table.find? key = none) : table.contains key = false := by
  cases present : table.contains key
  · rfl
  · obtain ⟨row,found⟩ := find_of_contains table key present
    rw [missing] at found
    cases found
end Miri.Memory.KeyedArray
