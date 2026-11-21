import ToyPin.Model

/-!
# The temporary-object actions on the empty heap

`Act.dropTemp` and `Act.freeTemp` act on the object at address `st.heap.length - 1`, computed
with truncated subtraction on `Nat`. On a non-empty heap this is the most recently allocated
object. On the empty heap the address is `0`, which is out of range: both actions leave the
state unchanged, and the `.freeTemp` case of `DropGuaranteeAct` holds vacuously because
`st.width 0 = 0`.
-/

namespace Toy.Pin

/-- On the empty heap, the address `st.heap.length - 1` used by `dropTemp` and `freeTemp` is `0`
(truncated subtraction), `dropTemp i` and `freeTemp` leave the state unchanged, and
`DropGuaranteeAct st .freeTemp` holds. -/
theorem tempActs_noop_on_empty_heap (st : State) (h : st.heap = []) (i : Nat) :
    st.heap.length - 1 = 0 ∧ applyAct st (.dropTemp i) = st ∧ applyAct st .freeTemp = st ∧
      DropGuaranteeAct st .freeTemp := by
  obtain ⟨heap, registry, nextId⟩ := st
  subst h
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [applyAct, State.dropAt, State.leafAt]
  · simp [applyAct, State.deallocAt, State.modifyObj, modifyAt]
  · simp [DropGuaranteeAct, State.width]

end Toy.Pin
