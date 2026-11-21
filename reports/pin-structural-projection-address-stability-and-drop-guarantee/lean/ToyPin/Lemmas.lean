import ToyPin.Model

/-!
# Basic lemmas about the heap operations

Frame lemmas describing how each primitive update changes `leafAt`, `isPinnedLoc`,
`isPinned`, and the heap length. Proof infrastructure only.
-/

namespace Toy.Pin

theorem getElem?_modifyAt {α : Type} (f : α → α) :
    ∀ (l : List α) (n m : Nat), (modifyAt f l n)[m]? = if n = m then (l[m]?).map f else l[m]?
  | [], _, _ => by simp [modifyAt]
  | a :: as, 0, 0 => by simp [modifyAt]
  | a :: as, 0, m + 1 => by simp [modifyAt]
  | a :: as, n + 1, 0 => by simp [modifyAt]
  | a :: as, n + 1, m + 1 => by simp [modifyAt, getElem?_modifyAt f as n m]

theorem length_modifyAt {α : Type} (f : α → α) :
    ∀ (l : List α) (n : Nat), (modifyAt f l n).length = l.length
  | [], _ => rfl
  | a :: as, 0 => rfl
  | a :: as, n + 1 => by simp [modifyAt, length_modifyAt f as n]

namespace State

@[simp] theorem modifyObj_registry (st : State) (b : Nat) (f : Obj → Obj) :
    (st.modifyObj b f).registry = st.registry := rfl

@[simp] theorem setLeaf_registry (st : State) (l : Loc) (x : Option Leaf) :
    (st.setLeaf l x).registry = st.registry := rfl

@[simp] theorem push_registry (st : State) (o : Obj) : (st.push o).registry = st.registry := rfl

@[simp] theorem modifyObj_length (st : State) (b : Nat) (f : Obj → Obj) :
    (st.modifyObj b f).heap.length = st.heap.length := length_modifyAt _ _ _

@[simp] theorem setLeaf_length (st : State) (l : Loc) (x : Option Leaf) :
    (st.setLeaf l x).heap.length = st.heap.length := modifyObj_length _ _ _

@[simp] theorem push_length (st : State) (o : Obj) :
    (st.push o).heap.length = st.heap.length + 1 := by simp [push]

theorem modifyObj_heap (st : State) (b : Nat) (f : Obj → Obj) (c : Nat) :
    (st.modifyObj b f).heap[c]? = if b = c then (st.heap[c]?).map f else st.heap[c]? :=
  getElem?_modifyAt _ _ _ _

theorem push_heap (st : State) (o : Obj) (c : Nat) :
    (st.push o).heap[c]? =
      if c < st.heap.length then st.heap[c]? else if c = st.heap.length then some o else none := by
  unfold push
  simp only
  by_cases h : c < st.heap.length
  · rw [List.getElem?_append_left h]; simp [h]
  · have hle : st.heap.length ≤ c := by omega
    rw [List.getElem?_append_right hle]
    by_cases h2 : c = st.heap.length
    · subst h2; simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp [h, h2]

/-- `leafAt` only depends on the object at the location's address. -/
theorem leafAt_congr {st st' : State} {l : Loc} (h : st'.heap[l.1]? = st.heap[l.1]?) :
    st'.leafAt l = st.leafAt l := by
  unfold leafAt; rw [h]

theorem isPinnedLoc_congr {st st' : State} {l : Loc} (h : st'.heap[l.1]? = st.heap[l.1]?) :
    st'.isPinnedLoc l = st.isPinnedLoc l := by
  unfold isPinnedLoc; rw [h]

theorem isPinned_congr {st st' : State} {b : Nat} (h : st'.heap[b]? = st.heap[b]?) :
    st'.isPinned b = st.isPinned b := by
  unfold isPinned; rw [h]

theorem width_congr {st st' : State} {b : Nat} (h : st'.heap[b]? = st.heap[b]?) :
    st'.width b = st.width b := by
  unfold width; rw [h]

/-! ### `modifyObj` -/

theorem modifyObj_heap_ne {st : State} {b c : Nat} (f : Obj → Obj) (h : c ≠ b) :
    (st.modifyObj b f).heap[c]? = st.heap[c]? := by
  rw [modifyObj_heap]; simp [Ne.symm h]

theorem leafAt_modifyObj_of_fields {st : State} {b : Nat} {f : Obj → Obj}
    (hf : ∀ o, (f o).fields = o.fields) (l : Loc) :
    (st.modifyObj b f).leafAt l = st.leafAt l := by
  unfold leafAt
  rw [modifyObj_heap]
  by_cases h : b = l.1
  · simp only [h, ite_true]
    cases st.heap[l.1]? <;> simp [Obj.leaf, hf]
  · simp [h]

theorem isPinnedLoc_modifyObj_of_pf {st : State} {b : Nat} {f : Obj → Obj}
    (hf : ∀ o, (f o).pinnedFields = o.pinnedFields) (l : Loc) :
    (st.modifyObj b f).isPinnedLoc l = st.isPinnedLoc l := by
  unfold isPinnedLoc
  rw [modifyObj_heap]
  by_cases h : b = l.1
  · simp only [h, ite_true]
    cases st.heap[l.1]? <;> simp [hf]
  · simp [h]

theorem isPinned_modifyObj_of_pinned {st : State} {b : Nat} {f : Obj → Obj}
    (hf : ∀ o, (f o).pinned = o.pinned) (c : Nat) :
    (st.modifyObj b f).isPinned c = st.isPinned c := by
  unfold isPinned
  rw [modifyObj_heap]
  by_cases h : b = c
  · simp only [h, ite_true]
    cases st.heap[c]? <;> simp [hf]
  · simp [h]

theorem width_modifyObj_of_len {st : State} {b : Nat} {f : Obj → Obj}
    (hf : ∀ o, (f o).fields.length = o.fields.length) (c : Nat) :
    (st.modifyObj b f).width c = st.width c := by
  unfold width
  rw [modifyObj_heap]
  by_cases h : b = c
  · simp only [h, ite_true]
    cases st.heap[c]? <;> simp [hf]
  · simp [h]

/-! ### `setLeaf` -/

theorem leafAt_setLeaf_ne {st : State} {l l' : Loc} (x : Option Leaf) (h : l' ≠ l) :
    (st.setLeaf l x).leafAt l' = st.leafAt l' := by
  unfold setLeaf leafAt
  rw [modifyObj_heap]
  by_cases hb : l.1 = l'.1
  · simp only [hb, ite_true]
    cases ho : st.heap[l'.1]? with
    | none => simp
    | some o =>
      simp only [Option.map_some, Obj.leaf]
      rw [getElem?_modifyAt]
      have : l.2 ≠ l'.2 := by
        intro h2; apply h; exact Prod.ext hb.symm h2.symm
      simp [this]
  · simp [hb]

theorem leafAt_setLeaf_self (st : State) (l : Loc) (x : Option Leaf) :
    (st.setLeaf l x).leafAt l = x ∨ (st.setLeaf l x).leafAt l = none := by
  unfold setLeaf leafAt
  rw [modifyObj_heap]
  simp only [ite_true]
  cases ho : st.heap[l.1]? with
  | none => simp
  | some o =>
    simp only [Option.map_some, Obj.leaf]
    rw [getElem?_modifyAt]
    simp only [ite_true]
    cases o.fields[l.2]? <;> simp

theorem leafAt_setLeaf_self_of_some {st : State} {l : Loc} {v : Leaf} (x : Option Leaf)
    (h : st.leafAt l = some v) : (st.setLeaf l x).leafAt l = x := by
  unfold setLeaf leafAt at *
  rw [modifyObj_heap]
  simp only [ite_true]
  cases ho : st.heap[l.1]? with
  | none => simp [ho] at h
  | some o =>
    simp only [ho, Obj.leaf] at h
    simp only [Option.map_some, Obj.leaf]
    rw [getElem?_modifyAt]
    simp only [ite_true]
    cases hi : o.fields[l.2]? with
    | none => simp [hi] at h
    | some y => simp

@[simp] theorem isPinnedLoc_setLeaf (st : State) (l : Loc) (x : Option Leaf) (l' : Loc) :
    (st.setLeaf l x).isPinnedLoc l' = st.isPinnedLoc l' := by
  unfold setLeaf
  exact isPinnedLoc_modifyObj_of_pf (f := fun o => { o with fields := modifyAt (fun _ => x) o.fields l.2 })
    (fun _ => rfl) l'

@[simp] theorem isPinned_setLeaf (st : State) (l : Loc) (x : Option Leaf) (c : Nat) :
    (st.setLeaf l x).isPinned c = st.isPinned c := by
  unfold setLeaf
  exact isPinned_modifyObj_of_pinned (f := fun o => { o with fields := modifyAt (fun _ => x) o.fields l.2 })
    (fun _ => rfl) c

/-! ### `push` -/

theorem leafAt_push_lt {st : State} {l : Loc} (o : Obj) (h : l.1 < st.heap.length) :
    (st.push o).leafAt l = st.leafAt l :=
  leafAt_congr (by rw [push_heap]; simp [h])

theorem leafAt_push_eq (st : State) (o : Obj) (i : Nat) :
    (st.push o).leafAt (st.heap.length, i) = o.leaf i := by
  unfold leafAt; rw [push_heap]; simp

theorem leafAt_push_gt {st : State} {l : Loc} (o : Obj) (h : st.heap.length < l.1) :
    (st.push o).leafAt l = none := by
  unfold leafAt; rw [push_heap]
  have h1 : ¬ l.1 < st.heap.length := by omega
  have h2 : l.1 ≠ st.heap.length := by omega
  simp [h1, h2]

theorem isPinnedLoc_push_lt {st : State} {l : Loc} (o : Obj) (h : l.1 < st.heap.length) :
    (st.push o).isPinnedLoc l = st.isPinnedLoc l :=
  isPinnedLoc_congr (by rw [push_heap]; simp [h])

theorem isPinned_push_lt {st : State} {c : Nat} (o : Obj) (h : c < st.heap.length) :
    (st.push o).isPinned c = st.isPinned c :=
  isPinned_congr (by rw [push_heap]; simp [h])

theorem isPinnedLoc_push_fresh (st : State) (fs : List (Option Leaf)) (l : Loc)
    (h : st.heap.length ≤ l.1) : (st.push (Obj.fresh fs)).isPinnedLoc l = false := by
  unfold isPinnedLoc; rw [push_heap]
  have h1 : ¬ l.1 < st.heap.length := by omega
  by_cases h2 : l.1 = st.heap.length <;> simp [h1, h2, Obj.fresh]

theorem isPinned_push_fresh (st : State) (fs : List (Option Leaf)) (c : Nat)
    (h : st.heap.length ≤ c) : (st.push (Obj.fresh fs)).isPinned c = false := by
  unfold isPinned; rw [push_heap]
  have h1 : ¬ c < st.heap.length := by omega
  by_cases h2 : c = st.heap.length <;> simp [h1, h2, Obj.fresh]

/-! ### Locations that hold a leaf exist -/

theorem isPinnedLoc_lt {st : State} {l : Loc} (h : st.isPinnedLoc l = true) :
    l.1 < st.heap.length := by
  unfold isPinnedLoc at h
  cases hb : st.heap[l.1]? with
  | none => simp [hb] at h
  | some o => exact (List.getElem?_eq_some_iff.mp hb).1

theorem isPinned_lt {st : State} {b : Nat} (h : st.isPinned b = true) : b < st.heap.length := by
  unfold isPinned at h
  cases hb : st.heap[b]? with
  | none => simp [hb] at h
  | some o => exact (List.getElem?_eq_some_iff.mp hb).1

theorem isLive_lt {st : State} {b : Nat} (h : st.isLive b = true) : b < st.heap.length := by
  unfold isLive at h
  cases hb : st.heap[b]? with
  | none => simp [hb] at h
  | some o => exact (List.getElem?_eq_some_iff.mp hb).1

end State

/-! ### Leaves of fresh objects -/

theorem Obj.leaf_fresh (fs : List (Option Leaf)) (i : Nat) :
    (Obj.fresh fs).leaf i = (match fs[i]? with | some x => x | none => none) := rfl

theorem leaf_tempFields (i : Nat) (x : Option Leaf) (j : Nat) :
    (Obj.fresh (tempFields i x)).leaf j = if j = i then x else none := by
  unfold Obj.leaf Obj.fresh tempFields
  simp only
  by_cases hj : j < i
  · have hj' : j < (List.replicate i (none : Option Leaf)).length := by simpa using hj
    rw [List.getElem?_append_left hj']
    simp [hj]; omega
  · have hj' : (List.replicate i (none : Option Leaf)).length ≤ j := by simp; omega
    rw [List.getElem?_append_right hj']
    simp only [List.length_replicate, List.getElem?_singleton]
    by_cases h2 : j = i
    · subst h2; simp
    · have : j - i ≠ 0 := by omega
      simp [this, h2]

theorem getElem?_mkFields :
    ∀ (n : Nat) (us : List (Option Bool)) (i : Nat),
      (mkFields n us)[i]? = (us[i]?).map (fun u => u.map fun b => ⟨n + i, b, none⟩)
  | _, [], _ => by simp [mkFields]
  | n, u :: us, 0 => by simp [mkFields]
  | n, u :: us, i + 1 => by
    simp only [mkFields, List.getElem?_cons_succ]
    rw [getElem?_mkFields (n + 1) us i]
    simp [Nat.add_assoc, Nat.add_comm 1 i]

theorem leaf_mkFields_selfPtr {n : Nat} {us : List (Option Bool)} {i : Nat} {v : Leaf}
    (h : (Obj.fresh (mkFields n us)).leaf i = some v) : v.selfPtr = none := by
  unfold Obj.leaf Obj.fresh at h
  simp only [getElem?_mkFields] at h
  cases hu : us[i]? with
  | none => simp [hu] at h
  | some u =>
    cases u with
    | none => simp [hu] at h
    | some b => simp [hu] at h; rw [← h]

end Toy.Pin
