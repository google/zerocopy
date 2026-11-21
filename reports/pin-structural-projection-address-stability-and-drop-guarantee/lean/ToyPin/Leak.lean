import ToyPin.Scope

/-!
# Leaking an object: what safe continuations can and cannot do to it

`Op.forget b` sets the object's `leaked` flag. In `SafeOp` the flag disables exactly
`Op.drop b` and `Op.forget b`; references obtained before the leak (pinned projections,
and `&mut` access where `MutFieldAvail`/`MutStructAvail` allow it) stay usable, so `forget`
is closer to `Box::leak` than to a value-consuming `mem::forget`. Two general facts:

* `leaked_object_never_dropped_or_deallocated`: for every declaration, every state in which
  object `b` is leaked, and every continuation accepted by `SafeProgram`, the continuation
  contains no `Op.drop b`, `b` keeps its liveness in every visited state, and stays leaked.
* `unmentioned_object_unchanged`: for every declaration and every continuation none of
  whose operations mentions `b` (no safety assumption), the object at `b` (all its leaves,
  self-pointers and flags) and every list entry into `b` are unchanged in every visited
  state. A value-consuming `mem::forget` of the only owner leaves no handle to `b`, so its
  continuations are of this kind (modeling bridge).
-/

namespace Toy.Pin

open State

/-! ## Heap length only grows -/

theorem length_le_applyAct (st : State) (a : Act) :
    st.heap.length ≤ (applyAct st a).heap.length := by
  cases a with
  | setSelf l =>
    simp only [applyAct]
    split
    · split <;> simp
    · simp
  | register l =>
    simp only [applyAct]
    split
    · split <;> simp
    · simp
  | dropLeaf l => simp [applyAct, dropAt_heap_length]
  | dropTemp i => simp [applyAct, dropAt_heap_length]
  | dealloc b => simp [applyAct, deallocAt_heap_length]
  | freeTemp => simp [applyAct, deallocAt_heap_length]
  | _ => simp [applyAct, State.push]

theorem length_le_runActs : ∀ (acts : List Act) (st : State),
    st.heap.length ≤ (runActs st acts).heap.length
  | [], _ => Nat.le_refl _
  | a :: as, st => Nat.le_trans (length_le_applyAct st a) (length_le_runActs as _)

theorem length_moveDrop (st : State) (l : Loc) :
    (applyAct (applyAct st (.moveOut l)) (.dropTemp l.2)).heap.length = st.heap.length + 1 := by
  simp [applyAct, dropAt_heap_length]

/-! ## Object status: liveness and the leaked flag -/

/-- The object at `b` exists, has liveness `L`, and is leaked. -/
def StatusIs (b : Nat) (L : Bool) (s : State) : Prop :=
  ∃ o, s.heap[b]? = some o ∧ o.live = L ∧ o.leaked = true

theorem statusIs_iff {b : Nat} {L : Bool} {s : State} :
    StatusIs b L s ↔ s.isLive b = L ∧ s.isLeaked b = true ∧ b < s.heap.length := by
  unfold StatusIs State.isLive State.isLeaked
  constructor
  · rintro ⟨o, ho, h1, h2⟩
    rw [ho]; exact ⟨h1, h2, (List.getElem?_eq_some_iff.mp ho).1⟩
  · rintro ⟨h1, h2, h3⟩
    cases ho : s.heap[b]? with
    | none => rw [List.getElem?_eq_none_iff] at ho; omega
    | some o => rw [ho] at h1 h2; exact ⟨o, rfl, h1, h2⟩

theorem StatusIs.lt {b : Nat} {L : Bool} {s : State} (h : StatusIs b L s) : b < s.heap.length :=
  (statusIs_iff.mp h).2.2

theorem StatusIs.congr {b : Nat} {L : Bool} {s s' : State} (h : StatusIs b L s)
    (he : s'.heap[b]? = s.heap[b]?) : StatusIs b L s' := by
  obtain ⟨o, ho, h1, h2⟩ := h
  exact ⟨o, he.trans ho, h1, h2⟩

theorem StatusIs.modifyObj {b c : Nat} {L : Bool} {s : State} {f : Obj → Obj}
    (hf : ∀ o, (f o).live = o.live ∧ (o.leaked = true → (f o).leaked = true))
    (h : StatusIs b L s) : StatusIs b L (s.modifyObj c f) := by
  obtain ⟨o, ho, h1, h2⟩ := h
  by_cases hc : c = b
  · subst hc
    refine ⟨f o, ?_, (hf o).1.trans h1, (hf o).2 h2⟩
    rw [modifyObj_heap, ho]; simp
  · exact ⟨o, (modifyObj_heap_ne f (Ne.symm hc)).trans ho, h1, h2⟩

theorem StatusIs.setLeaf {b : Nat} {L : Bool} {s : State} (l : Loc) (x : Option Leaf)
    (h : StatusIs b L s) : StatusIs b L (s.setLeaf l x) :=
  h.modifyObj (fun _ => ⟨rfl, id⟩)

theorem StatusIs.push {b : Nat} {L : Bool} {s : State} (o : Obj) (h : StatusIs b L s) :
    StatusIs b L (s.push o) :=
  h.congr (by rw [push_heap]; simp [h.lt])

theorem StatusIs.dropAt {b : Nat} {L : Bool} {s : State} (l : Loc) (h : StatusIs b L s) :
    StatusIs b L (s.dropAt l) := by
  unfold State.dropAt
  split
  · exact (h.setLeaf l none).congr rfl
  · exact h

/-- Primitive actions that keep the object at `b` allocated: every action except
deallocating `b` (directly, or as the most recently allocated object). -/
def ActKeepsAlloc (b : Nat) (s : State) : Act → Prop
  | .dealloc c => c ≠ b
  | .freeTemp => s.heap.length - 1 ≠ b
  | _ => True

theorem StatusIs.step {b : Nat} {L : Bool} {s : State} {a : Act} (ha : ActKeepsAlloc b s a)
    (h : StatusIs b L s) : StatusIs b L (applyAct s a) := by
  cases a with
  | alloc fs => exact (h.push _).congr rfl
  | pinObj c => exact h.modifyObj (fun _ => ⟨rfl, id⟩)
  | pinField l => exact h.modifyObj (fun _ => ⟨rfl, id⟩)
  | setSelf l =>
    simp only [applyAct]
    split
    · split
      · exact h.setLeaf _ _
      · exact h
    · exact h
  | register l =>
    simp only [applyAct]
    split
    · split
      · exact h.congr rfl
      · exact h
    · exact h
  | moveOut l => exact (h.setLeaf _ _).push _
  | moveObj c =>
    exact (h.modifyObj (c := c) (f := fun o => { o with fields := o.fields.map fun _ => none })
      (fun _ => ⟨rfl, id⟩)).push _
  | swap l l' => exact (h.setLeaf _ _).setLeaf _ _
  | dropLeaf l => exact h.dropAt l
  | dropTemp i => exact h.dropAt _
  | dealloc c =>
    exact h.congr (modifyObj_heap_ne _ (Ne.symm ha))
  | freeTemp =>
    exact h.congr (modifyObj_heap_ne _ (Ne.symm ha))
  | write l u => exact (h.setLeaf _ _).congr rfl
  | forget c => exact h.modifyObj (fun _ => ⟨rfl, fun _ => rfl⟩)

theorem moveDrop_keepsAlloc {b : Nat} (l : Loc) (s : State) (hb : b < s.heap.length) :
    Always (ActKeepsAlloc b) s (moveDrop l) := by
  refine ⟨trivial, trivial, ?_, trivial⟩
  show (applyAct (applyAct s (.moveOut l)) (.dropTemp l.2)).heap.length - 1 ≠ b
  rw [length_moveDrop]; omega

/-- Every operation other than `Op.drop b` keeps the object at `b` allocated. -/
theorem op_keepsAlloc (d : Decl) {b : Nat} (op : Op) (hop : op ≠ .drop b) (s : State)
    (hb : b < s.heap.length) : Always (ActKeepsAlloc b) s (expand d op) := by
  cases op with
  | new => exact ⟨trivial, trivial⟩
  | pin c => exact ⟨trivial, trivial⟩
  | projPin c i => exact ⟨trivial, trivial⟩
  | initSelf l => exact ⟨trivial, trivial⟩
  | link l => exact ⟨trivial, trivial⟩
  | replaceField c i =>
    show Always _ s (moveDrop (c, i) ++ [Act.write (c, i) (d.fieldTy i)])
    rw [always_append]
    exact ⟨moveDrop_keepsAlloc _ s hb, trivial, trivial⟩
  | swapField c c' i => exact ⟨trivial, trivial⟩
  | assignField c i => exact ⟨trivial, trivial, trivial⟩
  | replaceStruct c =>
    exact always_of_forall_mem _ (fun a ha _ => by
      simp only [expand, List.mem_cons, List.mem_map, List.mem_range] at ha
      rcases ha with rfl | ⟨i, -, rfl⟩ <;> trivial) s
  | take c i => exact moveDrop_keepsAlloc _ s hb
  | overwrite c i => exact ⟨trivial, trivial⟩
  | drop c =>
    have hcb : c ≠ b := fun h => hop (by rw [h])
    show Always _ s (dropActs d c)
    unfold dropActs
    obtain ⟨h1, hI1⟩ := always_flatMap (I := fun s => b < s.heap.length)
      (P := ActKeepsAlloc b) (dtorActs d c) d.dtor
      (fun x _ s' hs' => by
        refine ⟨?_, Nat.lt_of_lt_of_le hs' (length_le_runActs _ _)⟩
        cases x with
        | moveOut i => exact moveDrop_keepsAlloc _ s' hs'
        | overwrite i => exact ⟨trivial, trivial⟩) s hb
    obtain ⟨h2, hI2⟩ := always_flatMap (I := fun s => b < s.heap.length)
      (P := ActKeepsAlloc b) (glueActs d c) (List.range d.nfields)
      (fun i _ s' hs' => by
        refine ⟨?_, Nat.lt_of_lt_of_le hs' (length_le_runActs _ _)⟩
        unfold glueActs
        split
        · exact moveDrop_keepsAlloc _ s' hs'
        · exact ⟨trivial, trivial⟩) _ hI1
    rw [always_append, always_append]
    exact ⟨⟨h1, h2⟩, hcb, trivial⟩
  | forget c => exact ⟨trivial, trivial⟩

/-- **A leaked object is never dropped or deallocated by a safe continuation.** For every
declaration `d`, every state `st` in which the object at `b` is leaked, and every program
`rest` accepted by `SafeProgram d` from `st` (compiled by `compile d`), `rest` contains no
`Op.drop b`, and in every visited state the object at `b` has the liveness it had in `st`
and is still leaked. In particular `S`'s destructor, drop glue and deallocation never run
on it. -/
theorem leaked_object_never_dropped_or_deallocated (d : Decl) :
    ∀ (rest : List Op) (st : State) (b : Nat), st.isLeaked b = true →
      SafeProgram d st rest →
      Op.drop b ∉ rest ∧
        ∀ s ∈ states st (compile d rest), s.isLive b = st.isLive b ∧ s.isLeaked b = true := by
  suffices key : ∀ (rest : List Op) (st : State) (b : Nat) (L : Bool), StatusIs b L st →
      SafeProgram d st rest → Op.drop b ∉ rest ∧
        ∀ s ∈ states st (compile d rest), StatusIs b L s by
    intro rest st b hk hsafe
    have hb : b < st.heap.length := by
      unfold State.isLeaked at hk
      cases ho : st.heap[b]? with
      | none => rw [ho] at hk; cases hk
      | some o => exact (List.getElem?_eq_some_iff.mp ho).1
    have hst : StatusIs b (st.isLive b) st := statusIs_iff.mpr ⟨rfl, hk, hb⟩
    obtain ⟨h1, h2⟩ := key rest st b _ hst hsafe
    refine ⟨h1, fun s hs => ?_⟩
    have := statusIs_iff.mp (h2 s hs)
    exact ⟨this.1, this.2.1⟩
  intro rest
  induction rest with
  | nil =>
    intro st b L h _
    refine ⟨by simp, fun s hs => ?_⟩
    simp only [compile, List.flatMap_nil, states, List.mem_singleton] at hs
    subst hs; exact h
  | cons op ops ih =>
    intro st b L h hsafe
    have hop : op ≠ .drop b := by
      rintro rfl
      have := (statusIs_iff.mp h).2.1
      rw [hsafe.1.2] at this; cases this
    obtain ⟨hA, hB⟩ := always_inv (P := ActKeepsAlloc b) (I := StatusIs b L)
      (fun _ _ ha hs => hs.step ha) _ _ (op_keepsAlloc d op hop st h.lt) h
    obtain ⟨ih1, ih2⟩ := ih _ b L hB hsafe.2
    refine ⟨?_, fun s hs => ?_⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨fun he => hop he.symm, ih1⟩
    · simp only [compile, List.flatMap_cons] at hs
      rcases mem_states_append _ _ _ s hs with h1 | h1
      · exact hA s h1
      · exact ih2 s h1

/-! ## Continuations that never mention the object -/

/-- The operation names object `b` (as its own target, or as one of the objects of a swap). -/
def Op.Mentions (b : Nat) : Op → Prop
  | .new => False
  | .pin c => c = b
  | .projPin c _ => c = b
  | .initSelf l => l.1 = b
  | .link l => l.1 = b
  | .replaceField c _ => c = b
  | .swapField c c' _ => c = b ∨ c' = b
  | .assignField c _ => c = b
  | .replaceStruct c => c = b
  | .take c _ => c = b
  | .overwrite c _ => c = b
  | .drop c => c = b
  | .forget c => c = b

instance (b : Nat) (op : Op) : Decidable (op.Mentions b) := by
  cases op <;> unfold Op.Mentions <;> infer_instance

/-- Primitive actions that do not touch the object at `b`. -/
def ActAvoids (b : Nat) (s : State) : Act → Prop
  | .alloc _ => True
  | .pinObj c => c ≠ b
  | .pinField l => l.1 ≠ b
  | .setSelf l => l.1 ≠ b
  | .register _ => True
  | .moveOut l => l.1 ≠ b
  | .moveObj c => c ≠ b
  | .swap l l' => l.1 ≠ b ∧ l'.1 ≠ b
  | .dropLeaf l => l.1 ≠ b
  | .dropTemp _ => s.heap.length - 1 ≠ b
  | .dealloc c => c ≠ b
  | .freeTemp => s.heap.length - 1 ≠ b
  | .write l _ => l.1 ≠ b
  | .forget c => c ≠ b

theorem setLeaf_heap_ne {s : State} {l : Loc} (x : Option Leaf) {c : Nat} (h : l.1 ≠ c) :
    (s.setLeaf l x).heap[c]? = s.heap[c]? :=
  modifyObj_heap_ne _ (Ne.symm h)

theorem dropAt_heap_ne {s : State} {l : Loc} {c : Nat} (h : l.1 ≠ c) :
    (s.dropAt l).heap[c]? = s.heap[c]? := by
  unfold State.dropAt
  split
  · exact setLeaf_heap_ne none h
  · rfl

theorem dropAt_registry_keep {s : State} {l : Loc} {e : Loc × Nat} (h : l.1 ≠ e.1.1)
    (he : e ∈ s.registry) : e ∈ (s.dropAt l).registry := by
  unfold State.dropAt
  split
  · simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨he, fun heq => h ?_⟩
    rw [heq]
  · exact he

/-- The frame of an avoiding action, relative to a reference state `r`. -/
def Untouched (b : Nat) (r s : State) : Prop :=
  b < s.heap.length ∧ s.heap[b]? = r.heap[b]? ∧ ∀ e ∈ r.registry, e.1.1 = b → e ∈ s.registry

theorem Untouched.step {b : Nat} {r s : State} {a : Act} (ha : ActAvoids b s a)
    (h : Untouched b r s) : Untouched b r (applyAct s a) := by
  obtain ⟨hb, hh, hr⟩ := h
  refine ⟨Nat.lt_of_lt_of_le hb (length_le_applyAct s a), ?_, ?_⟩
  · refine Eq.trans ?_ hh
    cases a with
    | alloc fs => show (s.push _).heap[b]? = _; rw [push_heap]; simp [hb]
    | pinObj c => exact modifyObj_heap_ne _ (Ne.symm ha)
    | pinField l => exact modifyObj_heap_ne _ (Ne.symm ha)
    | setSelf l =>
      simp only [applyAct]
      split
      · split
        · exact setLeaf_heap_ne _ ha
        · rfl
      · rfl
    | register l =>
      simp only [applyAct]
      split
      · split <;> rfl
      · rfl
    | moveOut l =>
      show ((s.setLeaf l none).push _).heap[b]? = _
      rw [push_heap]; simp only [setLeaf_length, hb, ite_true]
      exact setLeaf_heap_ne _ ha
    | moveObj c =>
      show ((s.modifyObj c _).push _).heap[b]? = _
      rw [push_heap]; simp only [modifyObj_length, hb, ite_true]
      exact modifyObj_heap_ne _ (Ne.symm ha)
    | swap l l' =>
      show ((s.setLeaf l _).setLeaf l' _).heap[b]? = _
      rw [setLeaf_heap_ne _ ha.2, setLeaf_heap_ne _ ha.1]
    | dropLeaf l => exact dropAt_heap_ne ha
    | dropTemp i => exact dropAt_heap_ne ha
    | dealloc c => exact modifyObj_heap_ne _ (Ne.symm ha)
    | freeTemp => exact modifyObj_heap_ne _ (Ne.symm ha)
    | write l u => exact setLeaf_heap_ne _ ha
    | forget c => exact modifyObj_heap_ne _ (Ne.symm ha)
  · intro e he heb
    have hs := hr e he heb
    cases a with
    | register l =>
      simp only [applyAct]
      split
      · split
        · exact List.mem_cons_of_mem _ hs
        · exact hs
      · exact hs
    | setSelf l =>
      simp only [applyAct]
      split
      · split
        · exact hs
        · exact hs
      · exact hs
    | dropLeaf l => exact dropAt_registry_keep (by rw [heb]; exact ha) hs
    | dropTemp i => exact dropAt_registry_keep (by rw [heb]; exact ha) hs
    | alloc fs => exact hs
    | pinObj c => exact hs
    | pinField l => exact hs
    | moveOut l => exact hs
    | moveObj c => exact hs
    | swap l l' => exact hs
    | dealloc c => exact hs
    | freeTemp => exact hs
    | write l u => exact hs
    | forget c => exact hs

theorem moveDrop_avoids {b : Nat} (l : Loc) (hl : l.1 ≠ b) (s : State)
    (hb : b < s.heap.length) : Always (ActAvoids b) s (moveDrop l) := by
  refine ⟨hl, ?_, ?_, trivial⟩
  · show (applyAct s (.moveOut l)).heap.length - 1 ≠ b
    simp [applyAct]; omega
  · show (applyAct (applyAct s (.moveOut l)) (.dropTemp l.2)).heap.length - 1 ≠ b
    rw [length_moveDrop]; omega

/-- Every operation that does not mention `b` compiles to actions avoiding `b`. -/
theorem op_avoids (d : Decl) {b : Nat} (op : Op) (hop : ¬ op.Mentions b) (s : State)
    (hb : b < s.heap.length) : Always (ActAvoids b) s (expand d op) := by
  cases op with
  | new => exact ⟨trivial, trivial⟩
  | pin c => exact ⟨hop, trivial⟩
  | projPin c i => exact ⟨hop, trivial⟩
  | initSelf l => exact ⟨hop, trivial⟩
  | link l => exact ⟨trivial, trivial⟩
  | replaceField c i =>
    show Always _ s (moveDrop (c, i) ++ [Act.write (c, i) (d.fieldTy i)])
    rw [always_append]
    exact ⟨moveDrop_avoids (c, i) hop s hb, hop, trivial⟩
  | swapField c c' i =>
    simp only [Op.Mentions, not_or] at hop
    exact ⟨hop, trivial⟩
  | assignField c i => exact ⟨hop, hop, trivial⟩
  | replaceStruct c =>
    refine ⟨hop, always_of_forall_mem _ (fun a ha _ => ?_) _⟩
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact hop
  | take c i => exact moveDrop_avoids (c, i) hop s hb
  | overwrite c i => exact ⟨hop, trivial⟩
  | drop c =>
    show Always _ s (dropActs d c)
    unfold dropActs
    obtain ⟨h1, hI1⟩ := always_flatMap (I := fun s => b < s.heap.length)
      (P := ActAvoids b) (dtorActs d c) d.dtor
      (fun x _ s' hs' => by
        refine ⟨?_, Nat.lt_of_lt_of_le hs' (length_le_runActs _ _)⟩
        cases x with
        | moveOut i => exact moveDrop_avoids (c, i) hop s' hs'
        | overwrite i => exact ⟨hop, trivial⟩) s hb
    obtain ⟨h2, hI2⟩ := always_flatMap (I := fun s => b < s.heap.length)
      (P := ActAvoids b) (glueActs d c) (List.range d.nfields)
      (fun i _ s' hs' => by
        refine ⟨?_, Nat.lt_of_lt_of_le hs' (length_le_runActs _ _)⟩
        unfold glueActs
        split
        · exact moveDrop_avoids (c, i) hop s' hs'
        · exact ⟨hop, trivial⟩) _ hI1
    rw [always_append, always_append]
    exact ⟨⟨h1, h2⟩, hop, trivial⟩
  | forget c => exact ⟨hop, trivial⟩

/-- **An object that a continuation never mentions is left unchanged.** For every
declaration `d`, every state `st` with an object at address `b`, and every program `rest`
none of whose operations mentions `b` (compiled by `compile d`; no safety assumption), in
every visited state the object at `b` (its leaves, self-pointers, pinned flags, liveness and
leaked flag) is the one of `st`, and every list entry of `st` located in `b` is still
present. -/
theorem unmentioned_object_unchanged (d : Decl) (rest : List Op) (st : State) (b : Nat)
    (hb : b < st.heap.length) (hmention : ∀ op ∈ rest, ¬ op.Mentions b) :
    ∀ s ∈ states st (compile d rest),
      s.heap[b]? = st.heap[b]? ∧ ∀ e ∈ st.registry, e.1.1 = b → e ∈ s.registry := by
  suffices key : ∀ (rest : List Op) (s0 : State), (∀ op ∈ rest, ¬ op.Mentions b) →
      Untouched b st s0 → ∀ s ∈ states s0 (compile d rest), Untouched b st s by
    intro s hs
    have := key rest st hmention ⟨hb, rfl, fun _ h _ => h⟩ s hs
    exact ⟨this.2.1, this.2.2⟩
  intro rest
  induction rest with
  | nil =>
    intro s0 _ h s hs
    simp only [compile, List.flatMap_nil, states, List.mem_singleton] at hs
    subst hs; exact h
  | cons op ops ih =>
    intro s0 hm h s hs
    obtain ⟨hA, hB⟩ := always_inv (P := ActAvoids b) (I := Untouched b st)
      (fun _ _ ha hs => hs.step ha) _ _
      (op_avoids d op (hm op (List.mem_cons_self ..)) s0 h.1) h
    simp only [compile, List.flatMap_cons] at hs
    rcases mem_states_append _ _ _ s hs with h1 | h1
    · exact hA s h1
    · exact ih _ (fun o ho => hm o (List.mem_cons_of_mem _ ho)) hB s h1

/-- Leaf-level reading of `unmentioned_object_unchanged`: every field of `b` holds the same
value (with the same self-pointer), and every list entry into `b` is still present and finds
the same value. -/
theorem unmentioned_object_leaves_and_entries (d : Decl) (rest : List Op) (st : State)
    (b : Nat) (hb : b < st.heap.length) (hmention : ∀ op ∈ rest, ¬ op.Mentions b) :
    ∀ s ∈ states st (compile d rest),
      (∀ i, s.leafAt (b, i) = st.leafAt (b, i)) ∧
        ∀ e ∈ st.registry, e.1.1 = b → e ∈ s.registry ∧ s.leafAt e.1 = st.leafAt e.1 := by
  intro s hs
  obtain ⟨h1, h2⟩ := unmentioned_object_unchanged d rest st b hb hmention s hs
  refine ⟨fun i => leafAt_congr h1, fun e he heb => ⟨h2 e he heb, ?_⟩⟩
  exact leafAt_congr (by rw [heb]; exact h1)

end Toy.Pin
