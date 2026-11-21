import ToyPin.Lemmas

/-!
# The core pinning discipline (act level)

`addrInv_of_noPinnedMove_of_dropGuarantee`: along any sequence of primitive actions from
the empty heap in which (1) no pinned non-`Unpin` value is moved and (2) the memory of no
pinned non-`Unpin` value is invalidated or reused before its destructor runs, both
address-sensitive invariants (`SelfRefOK`, `ListOK`) hold at every visited state.

Each of the two hypotheses is tight, with one-object, one-field witness traces
(`noPinnedMove_tight`, `dropGuarantee_tight`); neither is necessary on an individual trace
(`noPinnedMove_not_necessary_on_a_trace`, `dropGuaranteeAct_not_necessary_on_a_trace`).
-/

namespace Toy.Pin

namespace State

@[simp] theorem leafAt_withNextId (st : State) (n : Nat) (l : Loc) :
    ({ st with nextId := n } : State).leafAt l = st.leafAt l := rfl

@[simp] theorem isPinnedLoc_withNextId (st : State) (n : Nat) (l : Loc) :
    ({ st with nextId := n } : State).isPinnedLoc l = st.isPinnedLoc l := rfl

@[simp] theorem leafAt_withRegistry (st : State) (r : List (Loc × Nat)) (l : Loc) :
    ({ st with registry := r } : State).leafAt l = st.leafAt l := rfl

@[simp] theorem isPinnedLoc_withRegistry (st : State) (r : List (Loc × Nat)) (l : Loc) :
    ({ st with registry := r } : State).isPinnedLoc l = st.isPinnedLoc l := rfl

theorem leafAt_clear {st : State} {b : Nat} {f : Obj → Obj}
    (hf : ∀ o, (f o).fields = o.fields.map fun _ => none) (i : Nat) :
    (st.modifyObj b f).leafAt (b, i) = none := by
  unfold leafAt
  rw [modifyObj_heap]
  simp only [ite_true]
  cases st.heap[b]? with
  | none => rfl
  | some o =>
    simp only [Option.map_some, Obj.leaf, hf, List.getElem?_map]
    cases o.fields[i]? <;> rfl

theorem isPinnedLoc_pinField_mono (st : State) (b i : Nat) (l : Loc)
    (h : st.isPinnedLoc l = true) :
    (st.modifyObj b fun o => { o with pinnedFields := i :: o.pinnedFields }).isPinnedLoc l
      = true := by
  unfold isPinnedLoc at *
  rw [modifyObj_heap]
  by_cases hb : b = l.1
  · simp only [hb, ite_true]
    cases ho : st.heap[l.1]? with
    | none => simp [ho] at h
    | some o => simp only [ho, decide_eq_true_eq] at h; simp [h]
  · simp [hb, h]

end State

open State

/-- Strengthened inductive invariant behind the core theorem: every set self-pointer points
to the value's own location, which is pinned and holds a non-`Unpin` value; every list entry
finds its value at a pinned location, and that value is not `Unpin`. -/
def CoreInv (st : State) : Prop :=
  (∀ l v, st.leafAt l = some v →
      v.selfPtr = none ∨ (v.selfPtr = some l ∧ st.isPinnedLoc l = true ∧ v.unpin = false)) ∧
  (∀ e ∈ st.registry, ∃ v, st.leafAt e.1 = some v ∧ v.id = e.2 ∧
      st.isPinnedLoc e.1 = true ∧ v.unpin = false)

theorem CoreInv.addrInv {st : State} (h : CoreInv st) : AddrInv st := by
  refine ⟨fun l v hv => ?_, fun e he => ?_⟩
  · rcases h.1 l v hv with h1 | ⟨h1, -, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · obtain ⟨v, hv, hid, -, -⟩ := h.2 e he
    simp [hv, hid]

theorem coreInv_init : CoreInv State.init := by
  refine ⟨fun l v hv => ?_, fun e he => ?_⟩
  · simp [State.leafAt, State.init] at hv
  · simp [State.init] at he

theorem CoreInv.selfPtr_none {st : State} (h : CoreInv st) {l : Loc} {v : Leaf}
    (hv : st.leafAt l = some v) (hp : ¬ PinnedNonUnpin st l) : v.selfPtr = none := by
  rcases h.1 l v hv with h1 | ⟨-, hpin, hu⟩
  · exact h1
  · exact absurd ⟨hpin, by simp [hv, hu]⟩ hp

theorem CoreInv.no_entry {st : State} (h : CoreInv st) {l : Loc}
    (hp : ¬ PinnedNonUnpin st l) : ∀ e ∈ st.registry, e.1 ≠ l := by
  intro e he heq
  obtain ⟨v, hv, -, hpin, hu⟩ := h.2 e he
  subst heq
  exact hp ⟨hpin, by simp [hv, hu]⟩

theorem CoreInv.entry_lt {st : State} (h : CoreInv st) :
    ∀ e ∈ st.registry, e.1.1 < st.heap.length := by
  intro e he
  obtain ⟨v, hv, -, -, -⟩ := h.2 e he
  exact (leafAt_some_bounds hv).1

/-- Frame principle: if pinned locations stay pinned, every leaf of the new state is an
old leaf at the same location or has no self-pointer, and the list only loses entries whose
locations are unchanged, the invariant is preserved. -/
theorem CoreInv.of_frame {st st' : State} (h : CoreInv st)
    (hpin : ∀ l, st.isPinnedLoc l = true → st'.isPinnedLoc l = true)
    (hleaf : ∀ l v, st'.leafAt l = some v → st.leafAt l = some v ∨ v.selfPtr = none)
    (hreg : ∀ e ∈ st'.registry, e ∈ st.registry)
    (hregleaf : ∀ e ∈ st'.registry, st'.leafAt e.1 = st.leafAt e.1) : CoreInv st' := by
  refine ⟨fun l v hv => ?_, fun e he => ?_⟩
  · rcases hleaf l v hv with hold | hnone
    · rcases h.1 l v hold with h1 | ⟨h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, hpin l h2, h3⟩
    · exact Or.inl hnone
  · obtain ⟨v, hv, hid, hp, hu⟩ := h.2 e (hreg e he)
    exact ⟨v, by rw [hregleaf e he]; exact hv, hid, hpin _ hp, hu⟩

/-- Leaves at existing addresses survive a `push`; the pushed object contributes leaves
described by `Obj.leaf`. -/
theorem leafAt_push_cases {st : State} {o : Obj} {l : Loc} {v : Leaf}
    (h : (st.push o).leafAt l = some v) :
    (l.1 < st.heap.length ∧ st.leafAt l = some v) ∨ (l.1 = st.heap.length ∧ o.leaf l.2 = some v) := by
  by_cases h1 : l.1 < st.heap.length
  · exact Or.inl ⟨h1, by rw [← leafAt_push_lt o h1]; exact h⟩
  · by_cases h2 : l.1 = st.heap.length
    · refine Or.inr ⟨h2, ?_⟩
      have : l = (st.heap.length, l.2) := Prod.ext h2 rfl
      rw [this, leafAt_push_eq] at h; exact h
    · rw [leafAt_push_gt o (by omega)] at h; simp at h

theorem isPinnedLoc_push_of {st : State} {o : Obj} {l : Loc} (h : st.isPinnedLoc l = true) :
    (st.push o).isPinnedLoc l = true := by
  rw [isPinnedLoc_push_lt o (isPinnedLoc_lt h)]; exact h

theorem leafAt_setLeaf_cases {st : State} {l m : Loc} {x : Option Leaf} {v : Leaf}
    (h : (st.setLeaf l x).leafAt m = some v) : (m = l ∧ x = some v) ∨ (m ≠ l ∧ st.leafAt m = some v) := by
  by_cases hm : m = l
  · subst hm
    rcases leafAt_setLeaf_self st m x with h1 | h1 <;> rw [h1] at h
    · exact Or.inl ⟨rfl, h⟩
    · simp at h
  · exact Or.inr ⟨hm, by rw [← leafAt_setLeaf_ne x hm]; exact h⟩

/-- The deallocation and clearing updates used by `dealloc`, `freeTemp`, `moveObj`. -/
theorem CoreInv.clear_obj {st : State} (h : CoreInv st) (b : Nat) (f : Obj → Obj)
    (hf : ∀ o, (f o).fields = o.fields.map fun _ => none)
    (hpf : ∀ o, (f o).pinnedFields = o.pinnedFields)
    (hp : ∀ i < st.width b, ¬ PinnedNonUnpin st (b, i)) :
    CoreInv (st.modifyObj b f) := by
  have hentry : ∀ e ∈ st.registry, e.1.1 ≠ b := by
    intro e he heq
    obtain ⟨v, hv, -, hpin, hu⟩ := h.2 e he
    have hbd := leafAt_some_bounds hv
    have : e.1 = (b, e.1.2) := Prod.ext heq rfl
    rw [heq] at hbd
    exact hp e.1.2 hbd.2 (by rw [← this]; exact ⟨hpin, by simp [hv, hu]⟩)
  refine h.of_frame (fun l hl => by rw [isPinnedLoc_modifyObj_of_pf hpf]; exact hl) ?_
    (fun e he => he) ?_
  · intro l v hv
    by_cases hb : l.1 = b
    · have : l = (b, l.2) := Prod.ext hb rfl
      rw [this, leafAt_clear hf] at hv; simp at hv
    · left; rw [← leafAt_congr (modifyObj_heap_ne f hb)]; exact hv
  · intro e he
    exact leafAt_congr (modifyObj_heap_ne f (hentry e he))

theorem CoreInv.dropAt {st : State} (h : CoreInv st) (l : Loc) : CoreInv (st.dropAt l) := by
  unfold State.dropAt
  cases hv : st.leafAt l with
  | none => exact h
  | some v =>
    simp only
    have hent : ∀ e ∈ st.registry.filter (fun e => decide (e ≠ (l, v.id))), e.1 ≠ l := by
      intro e he heq
      simp only [List.mem_filter, decide_eq_true_eq] at he
      obtain ⟨w, hw, hid, -, -⟩ := h.2 e he.1
      rw [heq, hv] at hw
      cases hw
      exact he.2 (Prod.ext heq hid.symm)
    refine h.of_frame (fun m hm => by simpa using hm) ?_ ?_ ?_
    · intro m w hw
      simp only [leafAt_withRegistry] at hw
      rcases leafAt_setLeaf_cases hw with ⟨-, h2⟩ | ⟨-, h2⟩
      · simp at h2
      · exact Or.inl h2
    · intro e he
      simp only [List.mem_filter] at he
      exact he.1
    · intro e he
      simp only [leafAt_withRegistry]
      exact leafAt_setLeaf_ne none (hent e he)

/-- One step preserves the strengthened invariant when the action respects both parts of
the pinning contract. -/
theorem CoreInv.step {st : State} (h : CoreInv st) (a : Act)
    (hm : NoPinnedMove st a) (hd : DropGuaranteeAct st a) : CoreInv (applyAct st a) := by
  cases a with
  | alloc fs =>
    have key : ∀ l, (applyAct st (.alloc fs)).leafAt l =
        (st.push (Obj.fresh (mkFields st.nextId fs))).leafAt l := fun _ => rfl
    have keyp : ∀ l, (applyAct st (.alloc fs)).isPinnedLoc l =
        (st.push (Obj.fresh (mkFields st.nextId fs))).isPinnedLoc l := fun _ => rfl
    refine h.of_frame (fun l hl => by rw [keyp]; exact isPinnedLoc_push_of hl) ?_
      (fun e he => he) ?_
    · intro l v hv
      rw [key] at hv
      rcases leafAt_push_cases hv with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inl h2
      · exact Or.inr (leaf_mkFields_selfPtr h2)
    · intro e he
      rw [key]
      exact leafAt_push_lt _ (h.entry_lt e he)
  | pinObj b =>
    have key : ∀ l, (applyAct st (.pinObj b)).leafAt l = st.leafAt l := fun l =>
      leafAt_modifyObj_of_fields (f := fun o => { o with pinned := true }) (fun _ => rfl) l
    have keyp : ∀ l, (applyAct st (.pinObj b)).isPinnedLoc l = st.isPinnedLoc l := fun l =>
      isPinnedLoc_modifyObj_of_pf (f := fun o => { o with pinned := true }) (fun _ => rfl) l
    refine h.of_frame (fun l hl => by rw [keyp]; exact hl) (fun l v hv => Or.inl (by rwa [key] at hv))
      (fun e he => he) (fun e _ => key _)
  | pinField l =>
    have key : ∀ m, (applyAct st (.pinField l)).leafAt m = st.leafAt m := fun m =>
      leafAt_modifyObj_of_fields (f := fun o => { o with pinnedFields := l.2 :: o.pinnedFields })
        (fun _ => rfl) m
    refine h.of_frame (fun m hm => isPinnedLoc_pinField_mono st l.1 l.2 m hm)
      (fun m v hv => Or.inl (by rwa [key] at hv)) (fun e he => he) (fun e _ => key _)
  | setSelf l =>
    simp only [applyAct]
    cases hv : st.leafAt l with
    | none => exact h
    | some v =>
      simp only
      split
      · rename_i hc
        obtain ⟨hpin, hu⟩ := hc
        refine ⟨fun m w hw => ?_, fun e he => ?_⟩
        · rcases leafAt_setLeaf_cases hw with ⟨rfl, h2⟩ | ⟨hne, h2⟩
          · cases h2; exact Or.inr ⟨rfl, by simpa using hpin, hu⟩
          · rcases h.1 m w h2 with h3 | ⟨h3, h4, h5⟩
            · exact Or.inl h3
            · exact Or.inr ⟨h3, by simpa using h4, h5⟩
        · obtain ⟨w, hw, hid, hp, hu'⟩ := h.2 e he
          by_cases heq : e.1 = l
          · have hvw : v = w := by rw [heq, hv] at hw; exact Option.some.inj hw
            refine ⟨{ v with selfPtr := some l }, ?_, by rw [hvw]; exact hid, by simpa using hp,
              by rw [hvw]; exact hu'⟩
            rw [heq]; exact leafAt_setLeaf_self_of_some _ hv
          · exact ⟨w, by rw [leafAt_setLeaf_ne _ heq]; exact hw, hid, by simpa using hp, hu'⟩
      · exact h
  | register l =>
    simp only [applyAct]
    cases hv : st.leafAt l with
    | none => exact h
    | some v =>
      simp only
      split
      · rename_i hc
        obtain ⟨hpin, hu⟩ := hc
        refine ⟨fun m w hw => ?_, fun e he => ?_⟩
        · simp only [leafAt_withRegistry] at hw
          rcases h.1 m w hw with h3 | ⟨h3, h4, h5⟩
          · exact Or.inl h3
          · exact Or.inr ⟨h3, by simpa using h4, h5⟩
        · simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨v, by simpa using hv, rfl, by simpa using hpin, hu⟩
          · obtain ⟨w, hw, hid, hp, hu'⟩ := h.2 e he
            exact ⟨w, by simpa using hw, hid, by simpa using hp, hu'⟩
      · exact h
  | moveOut l =>
    simp only [NoPinnedMove] at hm
    simp only [applyAct]
    refine h.of_frame (fun m hm' => isPinnedLoc_push_of (by simpa using hm')) ?_
      (fun e he => he) ?_
    · intro m w hw
      rcases leafAt_push_cases hw with ⟨-, h2⟩ | ⟨-, h2⟩
      · rcases leafAt_setLeaf_cases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
        · simp at h3
        · exact Or.inl h3
      · rw [leaf_tempFields] at h2
        split at h2
        · exact Or.inr (h.selfPtr_none h2 hm)
        · simp at h2
    · intro e he
      have hlt : e.1.1 < (st.setLeaf l none).heap.length := by simpa using h.entry_lt e he
      rw [leafAt_push_lt _ hlt]
      exact leafAt_setLeaf_ne none (h.no_entry hm e he)
  | moveObj b =>
    simp only [NoPinnedMove] at hm
    simp only [applyAct]
    have hclr := h.clear_obj b (fun o => { o with fields := o.fields.map fun _ => none })
      (fun _ => rfl) (fun _ => rfl) hm
    refine hclr.of_frame (fun m hm' => isPinnedLoc_push_of hm') ?_ (fun e he => he) ?_
    · intro m w hw
      rcases leafAt_push_cases hw with ⟨-, h2⟩ | ⟨hm1, h2⟩
      · exact Or.inl h2
      · right
        have hb : st.leafAt (b, m.2) = some w := by
          unfold State.leafAt
          cases ho : st.heap[b]? with
          | none => simp [ho, Obj.leaf, Obj.fresh] at h2
          | some o => simpa [ho, Obj.leaf, Obj.fresh] using h2
        exact h.selfPtr_none hb (hm m.2 (leafAt_some_bounds hb).2)
    · intro e he
      exact leafAt_push_lt _ (by simpa using h.entry_lt e he)
  | swap l l' =>
    simp only [NoPinnedMove] at hm
    simp only [applyAct]
    refine h.of_frame (fun m hm' => by simpa using hm') ?_ (fun e he => he) ?_
    · intro m w hw
      rcases leafAt_setLeaf_cases hw with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inr (h.selfPtr_none h2 hm.1)
      · rcases leafAt_setLeaf_cases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
        · exact Or.inr (h.selfPtr_none h3 hm.2)
        · exact Or.inl h3
    · intro e he
      simp only [setLeaf_registry] at he
      rw [leafAt_setLeaf_ne _ (h.no_entry hm.2 e he), leafAt_setLeaf_ne _ (h.no_entry hm.1 e he)]
  | dropLeaf l => exact h.dropAt l
  | dropTemp i => exact h.dropAt _
  | dealloc b =>
    simp only [DropGuaranteeAct] at hd
    exact h.clear_obj b _ (fun _ => rfl) (fun _ => rfl) hd
  | freeTemp =>
    simp only [DropGuaranteeAct] at hd
    exact h.clear_obj _ _ (fun _ => rfl) (fun _ => rfl) hd
  | write l u =>
    simp only [DropGuaranteeAct] at hd
    have key : ∀ m, (applyAct st (.write l u)).leafAt m =
        (st.setLeaf l (some ⟨st.nextId, u, none⟩)).leafAt m := fun _ => rfl
    have keyp : ∀ m, (applyAct st (.write l u)).isPinnedLoc m = st.isPinnedLoc m := fun m =>
      isPinnedLoc_setLeaf st l _ m
    refine h.of_frame (fun m hm' => by rw [keyp]; exact hm') ?_ (fun e he => he) ?_
    · intro m w hw
      rw [key] at hw
      rcases leafAt_setLeaf_cases hw with ⟨-, h2⟩ | ⟨-, h2⟩
      · cases h2; exact Or.inr rfl
      · exact Or.inl h2
    · intro e he
      rw [key]
      exact leafAt_setLeaf_ne _ (h.no_entry hd e he)
  | forget b =>
    have key : ∀ l, (applyAct st (.forget b)).leafAt l = st.leafAt l := fun l =>
      leafAt_modifyObj_of_fields (f := fun o => { o with leaked := true }) (fun _ => rfl) l
    have keyp : ∀ l, (applyAct st (.forget b)).isPinnedLoc l = st.isPinnedLoc l := fun l =>
      isPinnedLoc_modifyObj_of_pf (f := fun o => { o with leaked := true }) (fun _ => rfl) l
    refine h.of_frame (fun l hl => by rw [keyp]; exact hl) (fun l v hv => Or.inl (by rwa [key] at hv))
      (fun e he => he) (fun e _ => key _)

theorem coreInv_states :
    ∀ (acts : List Act) (st : State), CoreInv st → Always NoPinnedMove st acts →
      Always DropGuaranteeAct st acts → ∀ s ∈ states st acts, CoreInv s
  | [], st, h, _, _ => by
    intro s hs
    simp only [states, List.mem_singleton] at hs
    subst hs; exact h
  | a :: as, st, h, hm, hd => by
    intro s hs
    simp only [states, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact h
    · exact coreInv_states as _ (h.step a hm.1 hd.1) hm.2 hd.2 s hs

/-- **Core pinning discipline.** For every sequence of primitive actions run from
the empty heap: if no action moves a pinned non-`Unpin` value (`NoPinnedMove`) and no action
invalidates or reuses the memory of a pinned non-`Unpin` value before its destructor runs
(`DropGuaranteeAct`), then the self-reference invariant and the intrusive-list invariant hold
in every visited state. -/
theorem addrInv_of_noPinnedMove_of_dropGuarantee (acts : List Act)
    (hmove : Always NoPinnedMove State.init acts)
    (hdrop : Always DropGuaranteeAct State.init acts) :
    ∀ s ∈ states State.init acts, AddrInv s :=
  fun s hs => (coreInv_states acts _ coreInv_init hmove hdrop s hs).addrInv

end Toy.Pin
