import ToyPin.Structural

/-!
# Soundness of structural pinning under conditions (a)–(f)

`addrInv_of_structural_pinning_conditions`: if a struct declaration satisfies conditions
(a)–(f), every safe program keeps both address-sensitive invariants at every state.

The proof reduces to the core theorem `addrInv_of_noPinnedMove_of_dropGuarantee`: under
(a)–(f), every primitive action produced by a safe program respects `NoPinnedMove` and
`DropGuaranteeAct`.
-/

namespace Toy.Pin

open State

/-! ## Generic facts about action lists -/

theorem runActs_append : ∀ (st : State) (as bs : List Act),
    runActs st (as ++ bs) = runActs (runActs st as) bs
  | _, [], _ => rfl
  | st, a :: as, bs => runActs_append (applyAct st a) as bs

theorem always_append {P : State → Act → Prop} : ∀ (st : State) (as bs : List Act),
    Always P st (as ++ bs) ↔ Always P st as ∧ Always P (runActs st as) bs
  | st, [], bs => by simp [Always, runActs]
  | st, a :: as, bs => by
    simp only [List.cons_append, Always, runActs]
    rw [always_append (applyAct st a) as bs, and_assoc]

theorem always_mono {P Q : State → Act → Prop} (hPQ : ∀ s a, P s a → Q s a) :
    ∀ (st : State) (as : List Act), Always P st as → Always Q st as
  | _, [], _ => trivial
  | st, a :: as, h => ⟨hPQ st a h.1, always_mono hPQ (applyAct st a) as h.2⟩

/-- An invariant-carrying induction principle for `Always`. -/
theorem always_of_forall {P : State → Act → Prop} {I : State → Prop} :
    ∀ (as : List Act), (∀ a ∈ as, ∀ s, I s → P s a ∧ I (applyAct s a)) →
      ∀ st, I st → Always P st as ∧ I (runActs st as)
  | [], _, _, hI => ⟨trivial, hI⟩
  | a :: as, h, st, hI => by
    obtain ⟨hp, hI'⟩ := h a (List.mem_cons_self ..) st hI
    obtain ⟨h1, h2⟩ := always_of_forall as (fun b hb => h b (List.mem_cons_of_mem _ hb)) _ hI'
    exact ⟨⟨hp, h1⟩, h2⟩

/-- Block version: for `xs.flatMap f`, each block preserves the invariant. -/
theorem always_flatMap {α : Type} {P : State → Act → Prop} {I : State → Prop}
    (f : α → List Act) : ∀ (xs : List α),
      (∀ x ∈ xs, ∀ s, I s → Always P s (f x) ∧ I (runActs s (f x))) →
      ∀ st, I st → Always P st (xs.flatMap f) ∧ I (runActs st (xs.flatMap f))
  | [], _, _, hI => ⟨trivial, hI⟩
  | x :: xs, h, st, hI => by
    simp only [List.flatMap_cons]
    obtain ⟨h1, hI1⟩ := h x (List.mem_cons_self ..) st hI
    obtain ⟨h2, hI2⟩ := always_flatMap f xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) _ hI1
    rw [always_append, runActs_append]
    exact ⟨⟨h1, h2⟩, hI2⟩

/-! ## Frame facts for `dropAt`, `deallocAt`, `push` -/

namespace State

theorem dropAt_heap_length (st : State) (l : Loc) :
    (st.dropAt l).heap.length = st.heap.length := by
  unfold dropAt; split <;> simp

theorem isPinnedLoc_dropAt (st : State) (l m : Loc) :
    (st.dropAt l).isPinnedLoc m = st.isPinnedLoc m := by
  unfold dropAt; split
  · exact isPinnedLoc_setLeaf st l none m
  · rfl

theorem isPinned_dropAt (st : State) (l : Loc) (c : Nat) :
    (st.dropAt l).isPinned c = st.isPinned c := by
  unfold dropAt; split
  · exact isPinned_setLeaf st l none c
  · rfl

theorem leafAt_dropAt_cases {st : State} {l m : Loc} {v : Leaf}
    (h : (st.dropAt l).leafAt m = some v) : st.leafAt m = some v := by
  unfold dropAt at h; split at h
  · simp only [leafAt_withRegistry] at h
    rcases leafAt_setLeaf_cases h with ⟨-, h2⟩ | ⟨-, h2⟩
    · simp at h2
    · exact h2
  · exact h

theorem leafAt_dropAt_self (st : State) (l : Loc) : (st.dropAt l).leafAt l = none := by
  unfold dropAt; split
  · rename_i v hv
    simp only [leafAt_withRegistry]
    rw [leafAt_setLeaf_self_of_some none hv]
  · assumption

theorem leafAt_dropAt_of_none {st : State} {m : Loc} (l : Loc) (h : st.leafAt m = none) :
    (st.dropAt l).leafAt m = none := by
  cases hv : (st.dropAt l).leafAt m with
  | none => rfl
  | some v => rw [leafAt_dropAt_cases hv] at h; cases h

theorem deallocAt_heap_length (st : State) (b : Nat) :
    (st.deallocAt b).heap.length = st.heap.length := by
  unfold deallocAt; simp

theorem isPinnedLoc_deallocAt (st : State) (b : Nat) (m : Loc) :
    (st.deallocAt b).isPinnedLoc m = st.isPinnedLoc m := by
  unfold deallocAt
  exact isPinnedLoc_modifyObj_of_pf
    (f := fun o => { o with fields := o.fields.map fun _ => none, live := false })
    (fun _ => rfl) m

theorem isPinned_deallocAt (st : State) (b c : Nat) :
    (st.deallocAt b).isPinned c = st.isPinned c := by
  unfold deallocAt
  exact isPinned_modifyObj_of_pinned
    (f := fun o => { o with fields := o.fields.map fun _ => none, live := false })
    (fun _ => rfl) c

theorem leafAt_deallocAt_cases {st : State} {b : Nat} {m : Loc} {v : Leaf}
    (h : (st.deallocAt b).leafAt m = some v) : st.leafAt m = some v := by
  unfold deallocAt at h
  by_cases hb : m.1 = b
  · have : m = (b, m.2) := Prod.ext hb rfl
    rw [this, leafAt_clear (fun _ => rfl)] at h; cases h
  · rw [← leafAt_congr (modifyObj_heap_ne _ hb)]; exact h

theorem isPinned_push_imp {st : State} {fs : List (Option Leaf)} {c : Nat}
    (h : (st.push (Obj.fresh fs)).isPinned c = true) : st.isPinned c = true := by
  by_cases hc : c < st.heap.length
  · rwa [isPinned_push_lt _ hc] at h
  · rw [isPinned_push_fresh st fs c (by omega)] at h; cases h

theorem isPinnedLoc_push_imp {st : State} {fs : List (Option Leaf)} {l : Loc}
    (h : (st.push (Obj.fresh fs)).isPinnedLoc l = true) : st.isPinnedLoc l = true := by
  by_cases hc : l.1 < st.heap.length
  · rwa [isPinnedLoc_push_lt _ hc] at h
  · rw [isPinnedLoc_push_fresh st fs l (by omega)] at h; cases h

end State

theorem leaf_moveObj (st : State) (b j : Nat) :
    (Obj.fresh (match st.heap[b]? with
      | some o => o.fields
      | none => [])).leaf j = st.leafAt (b, j) := by
  unfold State.leafAt
  cases st.heap[b]? <;> simp [Obj.leaf, Obj.fresh]

/-! ## How actions change pinned flags -/

/-- An action other than `pinObj` never makes an object pinned. -/
theorem isPinned_applyAct_imp (st : State) (a : Act) (ha : ∀ c, a ≠ .pinObj c) (b : Nat)
    (h : (applyAct st a).isPinned b = true) : st.isPinned b = true := by
  cases a with
  | alloc fs => exact isPinned_push_imp (st := st) h
  | pinObj c => exact absurd rfl (ha c)
  | pinField l =>
    have : (applyAct st (.pinField l)).isPinned b = st.isPinned b :=
      isPinned_modifyObj_of_pinned
        (f := fun o => { o with pinnedFields := l.2 :: o.pinnedFields }) (fun _ => rfl) b
    rwa [this] at h
  | setSelf l =>
    simp only [applyAct] at h
    split at h
    · split at h
      · rwa [isPinned_setLeaf] at h
      · exact h
    · exact h
  | register l =>
    simp only [applyAct] at h
    split at h
    · split at h
      · exact h
      · exact h
    · exact h
  | moveOut l =>
    have := isPinned_push_imp (st := st.setLeaf l none) h
    rwa [isPinned_setLeaf] at this
  | moveObj c =>
    have := isPinned_push_imp h
    rwa [isPinned_modifyObj_of_pinned
      (f := fun o => { o with fields := o.fields.map fun _ => none }) (fun _ => rfl)] at this
  | swap l l' =>
    simp only [applyAct, isPinned_setLeaf] at h; exact h
  | dropLeaf l => simp only [applyAct, isPinned_dropAt] at h; exact h
  | dropTemp i => simp only [applyAct, isPinned_dropAt] at h; exact h
  | dealloc c => simp only [applyAct, isPinned_deallocAt] at h; exact h
  | freeTemp => simp only [applyAct, isPinned_deallocAt] at h; exact h
  | write l u =>
    have : (applyAct st (.write l u)).isPinned b = (st.setLeaf l _).isPinned b := rfl
    rw [this, isPinned_setLeaf] at h; exact h
  | forget c =>
    have : (applyAct st (.forget c)).isPinned b = st.isPinned b :=
      isPinned_modifyObj_of_pinned (f := fun o => { o with leaked := true }) (fun _ => rfl) b
    rwa [this] at h

/-- Pinned objects stay pinned. -/
theorem isPinned_applyAct_mono (st : State) (a : Act) (c : Nat) (h : st.isPinned c = true) :
    (applyAct st a).isPinned c = true := by
  have hlt := isPinned_lt h
  cases a with
  | pinObj b =>
    simp only [applyAct, isPinned] at h ⊢
    rw [modifyObj_heap]
    by_cases hb : b = c
    · simp only [hb, ite_true]
      cases ho : st.heap[c]? with
      | none => simp [ho] at h
      | some o => simp
    · simp only [hb, ite_false]; exact h
  | alloc fs =>
    show (st.push _).isPinned c = true
    rw [isPinned_push_lt _ hlt]; exact h
  | pinField l =>
    rw [show (applyAct st (.pinField l)).isPinned c = st.isPinned c from
      isPinned_modifyObj_of_pinned
        (f := fun o => { o with pinnedFields := l.2 :: o.pinnedFields }) (fun _ => rfl) c]
    exact h
  | setSelf l =>
    simp only [applyAct]
    split
    · split
      · rw [isPinned_setLeaf]; exact h
      · exact h
    · exact h
  | register l =>
    simp only [applyAct]
    split
    · split
      · exact h
      · exact h
    · exact h
  | moveOut l =>
    simp only [applyAct]
    rw [isPinned_push_lt _ (by simpa using hlt), isPinned_setLeaf]; exact h
  | moveObj b =>
    simp only [applyAct]
    rw [isPinned_push_lt _ (by simpa using hlt), isPinned_modifyObj_of_pinned
      (f := fun o => { o with fields := o.fields.map fun _ => none }) (fun _ => rfl)]
    exact h
  | swap l l' => simp only [applyAct, isPinned_setLeaf]; exact h
  | dropLeaf l => simp only [applyAct, isPinned_dropAt]; exact h
  | dropTemp i => simp only [applyAct, isPinned_dropAt]; exact h
  | dealloc b => simp only [applyAct, isPinned_deallocAt]; exact h
  | freeTemp => simp only [applyAct, isPinned_deallocAt]; exact h
  | write l u =>
    show (st.setLeaf l _).isPinned c = true
    rw [isPinned_setLeaf]; exact h
  | forget b =>
    rw [show (applyAct st (.forget b)).isPinned c = st.isPinned c from
      isPinned_modifyObj_of_pinned (f := fun o => { o with leaked := true }) (fun _ => rfl) c]
    exact h

/-- A pinned location after an action was pinned before, unless the action is `pinField`
of that location. -/
theorem isPinnedLoc_applyAct_imp (st : State) (a : Act) (l : Loc)
    (h : (applyAct st a).isPinnedLoc l = true) : st.isPinnedLoc l = true ∨ a = .pinField l := by
  cases a with
  | alloc fs => exact Or.inl (isPinnedLoc_push_imp (st := st) h)
  | pinObj c =>
    have : (applyAct st (.pinObj c)).isPinnedLoc l = st.isPinnedLoc l :=
      isPinnedLoc_modifyObj_of_pf (f := fun o => { o with pinned := true }) (fun _ => rfl) l
    exact Or.inl (by rwa [this] at h)
  | pinField m =>
    by_cases hm : l = m
    · exact Or.inr (by rw [hm])
    · left
      simp only [applyAct, isPinnedLoc] at h ⊢
      rw [modifyObj_heap] at h
      by_cases hb : m.1 = l.1
      · simp only [hb, ite_true] at h
        cases ho : st.heap[l.1]? with
        | none => simp [ho] at h
        | some o =>
          simp only [ho, Option.map_some, decide_eq_true_eq, List.mem_cons] at h ⊢
          rcases h with h | h
          · exact absurd (Prod.ext hb.symm h) hm
          · exact h
      · simp only [hb, ite_false] at h; exact h
  | setSelf m =>
    left
    simp only [applyAct] at h
    split at h
    · split at h
      · rwa [isPinnedLoc_setLeaf] at h
      · exact h
    · exact h
  | register m =>
    left
    simp only [applyAct] at h
    split at h
    · split at h
      · exact h
      · exact h
    · exact h
  | moveOut m =>
    have := isPinnedLoc_push_imp (st := st.setLeaf m none) h
    exact Or.inl (by rwa [isPinnedLoc_setLeaf] at this)
  | moveObj c =>
    have := isPinnedLoc_push_imp h
    exact Or.inl (by rwa [isPinnedLoc_modifyObj_of_pf
      (f := fun o => { o with fields := o.fields.map fun _ => none }) (fun _ => rfl)] at this)
  | swap m m' => left; simp only [applyAct, isPinnedLoc_setLeaf] at h; exact h
  | dropLeaf m => left; simp only [applyAct, isPinnedLoc_dropAt] at h; exact h
  | dropTemp i => left; simp only [applyAct, isPinnedLoc_dropAt] at h; exact h
  | dealloc c => left; simp only [applyAct, isPinnedLoc_deallocAt] at h; exact h
  | freeTemp => left; simp only [applyAct, isPinnedLoc_deallocAt] at h; exact h
  | write m u =>
    left
    have : (applyAct st (.write m u)).isPinnedLoc l = (st.setLeaf m _).isPinnedLoc l := rfl
    rw [this, isPinnedLoc_setLeaf] at h; exact h
  | forget c =>
    have : (applyAct st (.forget c)).isPinnedLoc l = st.isPinnedLoc l :=
      isPinnedLoc_modifyObj_of_pf (f := fun o => { o with leaked := true }) (fun _ => rfl) l
    exact Or.inl (by rwa [this] at h)

theorem isPinned_runActs_imp {b : Nat} : ∀ (as : List Act) (st : State),
    (∀ a ∈ as, ∀ c, a ≠ .pinObj c) → (runActs st as).isPinned b = true → st.isPinned b = true
  | [], _, _, h => h
  | a :: as, st, ha, h =>
    isPinned_applyAct_imp st a (ha a (List.mem_cons_self ..)) b
      (isPinned_runActs_imp as _ (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h)

/-! ## The invariant of safe programs -/

/-- Invariant maintained by safe programs over `d`: every pinned location is a structurally
projected field of a pinned object, and every value has the type of its field index. -/
def MacroInv (d : Decl) (st : State) : Prop :=
  (∀ l, st.isPinnedLoc l = true → st.isPinned l.1 = true ∧ ApiOp.projPin l.2 ∈ d.api) ∧
  (∀ l v, st.leafAt l = some v → v.unpin = d.fieldTy l.2)

theorem macroInv_init (d : Decl) : MacroInv d State.init := by
  refine ⟨fun l hl => ?_, fun l v hv => ?_⟩
  · simp [State.isPinnedLoc, State.init] at hl
  · simp [State.leafAt, State.init] at hv

/-- Under the invariant, a pinned non-`Unpin` value sits in a structurally pinned
non-`Unpin` field of a pinned object. -/
theorem MacroInv.pnu {d : Decl} {st : State} (h : MacroInv d st) {b i : Nat}
    (hp : PinnedNonUnpin st (b, i)) : st.isPinned b = true ∧ d.PinnedNonUnpinField i := by
  obtain ⟨hpin, hu⟩ := hp
  obtain ⟨h1, h2⟩ := h.1 _ hpin
  refine ⟨h1, h2, ?_⟩
  cases hv : st.leafAt (b, i) with
  | none => rw [hv] at hu; cases hu
  | some v =>
    rw [hv] at hu
    simp only [Option.map_some, Option.some.injEq] at hu
    exact (h.2 _ v hv).symm.trans hu

/-- Side conditions under which an action keeps values typed by their field index and only
pins structurally projected fields of pinned objects. -/
def ActTyped (d : Decl) (st : State) : Act → Prop
  | .alloc fs => fs = d.fieldUnpin.map some
  | .pinField l => st.isPinned l.1 = true ∧ ApiOp.projPin l.2 ∈ d.api
  | .swap l l' => l.2 = l'.2
  | .write l u => u = d.fieldTy l.2
  | _ => True

/-- An action of a safe program: typed, and respecting both parts of the pinning contract. -/
def Good (d : Decl) (st : State) (a : Act) : Prop :=
  ActTyped d st a ∧ NoPinnedMove st a ∧ DropGuaranteeAct st a

theorem leaf_mkFields_typed {n : Nat} {fu : List Bool} {i : Nat} {v : Leaf}
    (h : (Obj.fresh (mkFields n (fu.map some))).leaf i = some v) :
    v.unpin = (fu[i]?).getD true := by
  unfold Obj.leaf Obj.fresh at h
  simp only [getElem?_mkFields, List.getElem?_map] at h
  cases hu : fu[i]? with
  | none => simp [hu] at h
  | some b => simp [hu] at h; rw [← h]; rfl

theorem leafAt_clear_cases {st : State} {b : Nat} {f : Obj → Obj}
    (hf : ∀ o, (f o).fields = o.fields.map fun _ => none) {m : Loc} {v : Leaf}
    (h : (st.modifyObj b f).leafAt m = some v) : st.leafAt m = some v := by
  by_cases hb : m.1 = b
  · have : m = (b, m.2) := Prod.ext hb rfl
    rw [this, leafAt_clear hf] at h; cases h
  · rw [← leafAt_congr (modifyObj_heap_ne f hb)]; exact h

theorem MacroInv.step {d : Decl} {st : State} (h : MacroInv d st) (a : Act)
    (ht : ActTyped d st a) : MacroInv d (applyAct st a) := by
  refine ⟨fun l hl => ?_, fun l v hv => ?_⟩
  · rcases isPinnedLoc_applyAct_imp st a l hl with h1 | h1
    · obtain ⟨h2, h3⟩ := h.1 l h1
      exact ⟨isPinned_applyAct_mono st a _ h2, h3⟩
    · subst h1
      exact ⟨isPinned_applyAct_mono st _ _ ht.1, ht.2⟩
  · cases a with
    | alloc fs =>
      simp only [ActTyped] at ht; subst ht
      have hv' : (st.push (Obj.fresh (mkFields st.nextId (d.fieldUnpin.map some)))).leafAt l
          = some v := hv
      rcases leafAt_push_cases hv' with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact h.2 l v h2
      · exact leaf_mkFields_typed h2
    | pinObj b =>
      have : (applyAct st (.pinObj b)).leafAt l = st.leafAt l :=
        leafAt_modifyObj_of_fields (f := fun o => { o with pinned := true }) (fun _ => rfl) l
      rw [this] at hv; exact h.2 l v hv
    | pinField m =>
      have : (applyAct st (.pinField m)).leafAt l = st.leafAt l :=
        leafAt_modifyObj_of_fields
          (f := fun o => { o with pinnedFields := m.2 :: o.pinnedFields }) (fun _ => rfl) l
      rw [this] at hv; exact h.2 l v hv
    | setSelf m =>
      simp only [applyAct] at hv
      split at hv
      · rename_i w hw
        split at hv
        · rcases leafAt_setLeaf_cases hv with ⟨rfl, h2⟩ | ⟨-, h2⟩
          · cases h2; exact h.2 l w hw
          · exact h.2 l v h2
        · exact h.2 l v hv
      · exact h.2 l v hv
    | register m =>
      simp only [applyAct] at hv
      split at hv
      · split at hv
        · exact h.2 l v hv
        · exact h.2 l v hv
      · exact h.2 l v hv
    | moveOut m =>
      simp only [applyAct] at hv
      rcases leafAt_push_cases hv with ⟨-, h2⟩ | ⟨-, h2⟩
      · rcases leafAt_setLeaf_cases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
        · cases h3
        · exact h.2 l v h3
      · rw [leaf_tempFields] at h2
        split at h2
        · rename_i hidx
          rw [hidx]; exact h.2 m v h2
        · cases h2
    | moveObj b =>
      simp only [applyAct] at hv
      rcases leafAt_push_cases hv with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact h.2 l v (leafAt_clear_cases (fun _ => rfl) h2)
      · have hb : st.leafAt (b, l.2) = some v := by
          unfold State.leafAt
          cases ho : st.heap[b]? with
          | none => simp [ho, Obj.leaf, Obj.fresh] at h2
          | some o => simpa [ho, Obj.leaf, Obj.fresh] using h2
        exact h.2 (b, l.2) v hb
    | swap m m' =>
      simp only [ActTyped] at ht
      simp only [applyAct] at hv
      rcases leafAt_setLeaf_cases hv with ⟨rfl, h2⟩ | ⟨-, h2⟩
      · rw [← ht]; exact h.2 m v h2
      · rcases leafAt_setLeaf_cases h2 with ⟨rfl, h3⟩ | ⟨-, h3⟩
        · rw [ht]; exact h.2 m' v h3
        · exact h.2 l v h3
    | dropLeaf m => exact h.2 l v (leafAt_dropAt_cases hv)
    | dropTemp i => exact h.2 l v (leafAt_dropAt_cases hv)
    | dealloc b => exact h.2 l v (leafAt_deallocAt_cases hv)
    | freeTemp => exact h.2 l v (leafAt_deallocAt_cases hv)
    | write m u =>
      simp only [ActTyped] at ht
      have hv' : (st.setLeaf m (some ⟨st.nextId, u, none⟩)).leafAt l = some v := hv
      rcases leafAt_setLeaf_cases hv' with ⟨rfl, h2⟩ | ⟨-, h2⟩
      · cases h2; exact ht
      · exact h.2 l v h2
    | forget b =>
      have : (applyAct st (.forget b)).leafAt l = st.leafAt l :=
        leafAt_modifyObj_of_fields (f := fun o => { o with leaked := true }) (fun _ => rfl) l
      rw [this] at hv; exact h.2 l v hv

theorem MacroInv.runActs {d : Decl} {st : State} {as : List Act} (h : MacroInv d st)
    (hg : Always (Good d) st as) : MacroInv d (Toy.Pin.runActs st as) := by
  induction as generalizing st with
  | nil => exact h
  | cons a as ih => exact ih (h.step a hg.1.1) hg.2

/-! ## Each operation of a safe program respects the pinning contract -/

/-- The six conditions, bundled (internal). -/
structure Conds (d : Decl) : Prop where
  ca : UnpinOnlyIfPinnedFieldsUnpin d
  cb : DtorNoMoveOutOfPinned d
  cc : DropGuaranteeForPinned d
  cd : NoPinnedTake d
  ce : NotPackedIfPinned d
  cf : ProjectionConsistent d

theorem moveDrop_good {d : Decl} {st : State} {l : Loc} (hp : ¬ PinnedNonUnpin st l) :
    Always (Good d) st (moveDrop l) := by
  refine ⟨⟨trivial, hp, trivial⟩, ⟨trivial, trivial, trivial⟩,
    ⟨trivial, trivial, fun i _ hpnu => ?_⟩, trivial⟩
  have hlen : (applyAct (applyAct st (.moveOut l)) (.dropTemp l.2)).heap.length - 1
      = st.heap.length := by
    simp [applyAct, dropAt_heap_length]
  have hfalse : (applyAct (applyAct st (.moveOut l)) (.dropTemp l.2)).isPinnedLoc
      (st.heap.length, i) = false := by
    simp only [applyAct, isPinnedLoc_dropAt]
    exact isPinnedLoc_push_fresh _ _ _ (by simp)
  have h1 := hpnu.1
  rw [hlen, hfalse] at h1
  cases h1

theorem moveDrop_noPin (l : Loc) : ∀ a ∈ moveDrop l, ∀ c, a ≠ .pinObj c := by
  intro a ha c
  simp only [moveDrop, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> simp

theorem not_pnu_of_mutField {d : Decl} (hc : Conds d) {st s : State} {b i : Nat}
    (hI : MacroInv d s) (hst : s.isPinned b = true → st.isPinned b = true)
    (hm : MutFieldAvail d st b i) : ¬ PinnedNonUnpin s (b, i) := by
  intro hp
  obtain ⟨hpin, hsnu⟩ := hI.pnu hp
  rcases hm.2 with h1 | h1 | h1 | ⟨-, h1⟩
  · rw [hst hpin] at h1; cases h1
  · have := hc.ca h1 i hsnu.1; rw [hsnu.2] at this; cases this
  · exact hc.cf i hsnu h1
  · rw [hsnu.2] at h1; cases h1

theorem not_pnu_of_mutStruct {d : Decl} (hc : Conds d) {st s : State} {b : Nat}
    (hI : MacroInv d s) (hst : s.isPinned b = true → st.isPinned b = true)
    (hm : MutStructAvail d st b) (i : Nat) : ¬ PinnedNonUnpin s (b, i) := by
  intro hp
  obtain ⟨hpin, hsnu⟩ := hI.pnu hp
  rcases hm.2 with h1 | h1
  · rw [hst hpin] at h1; cases h1
  · have := hc.ca h1 i hsnu.1; rw [hsnu.2] at this; cases this

theorem runActs_dropLeafs_none (b : Nat) {m : Loc} : ∀ (is : List Nat) (s : State),
    s.leafAt m = none →
      (runActs s (is.flatMap fun i => [Act.dropLeaf (b, i)])).leafAt m = none
  | [], _, h => h
  | k :: ks, s, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, runActs]
    exact runActs_dropLeafs_none b ks _ (leafAt_dropAt_of_none _ h)

theorem glue_empty (b : Nat) : ∀ (is : List Nat) (s : State), ∀ j ∈ is,
    (runActs s (is.flatMap fun i => [Act.dropLeaf (b, i)])).leafAt (b, j) = none
  | [], _, _, hj => by cases hj
  | k :: ks, s, j, hj => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, runActs]
    simp only [List.mem_cons] at hj
    by_cases hjk : j = k
    · subst hjk
      exact runActs_dropLeafs_none b ks _ (leafAt_dropAt_self _ _)
    · exact glue_empty b ks _ j (hj.resolve_left hjk)

theorem drop_good {d : Decl} (hc : Conds d) {st : State} (hI : MacroInv d st) (b : Nat) :
    Always (Good d) st (dropActs d b) := by
  unfold dropActs
  -- destructor actions
  obtain ⟨h1, hI1⟩ := always_flatMap (I := MacroInv d) (P := Good d) (dtorActs d b) d.dtor
    (fun x hx s hs => by
      cases x with
      | moveOut i =>
        have hg : Always (Good d) s (dtorActs d b (.moveOut i)) := moveDrop_good (fun hp =>
          hc.cb i (hs.pnu hp).2 hx)
        exact ⟨hg, hs.runActs hg⟩
      | overwrite i =>
        have hg : Always (Good d) s (dtorActs d b (.overwrite i)) :=
          ⟨⟨rfl, trivial, fun hp => (hc.cc i (hs.pnu hp).2).2 hx⟩, trivial⟩
        exact ⟨hg, hs.runActs hg⟩) st hI
  -- drop-glue actions
  obtain ⟨h2, hI2⟩ := always_flatMap (I := MacroInv d) (P := Good d) (glueActs d b)
    (List.range d.nfields)
    (fun i _ s hs => by
      unfold glueActs
      split
      · rename_i hpk
        have hg : Always (Good d) s (moveDrop (b, i)) :=
          moveDrop_good (fun hp => hc.ce hpk i (hs.pnu hp).2)
        exact ⟨hg, hs.runActs hg⟩
      · have hg : Always (Good d) s [Act.dropLeaf (b, i)] := ⟨⟨trivial, trivial, trivial⟩, trivial⟩
        exact ⟨hg, hs.runActs hg⟩) _ hI1
  rw [always_append, always_append, runActs_append]
  refine ⟨⟨h1, h2⟩, ⟨trivial, trivial, fun j _ hp => ?_⟩, trivial⟩
  obtain ⟨-, hsnu⟩ := hI2.pnu hp
  by_cases hpk : d.packed = true
  · exact hc.ce hpk j hsnu
  · have hglue : (List.range d.nfields).flatMap (glueActs d b) =
        (List.range d.nfields).flatMap fun i => [Act.dropLeaf (b, i)] := by
      congr 1; funext i; simp [glueActs, hpk]
    have hj : j ∈ List.range d.nfields :=
      List.mem_range.mpr (Decl.lt_of_pinnedNonUnpinField hsnu)
    have hnone := glue_empty b (List.range d.nfields) (runActs st (d.dtor.flatMap (dtorActs d b))) j hj
    rw [← hglue] at hnone
    have h2' := hp.2
    rw [hnone] at h2'
    cases h2'

theorem op_good {d : Decl} (hc : Conds d) {st : State} (hI : MacroInv d st) (op : Op)
    (hs : SafeOp d st op) : Always (Good d) st (expand d op) := by
  cases op with
  | new => exact ⟨⟨rfl, trivial, trivial⟩, trivial⟩
  | pin b => exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
  | projPin b i => exact ⟨⟨⟨hs.2.1, hs.2.2⟩, trivial, trivial⟩, trivial⟩
  | initSelf l => exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
  | link l => exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩
  | replaceField b i =>
    have h1 : Always (Good d) st (moveDrop (b, i)) := moveDrop_good
      (not_pnu_of_mutField hc hI id hs)
    have hI1 := hI.runActs h1
    have hst := isPinned_runActs_imp (b := b) _ st (moveDrop_noPin (b, i))
    show Always (Good d) st (moveDrop (b, i) ++ [Act.write (b, i) (d.fieldTy i)])
    rw [always_append]
    exact ⟨h1, ⟨rfl, trivial, not_pnu_of_mutField hc hI1 hst hs⟩, trivial⟩
  | swapField b c i =>
    exact ⟨⟨rfl, ⟨not_pnu_of_mutField hc hI id hs.2.1, not_pnu_of_mutField hc hI id hs.2.2⟩,
      trivial⟩, trivial⟩
  | assignField b i =>
    refine ⟨⟨trivial, trivial, trivial⟩, ⟨rfl, trivial, ?_⟩, trivial⟩
    exact not_pnu_of_mutField hc (hI.step _ trivial)
      (isPinned_applyAct_imp st _ (fun c => by simp) b) hs
  | replaceStruct b =>
    refine ⟨⟨trivial, fun i _ => not_pnu_of_mutStruct hc hI id hs i, trivial⟩, ?_⟩
    have hI1 := hI.step (.moveObj b) trivial
    have hst1 := isPinned_applyAct_imp st (.moveObj b) (fun c => by simp) b
    refine (always_of_forall (I := fun s => MacroInv d s ∧
        (s.isPinned b = true → st.isPinned b = true)) _ ?_ _ ⟨hI1, hst1⟩).1
    intro a ha s ⟨hIs, hsts⟩
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    refine ⟨⟨rfl, trivial, not_pnu_of_mutStruct hc hIs hsts hs i⟩, hIs.step _ rfl, ?_⟩
    exact fun hp => hsts (isPinned_applyAct_imp s _ (fun c => by simp) b hp)
  | take b i =>
    exact moveDrop_good (fun hp => hc.cd i (hI.pnu hp).2 hs.2)
  | overwrite b i =>
    exact ⟨⟨rfl, trivial, fun hp => (hc.cc i (hI.pnu hp).2).1 hs.2⟩, trivial⟩
  | drop b => exact drop_good hc hI b
  | forget b => exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩

theorem good_compile {d : Decl} (hc : Conds d) : ∀ (prog : List Op) (st : State),
    MacroInv d st → SafeProgram d st prog → Always (Good d) st (compile d prog)
  | [], _, _, _ => trivial
  | op :: ops, st, hI, hsafe => by
    have h1 := op_good hc hI op hsafe.1
    have hI' := hI.runActs h1
    simp only [compile, List.flatMap_cons]
    rw [always_append]
    exact ⟨h1, good_compile hc ops _ hI' hsafe.2⟩

/-- **Structural pinning is sound under (a)–(f).** If `S : Unpin`
only when its structurally pinned fields are `Unpin` (a), its destructor does not move out of
a structurally pinned non-`Unpin` field (b), neither its API nor its destructor overwrites
such a field without dropping it (c), it offers no move-out operation for such a field (d),
it is not `#[repr(packed)]` when it has such a field (e), and such a field is not also
offered through a non-structural projection (f), then every safe program keeps the
self-reference and intrusive-list invariants at every state. -/
theorem addrInv_of_structural_pinning_conditions (d : Decl)
    (ha : UnpinOnlyIfPinnedFieldsUnpin d) (hb : DtorNoMoveOutOfPinned d)
    (hc : DropGuaranteeForPinned d) (hd : NoPinnedTake d) (he : NotPackedIfPinned d)
    (hf : ProjectionConsistent d) (prog : List Op) (hsafe : SafeProgram d State.init prog) :
    ∀ s ∈ states State.init (compile d prog), AddrInv s := by
  have hg := good_compile ⟨ha, hb, hc, hd, he, hf⟩ prog State.init (macroInv_init d) hsafe
  exact addrInv_of_noPinnedMove_of_dropGuarantee _
    (always_mono (fun _ _ h => h.2.1) _ _ hg) (always_mono (fun _ _ h => h.2.2) _ _ hg)

end Toy.Pin
