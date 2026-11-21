import ToyPin.Soundness

/-!
# Where address-sensitive state can arise

In this model a location is a *field* location `(b, i)`; no location denotes a whole
object, so a struct as a whole never carries a self-pointer or a list entry. Self-pointers
and list entries are created only by `Act.setSelf l` and `Act.register l` at a location `l`
with `isPinnedLoc l = true`, and safe programs make `isPinnedLoc (b, i)` true only through
`Op.projPin b i`, which requires `ApiOp.projPin i ∈ d.api`.

* `addrState_only_at_structurally_projected_fields`: in every state visited by a program
  accepted by `SafeProgram d` from `State.init`, every self-pointer target and every list
  entry is a field location whose index has an offered structural projection.
* `no_addrState_without_structural_projection`: if `d` offers no structural projection, no
  state visited by such a program has any self-pointer or list entry.
-/

namespace Toy.Pin

open State

/-! ## Generic facts about runs -/

theorem always_of_forall_mem {P : State → Act → Prop} :
    ∀ (as : List Act), (∀ a ∈ as, ∀ s, P s a) → ∀ st, Always P st as
  | [], _, _ => trivial
  | a :: as, h, st =>
    ⟨h a (List.mem_cons_self ..) st,
      always_of_forall_mem as (fun b hb => h b (List.mem_cons_of_mem _ hb)) _⟩

/-- An invariant preserved by every step allowed by `P` holds at every visited state and at
the final state. -/
theorem always_inv {P : State → Act → Prop} {I : State → Prop}
    (hstep : ∀ s a, P s a → I s → I (applyAct s a)) :
    ∀ (acts : List Act) (st : State), Always P st acts → I st →
      (∀ s ∈ states st acts, I s) ∧ I (runActs st acts)
  | [], st, _, hI => ⟨fun s hs => by simp [states] at hs; subst hs; exact hI, hI⟩
  | a :: as, st, h, hI => by
    obtain ⟨h1, h2⟩ := always_inv hstep as _ h.2 (hstep st a h.1 hI)
    refine ⟨fun s hs => ?_, h2⟩
    simp only [states, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hI
    · exact h1 s hs

theorem mem_states_append : ∀ (st : State) (as bs : List Act) (s : State),
    s ∈ states st (as ++ bs) → s ∈ states st as ∨ s ∈ states (runActs st as) bs
  | _, [], _, _, h => Or.inr h
  | st, a :: as, bs, s, h => by
    simp only [List.cons_append, states, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl (Or.inl rfl)
    · rcases mem_states_append (applyAct st a) as bs s h with h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1

/-! ## Provenance of leaves and list entries -/

theorem registry_dropAt_sub (st : State) (l : Loc) {e : Loc × Nat}
    (h : e ∈ (st.dropAt l).registry) : e ∈ st.registry := by
  unfold State.dropAt at h
  split at h
  · simp only [List.mem_filter] at h; exact h.1
  · exact h

/-- Every leaf of the new state is an old leaf (at some location), or has no self-pointer,
or is the leaf whose self-pointer `setSelf m` just set to a pinned location `m`. -/
theorem leafAt_applyAct_cases (st : State) (a : Act) {l : Loc} {v : Leaf}
    (h : (applyAct st a).leafAt l = some v) :
    (∃ m, st.leafAt m = some v) ∨ v.selfPtr = none ∨
      (∃ m, a = .setSelf m ∧ v.selfPtr = some m ∧ st.isPinnedLoc m = true) := by
  cases a with
  | alloc fs =>
    have h' : (st.push (Obj.fresh (mkFields st.nextId fs))).leafAt l = some v := h
    rcases leafAt_push_cases h' with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inl ⟨l, h2⟩
    · exact Or.inr (Or.inl (leaf_mkFields_selfPtr h2))
  | pinObj b =>
    have : (applyAct st (.pinObj b)).leafAt l = st.leafAt l :=
      leafAt_modifyObj_of_fields (f := fun o => { o with pinned := true }) (fun _ => rfl) l
    rw [this] at h; exact Or.inl ⟨l, h⟩
  | pinField m =>
    have : (applyAct st (.pinField m)).leafAt l = st.leafAt l :=
      leafAt_modifyObj_of_fields
        (f := fun o => { o with pinnedFields := m.2 :: o.pinnedFields }) (fun _ => rfl) l
    rw [this] at h; exact Or.inl ⟨l, h⟩
  | setSelf m =>
    simp only [applyAct] at h
    split at h
    · split at h
      · rename_i hc
        rcases leafAt_setLeaf_cases h with ⟨-, h2⟩ | ⟨-, h2⟩
        · cases h2
          exact Or.inr (Or.inr ⟨m, rfl, rfl, hc.1⟩)
        · exact Or.inl ⟨l, h2⟩
      · exact Or.inl ⟨l, h⟩
    · exact Or.inl ⟨l, h⟩
  | register m =>
    simp only [applyAct] at h
    split at h
    · split at h
      · exact Or.inl ⟨l, h⟩
      · exact Or.inl ⟨l, h⟩
    · exact Or.inl ⟨l, h⟩
  | moveOut m =>
    simp only [applyAct] at h
    rcases leafAt_push_cases h with ⟨-, h2⟩ | ⟨-, h2⟩
    · rcases leafAt_setLeaf_cases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
      · cases h3
      · exact Or.inl ⟨l, h3⟩
    · rw [leaf_tempFields] at h2
      split at h2
      · exact Or.inl ⟨m, h2⟩
      · cases h2
  | moveObj b =>
    simp only [applyAct] at h
    rcases leafAt_push_cases h with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inl ⟨l, leafAt_clear_cases (fun _ => rfl) h2⟩
    · have hb : st.leafAt (b, l.2) = some v := by
        unfold State.leafAt
        cases ho : st.heap[b]? with
        | none => simp [ho, Obj.leaf, Obj.fresh] at h2
        | some o => simpa [ho, Obj.leaf, Obj.fresh] using h2
      exact Or.inl ⟨_, hb⟩
  | swap m m' =>
    simp only [applyAct] at h
    rcases leafAt_setLeaf_cases h with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inl ⟨m, h2⟩
    · rcases leafAt_setLeaf_cases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
      · exact Or.inl ⟨m', h3⟩
      · exact Or.inl ⟨l, h3⟩
  | dropLeaf m => exact Or.inl ⟨l, leafAt_dropAt_cases h⟩
  | dropTemp i => exact Or.inl ⟨l, leafAt_dropAt_cases h⟩
  | dealloc b => exact Or.inl ⟨l, leafAt_deallocAt_cases h⟩
  | freeTemp => exact Or.inl ⟨l, leafAt_deallocAt_cases h⟩
  | write m u =>
    have h' : (st.setLeaf m (some ⟨st.nextId, u, none⟩)).leafAt l = some v := h
    rcases leafAt_setLeaf_cases h' with ⟨-, h2⟩ | ⟨-, h2⟩
    · cases h2; exact Or.inr (Or.inl rfl)
    · exact Or.inl ⟨l, h2⟩
  | forget b =>
    have : (applyAct st (.forget b)).leafAt l = st.leafAt l :=
      leafAt_modifyObj_of_fields (f := fun o => { o with leaked := true }) (fun _ => rfl) l
    rw [this] at h; exact Or.inl ⟨l, h⟩

/-- Every list entry of the new state is an old entry, or the entry that `register m` just
added for a pinned location `m`. -/
theorem registry_applyAct_cases (st : State) (a : Act) {e : Loc × Nat}
    (h : e ∈ (applyAct st a).registry) :
    e ∈ st.registry ∨ (∃ m, a = .register m ∧ e.1 = m ∧ st.isPinnedLoc m = true) := by
  cases a with
  | register m =>
    simp only [applyAct] at h
    split at h
    · split at h
      · rename_i hc
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inr ⟨m, rfl, rfl, hc.1⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inl h
  | setSelf m =>
    left
    simp only [applyAct] at h
    split at h
    · split at h
      · simpa using h
      · exact h
    · exact h
  | dropLeaf m => exact Or.inl (registry_dropAt_sub st m h)
  | dropTemp i => exact Or.inl (registry_dropAt_sub st _ h)
  | alloc fs => exact Or.inl h
  | pinObj b => exact Or.inl h
  | pinField m => exact Or.inl h
  | moveOut m => exact Or.inl h
  | moveObj b => exact Or.inl h
  | swap m m' => exact Or.inl h
  | dealloc b => exact Or.inl h
  | freeTemp => exact Or.inl h
  | write m u => exact Or.inl h
  | forget b => exact Or.inl h

/-- Without `register` actions the list never gains an entry. -/
theorem registry_sub_of_no_register (acts : List Act) (st : State)
    (hno : ∀ a ∈ acts, ∀ m, a ≠ .register m) :
    ∀ s ∈ states st acts, ∀ e ∈ s.registry, e ∈ st.registry :=
  (always_inv (P := fun _ a => ∀ m, a ≠ .register m)
    (I := fun s => ∀ e ∈ s.registry, e ∈ st.registry)
    (fun s a ha hI e he => by
      rcases registry_applyAct_cases s a he with h1 | ⟨m, h1, -, -⟩
      · exact hI e h1
      · exact absurd h1 (ha m))
    acts st (always_of_forall_mem acts (fun a h _ => hno a h) st) (fun _ h => h)).1

/-! ## Safe programs only produce typed actions -/

theorem op_typed (d : Decl) (st : State) (op : Op) (hs : SafeOp d st op) :
    Always (ActTyped d) st (expand d op) := by
  cases op with
  | new => exact ⟨rfl, trivial⟩
  | pin b => exact ⟨trivial, trivial⟩
  | projPin b i => exact ⟨⟨hs.2.1, hs.2.2⟩, trivial⟩
  | initSelf l => exact ⟨trivial, trivial⟩
  | link l => exact ⟨trivial, trivial⟩
  | replaceField b i => exact ⟨trivial, trivial, trivial, rfl, trivial⟩
  | swapField b c i => exact ⟨rfl, trivial⟩
  | assignField b i => exact ⟨trivial, rfl, trivial⟩
  | replaceStruct b =>
    refine ⟨trivial, always_of_forall_mem _ ?_ _⟩
    intro a ha s
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    rfl
  | take b i => exact ⟨trivial, trivial, trivial, trivial⟩
  | overwrite b i => exact ⟨rfl, trivial⟩
  | drop b =>
    apply always_of_forall_mem
    intro a ha s
    simp only [expand, dropActs, List.mem_append, List.mem_flatMap, List.mem_singleton] at ha
    rcases ha with (⟨x, -, hx⟩ | ⟨i, -, hi⟩) | rfl
    · cases x with
      | moveOut j =>
        simp only [dtorActs, moveDrop, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> trivial
      | overwrite j =>
        simp only [dtorActs, List.mem_singleton] at hx
        subst hx; rfl
    · unfold glueActs at hi
      split at hi
      · simp only [moveDrop, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> trivial
      · simp only [List.mem_singleton] at hi
        subst hi; trivial
    · trivial
  | forget b => exact ⟨trivial, trivial⟩

theorem typed_compile (d : Decl) : ∀ (prog : List Op) (st : State),
    SafeProgram d st prog → Always (ActTyped d) st (compile d prog)
  | [], _, _ => trivial
  | op :: ops, st, hsafe => by
    simp only [compile, List.flatMap_cons]
    rw [always_append]
    exact ⟨op_typed d st op hsafe.1, typed_compile d ops _ hsafe.2⟩

/-! ## Address-sensitive state only at structurally projected fields -/

/-- Every self-pointer target and every list entry is a field location whose index has an
offered structural projection (`ApiOp.projPin`). -/
def AddrStateAtProjected (d : Decl) (st : State) : Prop :=
  (∀ l v, st.leafAt l = some v → ∀ m, v.selfPtr = some m → ApiOp.projPin m.2 ∈ d.api) ∧
  (∀ e ∈ st.registry, ApiOp.projPin e.1.2 ∈ d.api)

theorem AddrStateAtProjected.step {d : Decl} {st : State} (hI : MacroInv d st)
    (h : AddrStateAtProjected d st) (a : Act) : AddrStateAtProjected d (applyAct st a) := by
  refine ⟨fun l v hv m hm => ?_, fun e he => ?_⟩
  · rcases leafAt_applyAct_cases st a hv with ⟨l0, h0⟩ | h0 | ⟨m', -, h1, h2⟩
    · exact h.1 l0 v h0 m hm
    · rw [h0] at hm; cases hm
    · rw [h1] at hm; cases hm; exact (hI.1 _ h2).2
  · rcases registry_applyAct_cases st a he with h0 | ⟨m, -, h1, h2⟩
    · exact h.2 e h0
    · rw [h1]; exact (hI.1 _ h2).2

/-- **Address-sensitive state arises only at structurally projected fields.** For every
declaration `d` and every program accepted by `SafeProgram d` from `State.init` (compiled by
`compile d`), in every visited state every self-pointer target `(b', i')` and every list
entry location `(b', i')` has `ApiOp.projPin i' ∈ d.api`. No location denotes a whole
struct, so the struct itself never holds a self-pointer or list entry. -/
theorem addrState_only_at_structurally_projected_fields (d : Decl) (prog : List Op)
    (hsafe : SafeProgram d State.init prog) :
    ∀ s ∈ states State.init (compile d prog), AddrStateAtProjected d s := by
  intro s hs
  exact ((always_inv (P := ActTyped d) (I := fun s => MacroInv d s ∧ AddrStateAtProjected d s)
    (fun s a ht hI => ⟨hI.1.step a ht, hI.2.step hI.1 a⟩) _ _ (typed_compile d prog _ hsafe)
    ⟨macroInv_init d,
      fun l v hv => by simp [State.leafAt, State.init] at hv,
      fun e he => by simp [State.init] at he⟩).1 s hs).2

/-- **Without a structural projection there is no address-sensitive state.** If `d` offers
no `ApiOp.projPin`, then in every state visited by a program accepted by `SafeProgram d`
from `State.init`, the list is empty and no leaf has a self-pointer. -/
theorem no_addrState_without_structural_projection (d : Decl)
    (hno : ∀ i, ApiOp.projPin i ∉ d.api) (prog : List Op)
    (hsafe : SafeProgram d State.init prog) :
    ∀ s ∈ states State.init (compile d prog),
      s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none := by
  intro s hs
  obtain ⟨h1, h2⟩ := addrState_only_at_structurally_projected_fields d prog hsafe s hs
  refine ⟨?_, fun l v hv => ?_⟩
  · cases hr : s.registry with
    | nil => rfl
    | cons e es => exact absurd (h2 e (by rw [hr]; exact List.mem_cons_self ..)) (hno _)
  · cases hp : v.selfPtr with
    | none => rfl
    | some m => exact absurd (h1 l v hv m hp) (hno _)

end Toy.Pin
