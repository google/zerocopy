import Toy.PlaceEval.MarkerSim

/-!
# Storage-marker erasure: the state relation and allocation steps

`SRel1` relates a source state (a run of `P`) to a target state (a run of
`eraseMarkers P x`) under an allocation renaming `f`. This file shows that it is preserved
by the allocation steps: deallocation and allocation of a local other than `x` in both
programs, and the source-only deallocation and allocation of `x`.
-/

namespace Toy.PlaceEval

/-! ## Frames, deallocation and allocation -/

theorem getD_set_none (l : List (Option Nat)) (y z : Nat) (v : Option Nat) :
    (l.set y v).getD z none = if y = z ∧ y < l.length then v else l.getD z none := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : y = z
  · subst h1
    by_cases h2 : y < l.length
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem allocOf_eq_none_of_le {st : State} {y : Local} (h : st.frame.length ≤ y) :
    st.allocOf y = none := by
  simp [State.allocOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem deallocate_allocOf (st : State) (y z : Local) :
    (deallocate st y).allocOf z = if z = y then none else st.allocOf z := by
  unfold deallocate
  cases h : st.allocOf y with
  | none =>
    by_cases hz : z = y
    · subst hz; simp [h]
    · simp [hz]
  | some k =>
    simp only [State.allocOf]
    rw [getD_set_none]
    by_cases hz : z = y
    · subst hz
      simp only [true_and, ↓reduceIte]
      split
      · rfl
      · rename_i hl
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
    · simp [hz, Ne.symm hz]

theorem deallocate_cells (st : State) (y : Local) : (deallocate st y).mem.cells = st.mem.cells := by
  unfold deallocate; split <;> rfl

theorem deallocate_frame_length (st : State) (y : Local) :
    (deallocate st y).frame.length = st.frame.length := by
  unfold deallocate; split <;> simp

theorem deallocate_getElem? (st : State) (y : Local) (j : Nat) :
    (deallocate st y).mem.allocs[j]? = (st.mem.allocs[j]?).map
      (fun al => if st.allocOf y = some j then { al with live := false } else al) := by
  unfold deallocate
  cases h : st.allocOf y with
  | none => simp
  | some k =>
    simp only [List.getElem?_modify, Option.some.injEq]
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]

theorem deallocate_get (st : State) (y : Local) (a : Nat) :
    (deallocate st y).mem.get a = st.mem.get a := by
  simp only [Mem.get, deallocate_cells]

/-- The state after allocating `L` for `x` at address `a`. -/
def allocState (st : State) (x : Local) (L : Layout) (a : Nat) : State :=
  { mem := { allocs := st.mem.allocs ++ [⟨a, L.size, true⟩],
             cells := placeCells a (List.replicate L.size .uninit) ++ st.mem.cells },
    frame := st.frame.set x (some st.mem.allocs.length) }

theorem allocate_fresh (ω : Nat → Nat) (st : State) (x : Local) (L : Layout) :
    allocate (.fresh ω) st x L =
      if (st.mem.allocs.all fun al =>
          !al.live || disjointRanges (L.align * (ω st.mem.allocs.length + 1)) L.size al.base al.size)
      then some (allocState st x L (L.align * (ω st.mem.allocs.length + 1))) else none := rfl

theorem allocate_slots (s : Local → Nat) (st : State) (x : Local) (L : Layout) :
    allocate (.slots s) st x L = some (allocState st x L (s x)) := rfl

theorem allocState_length (st : State) (x : Local) (L : Layout) (a : Nat) :
    (allocState st x L a).mem.allocs.length = st.mem.allocs.length + 1 := by
  simp [allocState]

theorem allocState_frame_length (st : State) (x : Local) (L : Layout) (a : Nat) :
    (allocState st x L a).frame.length = st.frame.length := by
  simp [allocState]

theorem allocState_getElem? (st : State) (x : Local) (L : Layout) (a j : Nat) :
    (allocState st x L a).mem.allocs[j]? =
      if j < st.mem.allocs.length then st.mem.allocs[j]?
      else if j = st.mem.allocs.length then some ⟨a, L.size, true⟩ else none := by
  simp only [allocState]
  by_cases h1 : j < st.mem.allocs.length
  · simp [h1, List.getElem?_append_left h1]
  · rw [List.getElem?_append_right (Nat.le_of_not_lt h1)]
    by_cases h2 : j = st.mem.allocs.length
    · subst h2; simp
    · have : j - st.mem.allocs.length ≠ 0 := by omega
      simp [h1, h2, this]

theorem allocState_getElem?_old {st : State} {x : Local} {L : Layout} {a j : Nat}
    (h : j < st.mem.allocs.length) : (allocState st x L a).mem.allocs[j]? = st.mem.allocs[j]? := by
  rw [allocState_getElem?, ite_pos' h]

theorem allocState_getElem?_new (st : State) (x : Local) (L : Layout) (a : Nat) :
    (allocState st x L a).mem.allocs[st.mem.allocs.length]? = some ⟨a, L.size, true⟩ := by
  rw [allocState_getElem?]; simp

theorem allocState_allocOf (st : State) (x : Local) (L : Layout) (a z : Nat) :
    (allocState st x L a).allocOf z =
      if x = z ∧ x < st.frame.length then some st.mem.allocs.length else st.allocOf z := by
  simp only [allocState, State.allocOf]
  rw [getD_set_none]

theorem allocState_get (st : State) (x : Local) (L : Layout) (a b : Nat) :
    (allocState st x L a).mem.get b = if a ≤ b ∧ b < a + L.size then .uninit else st.mem.get b := by
  have e : (allocState st x L a).mem.get b = (st.mem.writeCells a (List.replicate L.size .uninit)).get b :=
    rfl
  rw [e, get_writeCells, List.length_replicate]
  split
  · rename_i h
    simp [show b - a < L.size by omega]
  · rfl

theorem allocState_inBounds {st : State} {x : Local} {L : Layout} {a : Nat} {p : Ptr} {n : Nat}
    (h : (allocState st x L a).mem.inBounds p n = true) :
    (p.prov = some st.mem.allocs.length ∧ a ≤ p.addr ∧ p.addr + n ≤ a + L.size) ∨
      st.mem.inBounds p n = true := by
  unfold Mem.inBounds at h ⊢
  cases hp : p.prov with
  | none => rw [hp] at h; cases h
  | some k =>
    rw [hp] at h
    simp only at h ⊢
    rw [allocState_getElem?] at h
    by_cases h1 : k < st.mem.allocs.length
    · rw [ite_pos' h1] at h; exact Or.inr h
    · rw [ite_neg' h1] at h
      by_cases h2 : k = st.mem.allocs.length
      · subst h2
        simp only [↓reduceIte, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at h
        exact Or.inl ⟨rfl, h⟩
      · rw [ite_neg' h2] at h; cases h

theorem disjointRanges_comm (a n b m : Nat) : disjointRanges a n b m = disjointRanges b m a n := by
  unfold disjointRanges
  cases (n == 0) <;> cases (m == 0) <;> cases decide (a + n ≤ b) <;> cases decide (b + m ≤ a) <;> rfl

theorem disjointRanges_shift (a n b m D : Nat) :
    disjointRanges (a + D) n (b + D) m = disjointRanges a n b m := by
  unfold disjointRanges
  rw [show decide (a + D + n ≤ b + D) = decide (a + n ≤ b) from decide_eq_decide.mpr (by omega),
    show decide (b + D + m ≤ a + D) = decide (b + m ≤ a) from decide_eq_decide.mpr (by omega)]

/-! ## Monotonicity in the renaming -/

/-- `f'` extends `f`. -/
def FExt (f f' : Nat → Option Nat) : Prop := ∀ k k', f k = some k' → f' k = some k'

theorem V1.mono {D : Nat} {J : Ptr → Prop} {f f' : Nat → Option Nat} (hf : FExt f f')
    {p q : Ptr} (h : V1 D J f p q) : V1 D J f' p q := by
  rcases h with ⟨k, k', hk, h1, h2, h3⟩ | h
  · exact Or.inl ⟨k, k', hf k k' hk, h1, h2, h3⟩
  · exact Or.inr h

theorem CR1.mono {D : Nat} {J : Ptr → Prop} {f f' : Nat → Option Nat} (hf : FExt f f')
    {c d : Cell} (h : CR1 D J f c d) : CR1 D J f' c d := by
  cases c <;> cases d <;> simp only [CR1] at h ⊢
  all_goals first | trivial | exact h | exact ⟨h.1, h.2.mono hf⟩

/-! ## The state relation -/

/-- The address of the target allocation of `x`, shifted by `D`, is one the source can choose
for `x`. -/
def XAddr (mt : AllocMode) (D : Nat) (L : Layout) (x : Local) (b : Nat) : Prop :=
  match mt with
  | .fresh _ => ∃ w, b + D = L.align * (w + 1)
  | .slots s => b = s x

/-- Live target allocations are pairwise disjoint (fresh addresses only). -/
def TDisj (mt : AllocMode) (m : Mem) : Prop :=
  match mt with
  | .fresh _ => ∀ (j1 j2 : Nat) (a1 a2 : Alloc), j1 ≠ j2 → m.allocs[j1]? = some a1 →
      m.allocs[j2]? = some a2 → a1.live = true → a2.live = true →
      disjointRanges a1.base a1.size a2.base a2.size = true
  | .slots _ => True

/-- The source and target allocation modes match: the same static slot assignment, or fresh
addresses with alignments dividing the shift `D`. -/
def ModeRel (Ss : Sem) (mt : AllocMode) (D : Nat) (P : Prog) : Prop :=
  (∃ s, Ss = .slots s ∧ mt = .slots s ∧ D = 0) ∨
  (Ss = .fresh ∧ (∃ ω, mt = .fresh ω) ∧ ∀ y, (P.layout y).align ∣ D ∧
    (D = 0 ∨ 0 < (P.layout y).align))

/-- The state relation for the forward simulation. -/
structure SRel1 (P : Prog) (x : Local) (D : Nat) (J : Ptr → Prop) (mt : AllocMode)
    (f : Nat → Option Nat) (σ τ : State) : Prop where
  mem : MRel D J f σ.mem τ.mem
  frange : ∀ k k', f k = some k' → k < σ.mem.allocs.length ∧ k' < τ.mem.allocs.length
  fnone : ∀ k (al : Alloc), f k = none → σ.mem.allocs[k]? = some al → al.size = 0
  frame : ∀ y, y ≠ x → (σ.allocOf y = none ∧ τ.allocOf y = none) ∨
    ∃ k k', σ.allocOf y = some k ∧ τ.allocOf y = some k' ∧ f k = some k'
  framex : ∀ k, σ.allocOf x = some k → ∃ k', τ.allocOf x = some k' ∧ f k = some k'
  owner : ∀ y j k' (al : Alloc), σ.mem.allocs[j]? = some al → al.live = true → f j = some k' →
    τ.allocOf y = some k' → σ.allocOf y = some j
  tframe : ∀ y k, τ.allocOf y = some k → ∃ al : Alloc, τ.mem.allocs[k]? = some al ∧ al.live = true
  tinj : ∀ y z k, τ.allocOf y = some k → τ.allocOf z = some k → y = z
  slen : σ.frame.length = P.locals.length
  tlen : τ.frame.length = P.locals.length
  tdisj : TDisj mt τ.mem

/-- The target's allocation of `x` (for `x < P.locals.length`). -/
def XInv (P : Prog) (x : Local) (D : Nat) (mt : AllocMode) (τ : State) : Prop :=
  x < P.locals.length → ∃ (kx : Nat) (al : Alloc), τ.allocOf x = some kx ∧ τ.mem.allocs[kx]? = some al ∧
    al.size = (P.layout x).size ∧ XAddr mt D (P.layout x) x al.base

section SRel

variable {P : Prog} {x : Local} {D : Nat} {J : Ptr → Prop} {mt : AllocMode}
  {f : Nat → Option Nat}

theorem SRel1.frRel {σ τ : State} (h : SRel1 P x D J mt f σ τ) : FrRel f σ τ := by
  intro y k hk
  by_cases hy : y = x
  · subst hy; exact h.framex k hk
  · rcases h.frame y hy with ⟨h1, _⟩ | ⟨k1, k', h1, h2, h3⟩
    · rw [h1] at hk; cases hk
    · rw [h1] at hk; cases hk; exact ⟨k', h2, h3⟩

theorem inBounds_deallocate {st : State} {y : Local} {p : Ptr} {n : Nat}
    (h : (deallocate st y).mem.inBounds p n = true) : st.mem.inBounds p n = true := by
  unfold Mem.inBounds at h ⊢
  cases hp : p.prov with
  | none => rw [hp] at h; cases h
  | some k =>
    rw [hp] at h
    simp only at h ⊢
    rw [deallocate_getElem?] at h
    cases hk : st.mem.allocs[k]? with
    | none => rw [hk] at h; cases h
    | some al =>
      rw [hk] at h
      simp only [Option.map_some] at h
      split at h
      · simp at h
      · exact h

theorem TDisj.deallocate {m : AllocMode} {τ : State} (h : TDisj m τ.mem) (y : Local) :
    TDisj m (deallocate τ y).mem := by
  cases m with
  | slots s => exact True.intro
  | fresh ω =>
    unfold TDisj at h ⊢
    intro j1 j2 a1 a2 hne h1 h2 l1 l2
    rw [deallocate_getElem?] at h1 h2
    cases e1 : τ.mem.allocs[j1]? with
    | none => rw [e1] at h1; cases h1
    | some b1 =>
      cases e2 : τ.mem.allocs[j2]? with
      | none => rw [e2] at h2; cases h2
      | some b2 =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        have hb1 : b1.base = a1.base ∧ b1.size = a1.size ∧ b1.live = true := by
          split at h1 <;> (subst h1; simp_all)
        have hb2 : b2.base = a2.base ∧ b2.size = a2.size ∧ b2.live = true := by
          split at h2 <;> (subst h2; simp_all)
        have := h j1 j2 b1 b2 hne e1 e2 hb1.2.2 hb2.2.2
        rwa [hb1.1, hb1.2.1, hb2.1, hb2.2.1] at this

/-- Both programs free a local `y ≠ x`. -/
theorem SRel1.deallocate_both {σ τ : State} (h : SRel1 P x D J mt f σ τ) {y : Local}
    (hy : y ≠ x) : SRel1 P x D J mt f (deallocate σ y) (deallocate τ y) := by
  have hfr := h.frame y hy
  -- the allocations freed in the two states
  have hfree : ∀ j k', f j = some k' → σ.allocOf y = some j ∨ τ.allocOf y ≠ some k' ∨
      (∀ (al : Alloc), σ.mem.allocs[j]? = some al → al.live = false) := by
    intro j k' hj
    by_cases ht : τ.allocOf y = some k'
    · cases hl : σ.mem.allocs[j]? with
      | none => exact Or.inr (Or.inr fun al h => by cases h)
      | some al =>
        cases hlive : al.live with
        | false => exact Or.inr (Or.inr fun al' h' => by cases h'; exact hlive)
        | true => exact Or.inl (h.owner y j k' al hl hlive hj ht)
    · exact Or.inr (Or.inl ht)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' al hk hal
    rw [deallocate_getElem?] at hal
    cases e : σ.mem.allocs[k]? with
    | none => rw [e] at hal; cases hal
    | some al0 =>
      rw [e] at hal
      simp only [Option.map_some, Option.some.injEq] at hal
      obtain ⟨al', h1, h2, h3, h4⟩ := h.mem.falloc k k' al0 hk e
      refine ⟨if τ.allocOf y = some k' then { al' with live := false } else al', ?_, ?_, ?_, ?_⟩
      · rw [deallocate_getElem?, h1]; rfl
      · split at hal <;> split <;> (subst hal; simpa using h2)
      · split at hal <;> split <;> (subst hal; simpa using h3)
      · intro hl
        by_cases hsy : σ.allocOf y = some k
        · rw [ite_pos' hsy] at hal; subst hal; simp at hl
        · rw [ite_neg' hsy] at hal
          subst hal
          rcases hfree k k' hk with h5 | h5 | h5
          · exact absurd h5 hsy
          · rw [ite_neg' h5]; exact h4 hl
          · rw [h5 al0 e] at hl; cases hl
  · intro a
    rw [deallocate_get, deallocate_get]
    exact h.mem.cells a
  · intro p hj k hk
    cases hb : (deallocate σ y).mem.inBounds p k with
    | false => rfl
    | true =>
      have := inBounds_deallocate hb
      rw [h.mem.junk p hj k hk] at this; cases this
  · rcases h.mem.tpos with h0 | hpos
    · exact Or.inl h0
    · right
      intro k al hal
      rw [deallocate_getElem?] at hal
      cases e : τ.mem.allocs[k]? with
      | none => rw [e] at hal; cases hal
      | some al0 =>
        rw [e] at hal
        simp only [Option.map_some, Option.some.injEq] at hal
        have := hpos k al0 e
        split at hal <;> (subst hal; simpa using this)
  · intro k k' hk
    rw [deallocate_allocs_length, deallocate_allocs_length]
    exact h.frange k k' hk
  · intro k al hk hal
    rw [deallocate_getElem?] at hal
    cases e : σ.mem.allocs[k]? with
    | none => rw [e] at hal; cases hal
    | some al0 =>
      rw [e] at hal
      simp only [Option.map_some, Option.some.injEq] at hal
      have := h.fnone k al0 hk e
      split at hal <;> (subst hal; simpa using this)
  · intro z hz
    rw [deallocate_allocOf, deallocate_allocOf]
    by_cases hzy : z = y
    · simp [hzy]
    · simp only [hzy, ↓reduceIte]; exact h.frame z hz
  · intro k hk
    rw [deallocate_allocOf, ite_neg' (Ne.symm hy)] at hk
    rw [deallocate_allocOf, ite_neg' (Ne.symm hy)]
    exact h.framex k hk
  · intro z j k' al hal hlive hj ht
    rw [deallocate_allocOf] at ht ⊢
    by_cases hzy : z = y
    · rw [ite_pos' hzy] at ht; cases ht
    · rw [ite_neg' hzy] at ht ⊢
      rw [deallocate_getElem?] at hal
      cases e : σ.mem.allocs[j]? with
      | none => rw [e] at hal; cases hal
      | some al0 =>
        rw [e] at hal
        simp only [Option.map_some, Option.some.injEq] at hal
        have hl0 : al0.live = true := by
          split at hal <;> (subst hal; simp_all)
        exact h.owner z j k' al0 e hl0 hj ht
  · intro z k hk
    rw [deallocate_allocOf] at hk
    by_cases hzy : z = y
    · rw [ite_pos' hzy] at hk; cases hk
    · rw [ite_neg' hzy] at hk
      obtain ⟨al, h1, h2⟩ := h.tframe z k hk
      refine ⟨if τ.allocOf y = some k then { al with live := false } else al, ?_, ?_⟩
      · rw [deallocate_getElem?, h1]; rfl
      · have : τ.allocOf y ≠ some k := fun e => hzy (h.tinj z y k hk e)
        rw [ite_neg' this]; exact h2
  · intro z1 z2 k h1 h2
    rw [deallocate_allocOf] at h1 h2
    split at h1
    · cases h1
    · split at h2
      · cases h2
      · exact h.tinj z1 z2 k h1 h2
  · rw [deallocate_frame_length]; exact h.slen
  · rw [deallocate_frame_length]; exact h.tlen
  · exact h.tdisj.deallocate y

/-- The target relation for `x` survives freeing a local `y ≠ x` in the target. -/
theorem XInv.deallocate {τ : State} (h : XInv P x D mt τ) {y : Local} (hy : y ≠ x) :
    XInv P x D mt (deallocate τ y) := by
  intro hx
  obtain ⟨kx, al, h1, h2, h3, h4⟩ := h hx
  refine ⟨kx, if τ.allocOf y = some kx then { al with live := false } else al, ?_, ?_, ?_, ?_⟩
  · rw [deallocate_allocOf, ite_neg' (Ne.symm hy)]; exact h1
  · rw [deallocate_getElem?, h2]; rfl
  · split <;> simpa using h3
  · split <;> simpa using h4

/-- The source alone frees `x`. -/
theorem SRel1.deallocate_src_x {σ τ : State} (h : SRel1 P x D J mt f σ τ) :
    SRel1 P x D J mt f (deallocate σ x) τ := by
  refine ⟨⟨?_, ?_, ?_, h.mem.tpos⟩, ?_, ?_, ?_, ?_, ?_, h.tframe, h.tinj, ?_, h.tlen, h.tdisj⟩
  · intro k k' al hk hal
    rw [deallocate_getElem?] at hal
    cases e : σ.mem.allocs[k]? with
    | none => rw [e] at hal; cases hal
    | some al0 =>
      rw [e] at hal
      simp only [Option.map_some, Option.some.injEq] at hal
      obtain ⟨al', h1, h2, h3, h4⟩ := h.mem.falloc k k' al0 hk e
      refine ⟨al', h1, ?_, ?_, ?_⟩
      · split at hal <;> (subst hal; simpa using h2)
      · split at hal <;> (subst hal; simpa using h3)
      · intro hl
        split at hal
        · subst hal; simp at hl
        · subst hal; exact h4 hl
  · intro a
    rw [deallocate_get]
    exact h.mem.cells a
  · intro p hj k hk
    cases hb : (deallocate σ x).mem.inBounds p k with
    | false => rfl
    | true =>
      have := inBounds_deallocate hb
      rw [h.mem.junk p hj k hk] at this; cases this
  · intro k k' hk
    rw [deallocate_allocs_length]
    exact h.frange k k' hk
  · intro k al hk hal
    rw [deallocate_getElem?] at hal
    cases e : σ.mem.allocs[k]? with
    | none => rw [e] at hal; cases hal
    | some al0 =>
      rw [e] at hal
      simp only [Option.map_some, Option.some.injEq] at hal
      have := h.fnone k al0 hk e
      split at hal <;> (subst hal; simpa using this)
  · intro z hz
    rw [deallocate_allocOf, ite_neg' hz]
    exact h.frame z hz
  · intro k hk
    rw [deallocate_allocOf, ite_pos' rfl] at hk
    cases hk
  · intro z j k' al hal hlive hj ht
    rw [deallocate_getElem?] at hal
    cases e : σ.mem.allocs[j]? with
    | none => rw [e] at hal; cases hal
    | some al0 =>
      rw [e] at hal
      simp only [Option.map_some, Option.some.injEq] at hal
      by_cases hsx : σ.allocOf x = some j
      · rw [ite_pos' hsx] at hal; subst hal; simp at hlive
      · rw [ite_neg' hsx] at hal
        subst hal
        have ho := h.owner z j k' _ e hlive hj ht
        rw [deallocate_allocOf]
        by_cases hzx : z = x
        · subst hzx; exact absurd ho hsx
        · rw [ite_neg' hzx]; exact ho
  · rw [deallocate_frame_length]; exact h.slen

/-- Extend a renaming by `kS ↦ kT`. -/
def fext (f : Nat → Option Nat) (kS kT : Nat) : Nat → Option Nat :=
  fun k => if k = kS then some kT else f k

theorem FExt.fext {σ τ : State} (h : SRel1 P x D J mt f σ τ) (kT : Nat) :
    FExt f (fext f σ.mem.allocs.length kT) := by
  intro k k' hk
  have := (h.frange k k' hk).1
  simp only [Toy.PlaceEval.fext, show k ≠ σ.mem.allocs.length by omega, ↓reduceIte, hk]

theorem getElem?_lt {l : List Alloc} {k : Nat} {al : Alloc} (h : l[k]? = some al) : k < l.length := by
  rcases Nat.lt_or_ge k l.length with h1 | h1
  · exact h1
  · rw [List.getElem?_eq_none h1] at h; cases h

/-- The source passes its overlap check if, for every target allocation that is the image of
a live source allocation, the target range is disjoint from it. -/
theorem SRel1.srcCheck {σ τ : State} (h : SRel1 P x D J mt f σ τ) {a n : Nat}
    (hT : ∀ k k' (al' : Alloc), f k = some k' → (∃ al : Alloc, σ.mem.allocs[k]? = some al ∧
      al.live = true) → τ.mem.allocs[k']? = some al' → al'.live = true →
      disjointRanges a n al'.base al'.size = true) :
    (σ.mem.allocs.all fun al => !al.live || disjointRanges (a + D) n al.base al.size) = true := by
  rw [List.all_eq_true]
  intro al hmem
  obtain ⟨j, hj, hjal⟩ := List.getElem_of_mem hmem
  have e : σ.mem.allocs[j]? = some al := by rw [List.getElem?_eq_getElem hj, hjal]
  cases hl : al.live with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    cases hf : f j with
    | none =>
      have := h.fnone j al hf e
      simp [disjointRanges, this]
    | some j' =>
      obtain ⟨al', h1, h2, h3, h4⟩ := h.mem.falloc j j' al hf e
      have := hT j j' al' hf ⟨al, e, hl⟩ h1 (h4 hl)
      rw [h2, h3, disjointRanges_shift]
      exact this

/-- Both programs allocate a local `y ≠ x` (after freeing it). -/
theorem SRel1.alloc_both (hdj : DJOk D J) {σ τ : State} (h : SRel1 P x D J mt f σ τ) {y : Local}
    (hy : y ≠ x) (L : Layout) (aT : Nat)
    (hcheck : ∀ ω, mt = .fresh ω → ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al →
      al.live = true → disjointRanges aT L.size al.base al.size = true)
    (hpos : D = 0 ∨ 0 < aT) :
    SRel1 P x D J mt (fext f σ.mem.allocs.length τ.mem.allocs.length)
      (allocState σ y L (aT + D)) (allocState τ y L aT) := by
  have hext := FExt.fext h τ.mem.allocs.length
  have hflen : σ.frame.length = τ.frame.length := h.slen.trans h.tlen.symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' al hk hal
    simp only [fext] at hk
    by_cases hkS : k = σ.mem.allocs.length
    · subst hkS
      rw [ite_pos' rfl] at hk
      cases hk
      rw [allocState_getElem?_new] at hal
      cases hal
      exact ⟨_, allocState_getElem?_new _ _ _ _, rfl, rfl, fun _ => rfl⟩
    · rw [ite_neg' hkS] at hk
      have hr := h.frange k k' hk
      rw [allocState_getElem?_old hr.1] at hal
      obtain ⟨al', h1, h2⟩ := h.mem.falloc k k' al hk hal
      exact ⟨al', by rw [allocState_getElem?_old hr.2]; exact h1, h2⟩
  · intro t
    rw [allocState_get, allocState_get]
    by_cases h1 : aT + D ≤ t + D ∧ t + D < aT + D + L.size
    · rw [ite_pos' h1]; exact trivial
    · rw [ite_neg' h1, ite_neg' (by omega)]
      exact (h.mem.cells t).mono hext
  · intro p hj k hk
    cases hb : (allocState σ y L (aT + D)).mem.inBounds p k with
    | false => rfl
    | true =>
      rcases allocState_inBounds hb with ⟨hp, h1, _⟩ | hb'
      · rcases hdj.small p hj with h2 | h2
        · rw [hp] at h2; cases h2
        · omega
      · rw [h.mem.junk p hj k hk] at hb'; cases hb'
  · rcases hpos with h0 | hpos'
    · exact Or.inl h0
    · rcases h.mem.tpos with h0 | hp0
      · exact Or.inl h0
      · right
        intro k al hal
        rw [allocState_getElem?] at hal
        split at hal
        · exact hp0 k al hal
        · split at hal
          · cases hal; exact hpos'
          · cases hal
  · intro k k' hk
    simp only [fext] at hk
    rw [allocState_length, allocState_length]
    split at hk
    · cases hk; omega
    · have := h.frange k k' hk; omega
  · intro k al hk hal
    simp only [fext] at hk
    by_cases hkS : k = σ.mem.allocs.length
    · rw [ite_pos' hkS] at hk; cases hk
    · rw [ite_neg' hkS] at hk
      rw [allocState_getElem?] at hal
      by_cases hlt : k < σ.mem.allocs.length
      · rw [ite_pos' hlt] at hal; exact h.fnone k al hk hal
      · rw [ite_neg' hlt, ite_neg' hkS] at hal; cases hal
  · intro z hz
    rw [allocState_allocOf, allocState_allocOf, ← hflen]
    by_cases hc : y = z ∧ y < σ.frame.length
    · rw [ite_pos' hc, ite_pos' hc]
      exact Or.inr ⟨_, _, rfl, rfl, by simp [fext]⟩
    · rw [ite_neg' hc, ite_neg' hc]
      rcases h.frame z hz with h1 | ⟨k, k', h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨k, k', h1, h2, hext k k' h3⟩
  · intro k hk
    have hyx : ∀ n : Nat, ¬ (y = x ∧ y < n) := fun n hc => hy hc.1
    rw [allocState_allocOf, ite_neg' (hyx _)] at hk
    obtain ⟨k', h1, h2⟩ := h.framex k hk
    refine ⟨k', ?_, hext k k' h2⟩
    rw [allocState_allocOf, ite_neg' (hyx _)]
    exact h1
  · intro z j k' al hal hlive hj ht
    rw [allocState_allocOf] at ht ⊢
    simp only [fext] at hj
    by_cases hjS : j = σ.mem.allocs.length
    · rw [ite_pos' hjS] at hj
      cases hj
      by_cases hc : y = z ∧ y < τ.frame.length
      · rw [← hflen] at hc; rw [ite_pos' hc, hjS]
      · rw [ite_neg' hc] at ht
        obtain ⟨al', h1, _⟩ := h.tframe z _ ht
        have := getElem?_lt h1
        omega
    · rw [ite_neg' hjS] at hj
      have hr := h.frange j k' hj
      rw [allocState_getElem?_old hr.1] at hal
      by_cases hc : y = z ∧ y < τ.frame.length
      · rw [ite_pos' hc] at ht; cases ht; omega
      · rw [ite_neg' hc] at ht
        have ho := h.owner z j k' al hal hlive hj ht
        rw [← hflen] at hc
        rw [ite_neg' hc]
        exact ho
  · intro z k hk
    rw [allocState_allocOf] at hk
    split at hk
    · cases hk; exact ⟨_, allocState_getElem?_new _ _ _ _, rfl⟩
    · obtain ⟨al, h1, h2⟩ := h.tframe z k hk
      exact ⟨al, by rw [allocState_getElem?_old (getElem?_lt h1)]; exact h1, h2⟩
  · intro z1 z2 k h1 h2
    rw [allocState_allocOf] at h1 h2
    split at h1
    · rename_i hc1
      split at h2
      · rename_i hc2; exact hc1.1.symm.trans hc2.1
      · cases h1
        obtain ⟨al, e, _⟩ := h.tframe z2 _ h2
        have := getElem?_lt e; omega
    · split at h2
      · cases h2
        obtain ⟨al, e, _⟩ := h.tframe z1 _ h1
        have := getElem?_lt e; omega
      · exact h.tinj z1 z2 k h1 h2
  · rw [allocState_frame_length]; exact h.slen
  · rw [allocState_frame_length]; exact h.tlen
  · cases mt with
    | slots s => exact True.intro
    | fresh ω =>
      have hd := h.tdisj
      unfold TDisj at hd ⊢
      intro j1 j2 a1 a2 hne h1 h2 l1 l2
      rw [allocState_getElem?] at h1 h2
      split at h1
      · split at h2
        · exact hd j1 j2 a1 a2 hne h1 h2 l1 l2
        · split at h2
          · cases h2
            rw [disjointRanges_comm]
            exact hcheck ω rfl j1 a1 h1 l1
          · cases h2
      · split at h1
        · cases h1
          split at h2
          · exact hcheck ω rfl j2 a2 h2 l2
          · split at h2
            · omega
            · cases h2
        · cases h1

theorem XInv.allocState {τ : State} (h : XInv P x D mt τ) {y : Local} (hy : y ≠ x) (L : Layout)
    (a : Nat) : XInv P x D mt (allocState τ y L a) := by
  intro hx
  obtain ⟨kx, al, h1, h2, h3, h4⟩ := h hx
  refine ⟨kx, al, ?_, ?_, h3, h4⟩
  · rw [allocState_allocOf, ite_neg' (fun hc => hy hc.1)]; exact h1
  · rw [allocState_getElem?_old (getElem?_lt h2)]; exact h2

theorem XInv.allocate {m : AllocMode} {τ τ' : State} (h : XInv P x D mt τ) {y : Local}
    (hy : y ≠ x) {L : Layout} (ha : allocate m τ y L = some τ') : XInv P x D mt τ' := by
  obtain ⟨a, rfl⟩ := allocate_some ha
  exact h.allocState hy L a

theorem TDisj.of_allocs {m m' : Mem} (he : m'.allocs = m.allocs) (h : TDisj mt m) : TDisj mt m' := by
  cases mt with
  | slots s => exact True.intro
  | fresh ω =>
    unfold TDisj at h ⊢
    rw [he]; exact h

/-- Replacing the memories by related memories with the same allocation tables. -/
theorem SRel1.with_mem {σ τ : State} (h : SRel1 P x D J mt f σ τ) {m n : Mem}
    (hm : MRel D J f m n) (hma : m.allocs = σ.mem.allocs) (hna : n.allocs = τ.mem.allocs) :
    SRel1 P x D J mt f { σ with mem := m } { τ with mem := n } := by
  refine ⟨hm, ?_, ?_, h.frame, h.framex, ?_, ?_, h.tinj, h.slen, h.tlen, h.tdisj.of_allocs hna⟩
  · simp only [hma, hna]; exact h.frange
  · simp only [hma]; exact h.fnone
  · simp only [hma]; exact h.owner
  · simp only [hna]; exact h.tframe

/-- The source alone allocates `x < P.locals.length` at the target's address of `x`, shifted. -/
theorem SRel1.alloc_src_x_lt (hdj : DJOk D J) {σ τ : State} (h : SRel1 P x D J mt f σ τ)
    (hsx : σ.allocOf x = none) (hxl : x < P.locals.length) {kx : Nat} {al : Alloc}
    (h1 : τ.allocOf x = some kx) (h2 : τ.mem.allocs[kx]? = some al)
    (h3 : al.size = (P.layout x).size) :
    SRel1 P x D J mt (fext f σ.mem.allocs.length kx)
      (allocState σ x (P.layout x) (al.base + D)) τ := by
  have hext := FExt.fext h kx
  have hlive : al.live = true := by
    obtain ⟨al', e, l⟩ := h.tframe x kx h1
    rw [h2] at e; cases e; exact l
  have hxs : x < σ.frame.length := h.slen ▸ hxl
  refine ⟨⟨?_, ?_, ?_, h.mem.tpos⟩, ?_, ?_, ?_, ?_, ?_, h.tframe, h.tinj, ?_, h.tlen, h.tdisj⟩
  · intro k k' al0 hk hal
    simp only [fext] at hk
    by_cases hkS : k = σ.mem.allocs.length
    · subst hkS
      rw [ite_pos' rfl] at hk
      cases hk
      rw [allocState_getElem?_new] at hal
      cases hal
      exact ⟨al, h2, rfl, h3.symm, fun _ => hlive⟩
    · rw [ite_neg' hkS] at hk
      have hr := h.frange k k' hk
      rw [allocState_getElem?_old hr.1] at hal
      exact h.mem.falloc k k' al0 hk hal
  · intro t
    rw [allocState_get]
    by_cases hc : al.base + D ≤ t + D ∧ t + D < al.base + D + (P.layout x).size
    · rw [ite_pos' hc]; exact trivial
    · rw [ite_neg' hc]; exact (h.mem.cells t).mono hext
  · intro p hj k hk
    cases hb : (allocState σ x (P.layout x) (al.base + D)).mem.inBounds p k with
    | false => rfl
    | true =>
      rcases allocState_inBounds hb with ⟨hp, h4, _⟩ | hb'
      · rcases hdj.small p hj with h5 | h5
        · rw [hp] at h5; cases h5
        · omega
      · rw [h.mem.junk p hj k hk] at hb'; cases hb'
  · intro k k' hk
    simp only [fext] at hk
    rw [allocState_length]
    split at hk
    · cases hk; exact ⟨by omega, getElem?_lt h2⟩
    · have := h.frange k k' hk; omega
  · intro k al0 hk hal
    simp only [fext] at hk
    by_cases hkS : k = σ.mem.allocs.length
    · rw [ite_pos' hkS] at hk; cases hk
    · rw [ite_neg' hkS] at hk
      rw [allocState_getElem?] at hal
      by_cases hlt : k < σ.mem.allocs.length
      · rw [ite_pos' hlt] at hal; exact h.fnone k al0 hk hal
      · rw [ite_neg' hlt, ite_neg' hkS] at hal; cases hal
  · intro z hz
    rw [allocState_allocOf, ite_neg' (fun hc => hz hc.1.symm)]
    rcases h.frame z hz with h4 | ⟨k, k', h4, h5, h6⟩
    · exact Or.inl h4
    · exact Or.inr ⟨k, k', h4, h5, hext k k' h6⟩
  · intro k hk
    rw [allocState_allocOf, ite_pos' ⟨rfl, hxs⟩] at hk
    cases hk
    exact ⟨kx, h1, by simp [fext]⟩
  · intro z j k' al0 hal hl hj ht
    rw [allocState_allocOf]
    simp only [fext] at hj
    by_cases hjS : j = σ.mem.allocs.length
    · rw [ite_pos' hjS] at hj
      cases hj
      have hzx := h.tinj z x kx ht h1
      subst hzx
      rw [ite_pos' ⟨rfl, hxs⟩, hjS]
    · rw [ite_neg' hjS] at hj
      have hr := h.frange j k' hj
      rw [allocState_getElem?_old hr.1] at hal
      have ho := h.owner z j k' al0 hal hl hj ht
      by_cases hzx : z = x
      · subst hzx; rw [hsx] at ho; cases ho
      · rw [ite_neg' (fun hc => hzx hc.1.symm)]; exact ho
  · rw [allocState_frame_length]; exact h.slen

theorem layout_ge {P : Prog} {x : Local} (h : P.locals.length ≤ x) : P.layout x = ⟨0, 1⟩ := by
  simp [Prog.layout, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- The source alone allocates `x ≥ P.locals.length` (a zero-size allocation that no frame
records). -/
theorem SRel1.alloc_src_x_ge {σ τ : State} (h : SRel1 P x D J mt f σ τ)
    (hxl : P.locals.length ≤ x) (a : Nat) :
    SRel1 P x D J mt f (allocState σ x (P.layout x) a) τ := by
  have hsz : (P.layout x).size = 0 := by rw [layout_ge hxl]
  have hxs : σ.frame.length ≤ x := by rw [h.slen]; exact hxl
  have hnf : ∀ z, (allocState σ x (P.layout x) a).allocOf z = σ.allocOf z := by
    intro z
    rw [allocState_allocOf, ite_neg' (show ¬ (x = z ∧ x < σ.frame.length) from
      fun hc => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hc.2 hxs))]
  refine ⟨⟨?_, ?_, ?_, h.mem.tpos⟩, ?_, ?_, ?_, ?_, ?_, h.tframe, h.tinj, ?_, h.tlen, h.tdisj⟩
  · intro k k' al0 hk hal
    have hr := h.frange k k' hk
    rw [allocState_getElem?_old hr.1] at hal
    exact h.mem.falloc k k' al0 hk hal
  · intro t
    rw [allocState_get, hsz, ite_neg' (by omega)]
    exact h.mem.cells t
  · intro p hj k hk
    cases hb : (allocState σ x (P.layout x) a).mem.inBounds p k with
    | false => rfl
    | true =>
      rcases allocState_inBounds hb with ⟨_, h4, h5⟩ | hb'
      · omega
      · rw [h.mem.junk p hj k hk] at hb'; cases hb'
  · intro k k' hk
    rw [allocState_length]
    have := h.frange k k' hk; omega
  · intro k al0 hk hal
    rw [allocState_getElem?] at hal
    by_cases hlt : k < σ.mem.allocs.length
    · rw [ite_pos' hlt] at hal; exact h.fnone k al0 hk hal
    · rw [ite_neg' hlt] at hal
      split at hal
      · cases hal; exact hsz
      · cases hal
  · intro z hz; rw [hnf]; exact h.frame z hz
  · intro k hk; rw [hnf] at hk; exact h.framex k hk
  · intro z j k' al0 hal hl hj ht
    rw [hnf]
    have hr := h.frange j k' hj
    rw [allocState_getElem?_old hr.1] at hal
    exact h.owner z j k' al0 hal hl hj ht
  · rw [allocState_frame_length]; exact h.slen

theorem addr_shift {a d w : Nat} (h : a ∣ d) : a * (w + d / a + 1) = a * (w + 1) + d := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_div_cancel' h, Nat.mul_add]
  omega

/-- The source executes `storageLive x` (a step the target does not take). -/
theorem SRel1.storageLive_src_x {Ss : Sem} (hmode : ModeRel Ss mt D P) (hdj : DJOk D J)
    {σ τ : State} (h : SRel1 P x D J mt f σ τ) (hx : XInv P x D mt τ) :
    ∃ ω0 σ' f', execStmt (Ss.mode ω0) P σ (.storageLive x) = .ok none σ' ∧
      SRel1 P x D J mt f' σ' τ := by
  have h1 := h.deallocate_src_x
  have hsx : (deallocate σ x).allocOf x = none := by rw [deallocate_allocOf, ite_pos' rfl]
  by_cases hxl : x < P.locals.length
  · obtain ⟨kx, al, e1, e2, e3, e4⟩ := hx hxl
    have hrel := h1.alloc_src_x_lt hdj hsx hxl e1 e2 e3
    rcases hmode with ⟨s, rfl, rfl, rfl⟩ | ⟨rfl, ⟨ω, rfl⟩, _⟩
    · refine ⟨fun _ => 0, _, _, ?_, hrel⟩
      simp only [execStmt, Sem.mode, allocate_slots]
      simp only [XAddr] at e4
      rw [e4]; rfl
    · obtain ⟨w, hw⟩ := e4
      refine ⟨fun _ => w, _, _, ?_, hrel⟩
      have hchk := h1.srcCheck (a := al.base) (n := (P.layout x).size) (by
        intro k k' al' hk ⟨al0, hal0, hl0⟩ hal' hl'
        have hne : k' ≠ kx := by
          intro he; rw [he] at hk
          have := h1.owner x k kx al0 hal0 hl0 hk e1
          rw [hsx] at this; cases this
        have hd := h1.tdisj
        unfold TDisj at hd
        rw [← e3]
        exact hd kx k' al al' (Ne.symm hne) e2 hal' (by
          obtain ⟨al'', e, l⟩ := h1.tframe x kx e1
          rw [e2] at e; cases e; exact l) hl')
      simp only [execStmt, Sem.mode, allocate_fresh, ← hw, hchk, ↓reduceIte]
  · have hxl' : P.locals.length ≤ x := Nat.le_of_not_lt hxl
    rcases hmode with ⟨s, rfl, rfl, rfl⟩ | ⟨rfl, ⟨ω, rfl⟩, _⟩
    · exact ⟨fun _ => 0, _, _, by simp only [execStmt, Sem.mode, allocate_slots]; rfl,
        h1.alloc_src_x_ge hxl' _⟩
    · refine ⟨fun _ => 0, allocState (deallocate σ x) x (P.layout x) ((P.layout x).align * (0 + 1)),
        f, ?_, h1.alloc_src_x_ge hxl' _⟩
      have hsz : (P.layout x).size = 0 := by rw [layout_ge hxl']
      have hchk : ((deallocate σ x).mem.allocs.all fun al =>
          !al.live || disjointRanges ((P.layout x).align * ((fun _ => 0) (deallocate σ x).mem.allocs.length + 1))
            (P.layout x).size al.base al.size) = true := by
        rw [List.all_eq_true]; intro al _; simp [hsz, disjointRanges]
      simp only [execStmt, Sem.mode, allocate_fresh, hchk, ↓reduceIte]

/-- Both programs allocate a local `y ≠ x`: when the target's allocation succeeds, the source's
succeeds for a suitable oracle, at the target's address shifted by `D`. -/
theorem SRel1.alloc_exec {Ss : Sem} (hmode : ModeRel Ss mt D P) (hdj : DJOk D J)
    {σ τ : State} (h : SRel1 P x D J mt f σ τ) {y : Local} (hy : y ≠ x)
    {τ' : State} (ht : allocate mt τ y (P.layout y) = some τ') :
    ∃ ω0 σ' f', allocate (Ss.mode ω0) σ y (P.layout y) = some σ' ∧
      SRel1 P x D J mt f' σ' τ' := by
  rcases hmode with ⟨s, rfl, rfl, rfl⟩ | ⟨rfl, ⟨ω, rfl⟩, hal⟩
  · rw [allocate_slots] at ht
    cases ht
    exact ⟨fun _ => 0, _, fext f _ _, by simp only [Sem.mode, allocate_slots]; rfl,
      by simpa using h.alloc_both hdj hy (P.layout y) (s y) (fun ω e => by cases e) (Or.inl rfl)⟩
  · rw [allocate_fresh] at ht
    split at ht
    · rename_i htc
      cases ht
      have hdvd := (hal y).1
      have hpos : D = 0 ∨ 0 < (P.layout y).align * (ω τ.mem.allocs.length + 1) := by
        rcases (hal y).2 with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Nat.mul_pos h0 (Nat.succ_pos _))
      have htc' : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al →
          al.live = true → disjointRanges ((P.layout y).align *
            (ω τ.mem.allocs.length + 1)) (P.layout y).size al.base al.size = true := by
        intro k al hal' hl
        have := List.all_eq_true.1 htc al (List.mem_of_getElem? hal')
        simpa [hl] using this
      have hrel := h.alloc_both hdj hy (P.layout y) _ (fun ω' _ => htc') hpos
      refine ⟨fun _ => ω τ.mem.allocs.length + D / (P.layout y).align, _, _, ?_, hrel⟩
      have hchk := h.srcCheck (a := (P.layout y).align * (ω τ.mem.allocs.length + 1))
        (n := (P.layout y).size) (fun k k' al' _ _ hal' hl' => htc' k' al' hal' hl')
      simp only [Sem.mode, allocate_fresh, addr_shift hdvd, hchk, ↓reduceIte]
    · cases ht

/-- Both programs execute `storageLive y` for `y ≠ x`. -/
theorem SRel1.storageLive_both {Ss : Sem} (hmode : ModeRel Ss mt D P) (hdj : DJOk D J)
    {σ τ : State} (h : SRel1 P x D J mt f σ τ) (hx : XInv P x D mt τ) {y : Local} (hy : y ≠ x)
    {T : Prog} (hT : T.locals = P.locals) {τ' : State}
    (ht : execStmt mt T τ (.storageLive y) = .ok none τ') :
    ∃ ω0 σ' f', execStmt (Ss.mode ω0) P σ (.storageLive y) = .ok none σ' ∧
      SRel1 P x D J mt f' σ' τ' ∧ XInv P x D mt τ' := by
  have hlay : T.layout y = P.layout y := by simp [Prog.layout, hT]
  simp only [execStmt, hlay] at ht
  split at ht
  · rename_i τ2 hτ2
    cases ht
    obtain ⟨ω0, σ', f', h1, h2⟩ := (h.deallocate_both hy).alloc_exec hmode hdj hy hτ2
    exact ⟨ω0, σ', f', by simp only [execStmt, h1], h2, (hx.deallocate hy).allocate hy hτ2⟩
  · cases ht

/-- Both programs execute `storageDead y` for `y ≠ x`. -/
theorem SRel1.storageDead_both {σ τ : State} (h : SRel1 P x D J mt f σ τ) (hx : XInv P x D mt τ)
    {y : Local} (hy : y ≠ x) :
    SRel1 P x D J mt f (deallocate σ y) (deallocate τ y) ∧ XInv P x D mt (deallocate τ y) :=
  ⟨h.deallocate_both hy, hx.deallocate hy⟩

end SRel

end Toy.PlaceEval
