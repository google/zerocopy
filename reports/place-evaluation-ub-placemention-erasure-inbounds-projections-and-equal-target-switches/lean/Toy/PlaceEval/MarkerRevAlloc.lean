import Toy.PlaceEval.MarkerRevMem

/-!
# Storage-marker erasure, reverse direction: memory changes

How the memory relation `MRel2` behaves when allocations are freed or added on one or both
sides.
-/

namespace Toy.PlaceEval

/-- Pointers satisfying `JA A`: no provenance, or an address at most `A`. -/
def JA (A : Nat) (p : Ptr) : Prop := p.prov = none ∨ p.addr ≤ A

/-- `m'` has the allocations of `m` (same bases and sizes, liveness only lost) and its cells. -/
structure Weaker (m m' : Mem) : Prop where
  cells : m'.cells = m.cells
  len : m'.allocs.length = m.allocs.length
  alloc : ∀ (k : Nat) (al' : Alloc), m'.allocs[k]? = some al' → ∃ al : Alloc, m.allocs[k]? = some al ∧
    al.base = al'.base ∧ al.size = al'.size ∧ (al'.live = true → al.live = true)
  alloc' : ∀ (k : Nat) (al : Alloc), m.allocs[k]? = some al → ∃ al' : Alloc, m'.allocs[k]? = some al' ∧
    al.base = al'.base ∧ al.size = al'.size

theorem Weaker.refl (m : Mem) : Weaker m m :=
  ⟨rfl, rfl, fun _ al h => ⟨al, h, rfl, rfl, id⟩, fun _ al h => ⟨al, h, rfl, rfl⟩⟩

theorem weaker_deallocate (st : State) (y : Local) : Weaker st.mem (deallocate st y).mem := by
  refine ⟨deallocate_cells st y, deallocate_allocs_length st y, fun k al' h => ?_, fun k al h => ?_⟩
  · rw [deallocate_getElem?] at h
    cases e : st.mem.allocs[k]? with
    | none => rw [e] at h; cases h
    | some al =>
      rw [e] at h
      simp only [Option.map_some, Option.some.injEq] at h
      refine ⟨al, rfl, ?_, ?_, ?_⟩ <;> split at h <;> (subst h; simp_all)
  · refine ⟨if st.allocOf y = some k then { al with live := false } else al, ?_, ?_, ?_⟩
    · rw [deallocate_getElem?, h]; rfl
    · split <;> rfl
    · split <;> rfl

theorem Weaker.get {m m' : Mem} (h : Weaker m m') (a : Nat) : m'.get a = m.get a := by
  simp only [Mem.get, h.cells]

theorem Weaker.inBounds {m m' : Mem} (h : Weaker m m') {p : Ptr} {k : Nat}
    (hb : m'.inBounds p k = true) : m.inBounds p k = true := by
  obtain ⟨j, al', e1, e2, e3, e4, e5⟩ := inBounds_some hb
  obtain ⟨al, f1, f2, f3, f4⟩ := h.alloc j al' e2
  simp only [Mem.inBounds, e1, f1, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨f4 e3, by omega⟩, by omega⟩

theorem TDisj.weaker {mt : AllocMode} {m m' : Mem} (h : Weaker m m') (hd : TDisj mt m) :
    TDisj mt m' := by
  cases mt with
  | slots s => exact True.intro
  | fresh ω =>
    unfold TDisj at hd ⊢
    intro j1 j2 a1 a2 hne h1 h2 l1 l2
    obtain ⟨b1, e1, f1, g1, k1⟩ := h.alloc j1 a1 h1
    obtain ⟨b2, e2, f2, g2, k2⟩ := h.alloc j2 a2 h2
    have := hd j1 j2 b1 b2 hne e1 e2 (k1 l1) (k2 l2)
    rwa [f1, g1, f2, g2] at this

/-- `g'` extends `g`. -/
def GExt (g g' : Nat → Option (Nat × Nat × Nat)) : Prop := ∀ k v, g k = some v → g' k = some v

theorem V2.mono {J : Ptr → Prop} {g g' : Nat → Option (Nat × Nat × Nat)} (hg : GExt g g')
    {p q : Ptr} (h : V2 J g p q) : V2 J g' p q := by
  rcases h with ⟨kT, kS, bS, bT, h1, h2⟩ | h
  · exact Or.inl ⟨kT, kS, bS, bT, hg _ _ h1, h2⟩
  · exact Or.inr h

theorem CR2.mono {J : Ptr → Prop} {g g' : Nat → Option (Nat × Nat × Nat)} (hg : GExt g g')
    {c d : Cell} (h : CR2 J g c d) : CR2 J g' c d := by
  cases c <;> cases d <;> simp only [CR2] at h ⊢
  all_goals first | trivial | exact h | exact ⟨h.1, h.2.mono hg⟩

section MemChanges

variable {J : Ptr → Prop} {g : Nat → Option (Nat × Nat × Nat)} {A : Nat}

theorem MRel2.weaken {m n m' n' : Mem} (hm : MRel2 J g m n) (h1 : Weaker m m') (h2 : Weaker n n') :
    MRel2 J g m' n' := by
  refine ⟨fun kT kS bS bT hg => ?_, fun kT kS bS bT alS alT hg e1 e2 => ?_,
    fun kT kS bS bT alS alT hg e1 e2 l1 l2 i hi => ?_, fun p hj k hk => ?_,
    hm.sdisj.weaker h1, hm.tdisj.weaker h2, fun kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2 => ?_⟩
  · obtain ⟨⟨alS, f1, f2⟩, ⟨alT, f3, f4⟩⟩ := hm.gbase kT kS bS bT hg
    obtain ⟨alS', g1, g2, _⟩ := h1.alloc' kS alS f1
    obtain ⟨alT', g3, g4, _⟩ := h2.alloc' kT alT f3
    exact ⟨⟨alS', g1, by omega⟩, ⟨alT', g3, by omega⟩⟩
  · obtain ⟨a, f1, _, f3, _⟩ := h1.alloc kS alS e1
    obtain ⟨b, f4, _, f6, _⟩ := h2.alloc kT alT e2
    have := hm.gsize kT kS bS bT a b hg f1 f4
    omega
  · obtain ⟨a, f1, _, _, f4⟩ := h1.alloc kS alS e1
    obtain ⟨b, f5, _, f7, f8⟩ := h2.alloc kT alT e2
    rw [h1.get, h2.get]
    exact hm.cells kT kS bS bT a b hg f1 f5 (f4 l1) (f8 l2) i (by omega)
  · cases hb : m'.inBounds p k with
    | false => rfl
    | true => have := h1.inBounds hb; rw [hm.junk p hj k hk] at this; cases this
  · obtain ⟨c1, f1, _, _, k1⟩ := h2.alloc kT1 a1 e1
    obtain ⟨c2, f2, _, _, k2⟩ := h2.alloc kT2 a2 e2
    exact hm.ginj kT1 kT2 kS b1 b1' b2 b2' c1 c2 g1 g2 f1 f2 (k1 l1) (k2 l2)

/-- Add the entry `kT ↦ v` to `g`. -/
def gext (g : Nat → Option (Nat × Nat × Nat)) (kT : Nat) (v : Nat × Nat × Nat) :
    Nat → Option (Nat × Nat × Nat) := fun k => if k = kT then some v else g k

theorem MRel2.gbound {m n : Mem} (hm : MRel2 J g m n) {kT kS bS bT : Nat}
    (hg : g kT = some (kS, bS, bT)) : kS < m.allocs.length ∧ kT < n.allocs.length := by
  obtain ⟨⟨alS, f1, _⟩, ⟨alT, f3, _⟩⟩ := hm.gbase kT kS bS bT hg
  exact ⟨getElem?_lt f1, getElem?_lt f3⟩

theorem GExt.gext {m n : Mem} (hm : MRel2 J g m n) (v : Nat × Nat × Nat) :
    GExt g (Toy.PlaceEval.gext g n.allocs.length v) := by
  intro k w hk
  obtain ⟨kS, bS, bT⟩ := w
  have := (hm.gbound hk).2
  simp only [Toy.PlaceEval.gext, show k ≠ n.allocs.length by omega, ↓reduceIte, hk]

/-- Both sides allocate (`g` gains the new pair). -/
theorem MRel2.alloc_both {σ τ : State} (hm : MRel2 (JA A) g σ.mem τ.mem) (y z : Local)
    (L : Layout) (bS bT : Nat) (hA : A < bS)
    (hcS : ∀ (k : Nat) (al : Alloc), σ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges bS L.size al.base al.size = true)
    (hcT : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges bT L.size al.base al.size = true) :
    MRel2 (JA A) (gext g τ.mem.allocs.length (σ.mem.allocs.length, bS, bT))
      (allocState σ y L bS).mem (allocState τ z L bT).mem := by
  have hext := GExt.gext hm (σ.mem.allocs.length, bS, bT)
  refine ⟨fun kT kS cS cT hg => ?_, fun kT kS cS cT alS alT hg e1 e2 => ?_,
    fun kT kS cS cT alS alT hg e1 e2 l1 l2 i hi => ?_, fun p hj k hk => ?_, ?_, ?_,
    fun kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2 => ?_⟩
  · simp only [gext] at hg
    split at hg
    · cases hg
      rename_i h
      exact ⟨⟨_, allocState_getElem?_new _ _ _ _, rfl⟩,
        ⟨_, (by rw [h]; exact allocState_getElem?_new _ _ _ _), rfl⟩⟩
    · obtain ⟨⟨alS, f1, f2⟩, ⟨alT, f3, f4⟩⟩ := hm.gbase kT kS cS cT hg
      exact ⟨⟨alS, by rw [allocState_getElem?_old (getElem?_lt f1)]; exact f1, f2⟩,
        ⟨alT, by rw [allocState_getElem?_old (getElem?_lt f3)]; exact f3, f4⟩⟩
  · simp only [gext] at hg
    split at hg
    · rename_i h; cases hg; subst h
      rw [allocState_getElem?_new] at e1 e2
      cases e1; cases e2; rfl
    · have hb := hm.gbound hg
      rw [allocState_getElem?_old hb.1] at e1
      rw [allocState_getElem?_old hb.2] at e2
      exact hm.gsize kT kS cS cT alS alT hg e1 e2
  · rw [allocState_get, allocState_get]
    simp only [gext] at hg
    split at hg
    · rename_i h; cases hg; subst h
      rw [allocState_getElem?_new] at e2
      cases e2
      simp only at hi
      rw [ite_pos' ⟨by omega, by omega⟩]; exact trivial
    · have hb := hm.gbound hg
      rw [allocState_getElem?_old hb.1] at e1
      rw [allocState_getElem?_old hb.2] at e2
      obtain ⟨⟨alS', f1, f2⟩, ⟨alT', f3, f4⟩⟩ := hm.gbase kT kS cS cT hg
      rw [e1] at f1; cases f1
      rw [e2] at f3; cases f3
      have hsz := hm.gsize kT kS _ _ alS alT hg e1 e2
      have dS := hcS kS alS e1 l1
      have dT := hcT kT alT e2 l2
      rw [disjointRanges_comm] at dS dT
      have nS := not_mem_of_disjoint (a := cS + i) dS ⟨by omega, by omega⟩
      have nT := not_mem_of_disjoint (a := cT + i) dT ⟨by omega, by omega⟩
      rw [ite_neg' nS, ite_neg' nT]
      exact (hm.cells kT kS _ _ alS alT hg e1 e2 l1 l2 i hi).mono hext
  · cases hb : (allocState σ y L bS).mem.inBounds p k with
    | false => rfl
    | true =>
      rcases allocState_inBounds hb with ⟨hp, h1, _⟩ | hb'
      · rcases hj with h2 | h2
        · rw [hp] at h2; cases h2
        · omega
      · rw [hm.junk p hj k hk] at hb'; cases hb'
  · have hd := hm.sdisj
    unfold TDisj at hd ⊢
    intro j1 j2 a1 a2 hne h1 h2 l1 l2
    rw [allocState_getElem?] at h1 h2
    split at h1
    · split at h2
      · exact hd j1 j2 a1 a2 hne h1 h2 l1 l2
      · split at h2
        · cases h2; rw [disjointRanges_comm]; exact hcS j1 a1 h1 l1
        · cases h2
    · split at h1
      · cases h1
        split at h2
        · exact hcS j2 a2 h2 l2
        · split at h2
          · omega
          · cases h2
      · cases h1
  · have hd := hm.tdisj
    unfold TDisj at hd ⊢
    intro j1 j2 a1 a2 hne h1 h2 l1 l2
    rw [allocState_getElem?] at h1 h2
    split at h1
    · split at h2
      · exact hd j1 j2 a1 a2 hne h1 h2 l1 l2
      · split at h2
        · cases h2; rw [disjointRanges_comm]; exact hcT j1 a1 h1 l1
        · cases h2
    · split at h1
      · cases h1
        split at h2
        · exact hcT j2 a2 h2 l2
        · split at h2
          · omega
          · cases h2
      · cases h1
  · simp only [gext] at g1 g2
    rw [allocState_getElem?] at e1 e2
    split at g1 <;> split at g2
    · rename_i h1 h2; rw [h1, h2]
    · rename_i h1 h2
      cases g1
      have := (hm.gbound g2).1; omega
    · rename_i h1 h2
      cases g2
      have := (hm.gbound g1).1; omega
    · have hb1 := (hm.gbound g1).2
      have hb2 := (hm.gbound g2).2
      rw [ite_pos' hb1] at e1
      rw [ite_pos' hb2] at e2
      exact hm.ginj kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2

/-- The target alone allocates; the new allocation is related to the existing source
allocation `kx` (at base `bS`, of the same size and live), which no live target allocation is
related to. -/
theorem MRel2.alloc_tgt {σ τ : State} (hm : MRel2 J g σ.mem τ.mem) (z : Local) (L : Layout)
    (bT kx : Nat) (alx : Alloc) (hx : σ.mem.allocs[kx]? = some alx) (hsz : alx.size = L.size)
    (hfree : ∀ kT bS' bT' (alT : Alloc), g kT = some (kx, bS', bT') → τ.mem.allocs[kT]? = some alT →
      alT.live = true → False)
    (hcT : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges bT L.size al.base al.size = true) :
    MRel2 J (gext g τ.mem.allocs.length (kx, alx.base, bT)) σ.mem (allocState τ z L bT).mem := by
  have hext := GExt.gext hm (kx, alx.base, bT)
  refine ⟨fun kT kS cS cT hg => ?_, fun kT kS cS cT alS alT hg e1 e2 => ?_,
    fun kT kS cS cT alS alT hg e1 e2 l1 l2 i hi => ?_, hm.junk, hm.sdisj, ?_,
    fun kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2 => ?_⟩
  · simp only [gext] at hg
    split at hg
    · rename_i h; cases hg
      exact ⟨⟨alx, hx, rfl⟩, ⟨_, (by rw [h]; exact allocState_getElem?_new _ _ _ _), rfl⟩⟩
    · obtain ⟨hs, ⟨alT, f3, f4⟩⟩ := hm.gbase kT kS cS cT hg
      exact ⟨hs, ⟨alT, by rw [allocState_getElem?_old (getElem?_lt f3)]; exact f3, f4⟩⟩
  · simp only [gext] at hg
    split at hg
    · rename_i h; cases hg; subst h
      rw [allocState_getElem?_new] at e2
      rw [hx] at e1
      cases e1; cases e2; exact hsz
    · have hb := hm.gbound hg
      rw [allocState_getElem?_old hb.2] at e2
      exact hm.gsize kT kS cS cT alS alT hg e1 e2
  · rw [allocState_get]
    simp only [gext] at hg
    split at hg
    · rename_i h; cases hg; subst h
      rw [allocState_getElem?_new] at e2
      cases e2
      simp only at hi
      rw [ite_pos' ⟨by omega, by omega⟩]
      cases σ.mem.get (alx.base + i) <;> exact trivial
    · have hb := hm.gbound hg
      rw [allocState_getElem?_old hb.2] at e2
      obtain ⟨_, ⟨alT', f3, f4⟩⟩ := hm.gbase kT kS cS cT hg
      rw [e2] at f3; cases f3
      have dT := hcT kT alT e2 l2
      rw [disjointRanges_comm] at dT
      have nT := not_mem_of_disjoint (a := cT + i) dT ⟨by omega, by omega⟩
      rw [ite_neg' nT]
      exact (hm.cells kT kS _ _ alS alT hg e1 e2 l1 l2 i hi).mono hext
  · have hd := hm.tdisj
    unfold TDisj at hd ⊢
    intro j1 j2 a1 a2 hne h1 h2 l1 l2
    rw [allocState_getElem?] at h1 h2
    split at h1
    · split at h2
      · exact hd j1 j2 a1 a2 hne h1 h2 l1 l2
      · split at h2
        · cases h2; rw [disjointRanges_comm]; exact hcT j1 a1 h1 l1
        · cases h2
    · split at h1
      · cases h1
        split at h2
        · exact hcT j2 a2 h2 l2
        · split at h2
          · omega
          · cases h2
      · cases h1
  · simp only [gext] at g1 g2
    rw [allocState_getElem?] at e1 e2
    split at g1 <;> split at g2
    · rename_i h1 h2; rw [h1, h2]
    · rename_i h1 h2
      cases g1
      have hb2 := (hm.gbound g2).2
      rw [ite_pos' hb2] at e2
      exact (hfree kT2 b2 b2' a2 g2 e2 l2).elim
    · rename_i h1 h2
      cases g2
      have hb1 := (hm.gbound g1).2
      rw [ite_pos' hb1] at e1
      exact (hfree kT1 b1 b1' a1 g1 e1 l1).elim
    · have hb1 := (hm.gbound g1).2
      have hb2 := (hm.gbound g2).2
      rw [ite_pos' hb1] at e1
      rw [ite_pos' hb2] at e2
      exact hm.ginj kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2

/-- The target alone makes a zero-size allocation, related to nothing. -/
theorem MRel2.alloc_tgt_zero {σ τ : State} (hm : MRel2 J g σ.mem τ.mem) (z : Local) (L : Layout)
    (bT : Nat) (hz : L.size = 0) : MRel2 J g σ.mem (allocState τ z L bT).mem := by
  refine ⟨fun kT kS cS cT hg => ?_, fun kT kS cS cT alS alT hg e1 e2 => ?_,
    fun kT kS cS cT alS alT hg e1 e2 l1 l2 i hi => ?_, hm.junk, hm.sdisj, ?_,
    fun kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2 => ?_⟩
  · obtain ⟨hs, ⟨alT, f3, f4⟩⟩ := hm.gbase kT kS cS cT hg
    exact ⟨hs, ⟨alT, by rw [allocState_getElem?_old (getElem?_lt f3)]; exact f3, f4⟩⟩
  · rw [allocState_getElem?_old (hm.gbound hg).2] at e2
    exact hm.gsize kT kS cS cT alS alT hg e1 e2
  · rw [allocState_getElem?_old (hm.gbound hg).2] at e2
    rw [allocState_get, hz, ite_neg' (by omega)]
    exact hm.cells kT kS cS cT alS alT hg e1 e2 l1 l2 i hi
  · have hd := hm.tdisj
    unfold TDisj at hd ⊢
    intro j1 j2 a1 a2 hne h1 h2 l1 l2
    rw [allocState_getElem?] at h1 h2
    split at h1
    · split at h2
      · exact hd j1 j2 a1 a2 hne h1 h2 l1 l2
      · split at h2
        · cases h2; simp [disjointRanges, hz]
        · cases h2
    · split at h1
      · cases h1; simp [disjointRanges, hz]
      · cases h1
  · rw [allocState_getElem?_old (hm.gbound g1).2] at e1
    rw [allocState_getElem?_old (hm.gbound g2).2] at e2
    exact hm.ginj kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2

/-- The source alone allocates (at entry, for `x`). -/
theorem MRel2.alloc_src {σ τ : State} (hm : MRel2 (JA A) g σ.mem τ.mem) (z : Local) (L : Layout)
    (bS : Nat) (hA : A < bS)
    (hcS : ∀ (k : Nat) (al : Alloc), σ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges bS L.size al.base al.size = true) :
    MRel2 (JA A) g (allocState σ z L bS).mem τ.mem := by
  refine ⟨fun kT kS cS cT hg => ?_, fun kT kS cS cT alS alT hg e1 e2 => ?_,
    fun kT kS cS cT alS alT hg e1 e2 l1 l2 i hi => ?_, fun p hj k hk => ?_, ?_, hm.tdisj,
    fun kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2 =>
      hm.ginj kT1 kT2 kS b1 b1' b2 b2' a1 a2 g1 g2 e1 e2 l1 l2⟩
  · obtain ⟨⟨alS, f1, f2⟩, ht⟩ := hm.gbase kT kS cS cT hg
    exact ⟨⟨alS, by rw [allocState_getElem?_old (getElem?_lt f1)]; exact f1, f2⟩, ht⟩
  · rw [allocState_getElem?_old (hm.gbound hg).1] at e1
    exact hm.gsize kT kS cS cT alS alT hg e1 e2
  · rw [allocState_getElem?_old (hm.gbound hg).1] at e1
    rw [allocState_get]
    obtain ⟨⟨alS', f1, f2⟩, _⟩ := hm.gbase kT kS cS cT hg
    rw [e1] at f1; cases f1
    have hsz := hm.gsize kT kS _ _ alS alT hg e1 e2
    have dS := hcS kS alS e1 l1
    rw [disjointRanges_comm] at dS
    have nS := not_mem_of_disjoint (a := cS + i) dS ⟨by omega, by omega⟩
    rw [ite_neg' nS]
    exact hm.cells kT kS _ _ alS alT hg e1 e2 l1 l2 i hi
  · cases hb : (allocState σ z L bS).mem.inBounds p k with
    | false => rfl
    | true =>
      rcases allocState_inBounds hb with ⟨hp, h1, _⟩ | hb'
      · rcases hj with h2 | h2
        · rw [hp] at h2; cases h2
        · omega
      · rw [hm.junk p hj k hk] at hb'; cases hb'
  · have hd := hm.sdisj
    unfold TDisj at hd ⊢
    intro j1 j2 a1 a2 hne h1 h2 l1 l2
    rw [allocState_getElem?] at h1 h2
    split at h1
    · split at h2
      · exact hd j1 j2 a1 a2 hne h1 h2 l1 l2
      · split at h2
        · cases h2; rw [disjointRanges_comm]; exact hcS j1 a1 h1 l1
        · cases h2
    · split at h1
      · cases h1
        split at h2
        · exact hcS j2 a2 h2 l2
        · split at h2
          · omega
          · cases h2
      · cases h1

end MemChanges

end Toy.PlaceEval
