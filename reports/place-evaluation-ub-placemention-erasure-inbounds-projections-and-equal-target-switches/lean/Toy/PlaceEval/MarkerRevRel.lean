import Toy.PlaceEval.MarkerRevAlloc

/-!
# Storage-marker erasure, reverse direction: the state relation

`SRel2` relates a source state (a run of `eraseMarkers P x`) to a target state (a run of
`P`). In the source, `x` (if `x < P.locals.length`) has one allocation at base `X0` for the
whole run; every other source allocation is the image of a live target allocation shifted by
`D`.
-/

namespace Toy.PlaceEval

/-- The state relation for the reverse direction. -/
structure SRel2 (P : Prog) (x : Local) (D X0 A : Nat) (g : Nat → Option (Nat × Nat × Nat))
    (σ τ : State) : Prop where
  mem : MRel2 (JA A) g σ.mem τ.mem
  frame : ∀ y, y ≠ x → (σ.allocOf y = none ∧ τ.allocOf y = none) ∨
    ∃ kS kT bS bT, σ.allocOf y = some kS ∧ τ.allocOf y = some kT ∧ g kT = some (kS, bS, bT)
  xS : x < P.locals.length → σ.allocOf x = none ∨ ∃ (kx : Nat) (al : Alloc),
    σ.allocOf x = some kx ∧ σ.mem.allocs[kx]? = some al ∧ al.base = X0 ∧
    al.size = (P.layout x).size
  xT : ∀ kT, τ.allocOf x = some kT → ∃ kS bS bT, σ.allocOf x = some kS ∧ g kT = some (kS, bS, bT)
  xown : ∀ kT kS bS bT (alT : Alloc), g kT = some (kS, bS, bT) → σ.allocOf x = some kS →
    τ.mem.allocs[kT]? = some alT → alT.live = true → τ.allocOf x = some kT
  spre : ∀ jS (alS : Alloc), σ.mem.allocs[jS]? = some alS → alS.live = true →
    σ.allocOf x ≠ some jS → ∃ (jT : Nat) (alT : Alloc), g jT = some (jS, alS.base, alT.base) ∧
      τ.mem.allocs[jT]? = some alT ∧ alT.live = true ∧ alS.base = alT.base + D
  sframe : ∀ y k, σ.allocOf y = some k → ∃ al : Alloc, σ.mem.allocs[k]? = some al ∧ al.live = true
  sinj : ∀ y z k, σ.allocOf y = some k → σ.allocOf z = some k → y = z
  tframe : ∀ y k, τ.allocOf y = some k → ∃ al : Alloc, τ.mem.allocs[k]? = some al ∧ al.live = true
  tinj : ∀ y z k, τ.allocOf y = some k → τ.allocOf z = some k → y = z
  slen : σ.frame.length = P.locals.length
  tlen : τ.frame.length = P.locals.length
  tpos : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al → 0 < al.base

section SRel2

variable {P : Prog} {x : Local} {D X0 A : Nat} {g : Nat → Option (Nat × Nat × Nat)}

theorem SRel2.frRel2 {σ τ : State} (h : SRel2 P x D X0 A g σ τ) : FrRel2 g σ τ := by
  intro y kS kT h1 h2
  by_cases hy : y = x
  · subst hy
    obtain ⟨kS', bS, bT, e1, e2⟩ := h.xT kT h2
    rw [h1] at e1; cases e1
    exact ⟨bS, bT, e2⟩
  · rcases h.frame y hy with ⟨e1, _⟩ | ⟨kS', kT', bS, bT, e1, e2, e3⟩
    · rw [h1] at e1; cases e1
    · rw [h1] at e1; cases e1
      rw [h2] at e2; cases e2
      exact ⟨bS, bT, e3⟩

theorem SRel2.with_mem {σ τ : State} (h : SRel2 P x D X0 A g σ τ) {m n : Mem}
    (hm : MRel2 (JA A) g m n) (hma : m.allocs = σ.mem.allocs) (hna : n.allocs = τ.mem.allocs) :
    SRel2 P x D X0 A g { σ with mem := m } { τ with mem := n } := by
  refine ⟨hm, h.frame, ?_, h.xT, ?_, ?_, ?_, h.sinj, ?_, h.tinj, h.slen, h.tlen, ?_⟩
  · simp only [hma]; exact h.xS
  · simp only [hna]; exact h.xown
  · simp only [hma, hna]; exact h.spre
  · simp only [hma]; exact h.sframe
  · simp only [hna]; exact h.tframe
  · simp only [hna]; exact h.tpos

theorem deallocate_live {st : State} {y : Local} {k : Nat} {al : Alloc}
    (h : (deallocate st y).mem.allocs[k]? = some al) (hl : al.live = true) :
    st.allocOf y ≠ some k ∧ st.mem.allocs[k]? = some al := by
  rw [deallocate_getElem?] at h
  cases e : st.mem.allocs[k]? with
  | none => rw [e] at h; cases h
  | some al0 =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    by_cases hy : st.allocOf y = some k
    · rw [ite_pos' hy] at h; subst h; simp at hl
    · rw [ite_neg' hy] at h; exact ⟨hy, by rw [h]⟩

theorem deallocate_keep {st : State} {y : Local} {k : Nat} {al : Alloc}
    (h : st.mem.allocs[k]? = some al) (hy : st.allocOf y ≠ some k) :
    (deallocate st y).mem.allocs[k]? = some al := by
  rw [deallocate_getElem?, h]; simp [hy]

theorem deallocate_base {st : State} {y : Local} {k : Nat} {al : Alloc}
    (h : st.mem.allocs[k]? = some al) : ∃ al' : Alloc, (deallocate st y).mem.allocs[k]? = some al' ∧
      al'.base = al.base ∧ al'.size = al.size := by
  refine ⟨if st.allocOf y = some k then { al with live := false } else al, ?_, ?_, ?_⟩
  · rw [deallocate_getElem?, h]; rfl
  · split <;> rfl
  · split <;> rfl

/-- Both programs free `y ≠ x`. -/
theorem SRel2.deallocate_both {σ τ : State} (h : SRel2 P x D X0 A g σ τ) {y : Local}
    (hy : y ≠ x) : SRel2 P x D X0 A g (deallocate σ y) (deallocate τ y) := by
  have hyx : ∀ z, z = x → z ≠ y := fun z hz => hz ▸ (Ne.symm hy)
  refine ⟨h.mem.weaken (weaker_deallocate σ y) (weaker_deallocate τ y), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [deallocate_allocOf, deallocate_allocOf]
    by_cases hzy : z = y
    · simp [hzy]
    · simp only [hzy, ↓reduceIte]; exact h.frame z hz
  · intro hx
    rcases h.xS hx with hn | ⟨kx, al, e1, e2, e3, e4⟩
    · left; rw [deallocate_allocOf, ite_neg' (hyx x rfl)]; exact hn
    obtain ⟨al', f1, f2, f3⟩ := deallocate_base (y := y) e2
    refine Or.inr ⟨kx, al', ?_, f1, f2.trans e3, f3.trans e4⟩
    rw [deallocate_allocOf, ite_neg' (hyx x rfl)]; exact e1
  · intro kT hk
    rw [deallocate_allocOf, ite_neg' (hyx x rfl)] at hk
    obtain ⟨kS, bS, bT, e1, e2⟩ := h.xT kT hk
    exact ⟨kS, bS, bT, by rw [deallocate_allocOf, ite_neg' (hyx x rfl)]; exact e1, e2⟩
  · intro kT kS bS bT alT hg hsx he hl
    rw [deallocate_allocOf, ite_neg' (hyx x rfl)] at hsx ⊢
    obtain ⟨_, he'⟩ := deallocate_live he hl
    exact h.xown kT kS bS bT alT hg hsx he' hl
  · intro jS alS he hl hne
    rw [deallocate_allocOf, ite_neg' (hyx x rfl)] at hne
    obtain ⟨hny, he'⟩ := deallocate_live he hl
    obtain ⟨jT, alT, f1, f2, f3, f4⟩ := h.spre jS alS he' hl hne
    refine ⟨jT, alT, f1, deallocate_keep f2 ?_, f3, f4⟩
    intro hty
    rcases h.frame y hy with ⟨_, e2⟩ | ⟨kS, kT, bS, bT, e1, e2, e3⟩
    · rw [e2] at hty; cases hty
    · rw [e2] at hty; cases hty
      rw [e3] at f1; cases f1
      exact hny e1
  · intro z k hk
    rw [deallocate_allocOf] at hk
    split at hk
    · cases hk
    · rename_i hzy
      obtain ⟨al, e1, e2⟩ := h.sframe z k hk
      refine ⟨al, deallocate_keep e1 fun hk' => hzy (h.sinj z y k hk hk'), e2⟩
  · intro z1 z2 k h1 h2
    rw [deallocate_allocOf] at h1 h2
    split at h1
    · cases h1
    · split at h2
      · cases h2
      · exact h.sinj z1 z2 k h1 h2
  · intro z k hk
    rw [deallocate_allocOf] at hk
    split at hk
    · cases hk
    · rename_i hzy
      obtain ⟨al, e1, e2⟩ := h.tframe z k hk
      refine ⟨al, deallocate_keep e1 fun hk' => hzy (h.tinj z y k hk hk'), e2⟩
  · intro z1 z2 k h1 h2
    rw [deallocate_allocOf] at h1 h2
    split at h1
    · cases h1
    · split at h2
      · cases h2
      · exact h.tinj z1 z2 k h1 h2
  · rw [deallocate_frame_length]; exact h.slen
  · rw [deallocate_frame_length]; exact h.tlen
  · intro k al hal
    obtain ⟨al0, e1, e2, _⟩ := (weaker_deallocate τ y).alloc k al hal
    rw [← e2]; exact h.tpos k al0 e1

/-- The target alone frees `x`. -/
theorem SRel2.deallocate_tgt_x {σ τ : State} (h : SRel2 P x D X0 A g σ τ) :
    SRel2 P x D X0 A g σ (deallocate τ x) := by
  refine ⟨h.mem.weaken (Weaker.refl _) (weaker_deallocate τ x), ?_, h.xS, ?_, ?_, ?_, h.sframe,
    h.sinj, ?_, ?_, h.slen, ?_, ?_⟩
  · intro z hz
    rw [deallocate_allocOf, ite_neg' hz]; exact h.frame z hz
  · intro kT hk
    rw [deallocate_allocOf, ite_pos' rfl] at hk; cases hk
  · intro kT kS bS bT alT hg hsx he hl
    obtain ⟨hnx, he'⟩ := deallocate_live he hl
    exact absurd (h.xown kT kS bS bT alT hg hsx he' hl) hnx
  · intro jS alS he hl hne
    obtain ⟨jT, alT, f1, f2, f3, f4⟩ := h.spre jS alS he hl hne
    refine ⟨jT, alT, f1, deallocate_keep f2 ?_, f3, f4⟩
    intro hx
    obtain ⟨kS, bS, bT, e1, e2⟩ := h.xT jT hx
    rw [e2] at f1; cases f1
    exact hne e1
  · intro z k hk
    rw [deallocate_allocOf] at hk
    split at hk
    · cases hk
    · rename_i hzx
      obtain ⟨al, e1, e2⟩ := h.tframe z k hk
      exact ⟨al, deallocate_keep e1 fun hk' => hzx (h.tinj z x k hk hk'), e2⟩
  · intro z1 z2 k h1 h2
    rw [deallocate_allocOf] at h1 h2
    split at h1
    · cases h1
    · split at h2
      · cases h2
      · exact h.tinj z1 z2 k h1 h2
  · rw [deallocate_frame_length]; exact h.tlen
  · intro k al hal
    obtain ⟨al0, e1, e2, _⟩ := (weaker_deallocate τ x).alloc k al hal
    rw [← e2]; exact h.tpos k al0 e1

theorem SRel2.frame_valid {σ τ : State} (h : SRel2 P x D X0 A g σ τ) {y k : Nat}
    (hk : σ.allocOf y = some k) : k < σ.mem.allocs.length := by
  obtain ⟨al, e, _⟩ := h.sframe y k hk
  exact getElem?_lt e

theorem SRel2.tframe_valid {σ τ : State} (h : SRel2 P x D X0 A g σ τ) {y k : Nat}
    (hk : τ.allocOf y = some k) : k < τ.mem.allocs.length := by
  obtain ⟨al, e, _⟩ := h.tframe y k hk
  exact getElem?_lt e

/-- Both programs allocate `y ≠ x`: the target at `aT`, the source at `aT + D`. -/
theorem SRel2.alloc_both {σ τ : State} (h : SRel2 P x D X0 A g σ τ) {y : Local} (hy : y ≠ x)
    (L : Layout) (aT : Nat) (hAD : A < D) (hXD : X0 + (P.layout x).size ≤ D + 1)
    (haT : 0 < aT)
    (hcT : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges aT L.size al.base al.size = true) :
    (∀ (k : Nat) (al : Alloc), σ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges (aT + D) L.size al.base al.size = true) ∧
    SRel2 P x D X0 A (gext g τ.mem.allocs.length (σ.mem.allocs.length, aT + D, aT))
      (allocState σ y L (aT + D)) (allocState τ y L aT) := by
  have hcS : ∀ (k : Nat) (al : Alloc), σ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges (aT + D) L.size al.base al.size = true := by
    intro k al he hl
    by_cases hkx : σ.allocOf x = some k
    · have hxl : x < P.locals.length := by
        rw [← h.slen]
        rcases Nat.lt_or_ge x σ.frame.length with h1 | h1
        · exact h1
        · rw [allocOf_eq_none_of_le h1] at hkx; cases hkx
      rcases h.xS hxl with hn | ⟨kx, alx, e1, e2, e3, e4⟩
      · rw [hn] at hkx; cases hkx
      rw [hkx] at e1; cases e1
      rw [he] at e2; cases e2
      simp only [disjointRanges, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      omega
    · obtain ⟨jT, alT, f1, f2, f3, f4⟩ := h.spre k al he hl hkx
      have hsz := h.mem.gsize jT k _ _ al alT f1 he f2
      rw [f4, hsz, disjointRanges_shift]
      exact hcT jT alT f2 f3
  have hm := h.mem.alloc_both y y L (aT + D) aT (by omega) hcS hcT
  have hext := GExt.gext h.mem (σ.mem.allocs.length, aT + D, aT)
  have hflen : σ.frame.length = τ.frame.length := h.slen.trans h.tlen.symm
  have hyx : ∀ n : Nat, ¬ (y = x ∧ y < n) := fun n hc => hy hc.1
  refine ⟨hcS, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [allocState_allocOf, allocState_allocOf, ← hflen]
    by_cases hc : y = z ∧ y < σ.frame.length
    · rw [ite_pos' hc, ite_pos' hc]
      exact Or.inr ⟨_, _, aT + D, aT, rfl, rfl, by simp [gext]⟩
    · rw [ite_neg' hc, ite_neg' hc]
      rcases h.frame z hz with h1 | ⟨kS, kT, bS, bT, h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨kS, kT, bS, bT, h1, h2, hext _ _ h3⟩
  · intro hx
    rcases h.xS hx with hn | ⟨kx, al, e1, e2, e3, e4⟩
    · left; rw [allocState_allocOf, ite_neg' (hyx _)]; exact hn
    refine Or.inr ⟨kx, al, ?_, ?_, e3, e4⟩
    · rw [allocState_allocOf, ite_neg' (hyx _)]; exact e1
    · rw [allocState_getElem?_old (getElem?_lt e2)]; exact e2
  · intro kT hk
    rw [allocState_allocOf, ite_neg' (hyx _)] at hk
    obtain ⟨kS, bS, bT, e1, e2⟩ := h.xT kT hk
    exact ⟨kS, bS, bT, by rw [allocState_allocOf, ite_neg' (hyx _)]; exact e1, hext _ _ e2⟩
  · intro kT kS bS bT alT hg hsx he hl
    rw [allocState_allocOf, ite_neg' (hyx _)] at hsx ⊢
    simp only [gext] at hg
    split at hg
    · cases hg; have := h.frame_valid hsx; omega
    · rw [allocState_getElem?_old (h.mem.gbound hg).2] at he
      exact h.xown kT kS bS bT alT hg hsx he hl
  · intro jS alS he hl hne
    rw [allocState_allocOf, ite_neg' (hyx _)] at hne
    rw [allocState_getElem?] at he
    split at he
    · obtain ⟨jT, alT, f1, f2, f3, f4⟩ := h.spre jS alS he hl hne
      exact ⟨jT, alT, hext _ _ f1, by rw [allocState_getElem?_old (getElem?_lt f2)]; exact f2, f3, f4⟩
    · split at he
      · cases he
        rename_i _ hj
        subst hj
        exact ⟨_, _, by simp [gext], allocState_getElem?_new _ _ _ _, rfl, rfl⟩
      · cases he
  · intro z k hk
    rw [allocState_allocOf] at hk
    split at hk
    · cases hk; exact ⟨_, allocState_getElem?_new _ _ _ _, rfl⟩
    · obtain ⟨al, e1, e2⟩ := h.sframe z k hk
      exact ⟨al, by rw [allocState_getElem?_old (getElem?_lt e1)]; exact e1, e2⟩
  · intro z1 z2 k h1 h2
    rw [allocState_allocOf] at h1 h2
    split at h1
    · rename_i hc1
      split at h2
      · rename_i hc2; exact hc1.1.symm.trans hc2.1
      · cases h1; have := h.frame_valid h2; omega
    · split at h2
      · cases h2; have := h.frame_valid h1; omega
      · exact h.sinj z1 z2 k h1 h2
  · intro z k hk
    rw [allocState_allocOf] at hk
    split at hk
    · cases hk; exact ⟨_, allocState_getElem?_new _ _ _ _, rfl⟩
    · obtain ⟨al, e1, e2⟩ := h.tframe z k hk
      exact ⟨al, by rw [allocState_getElem?_old (getElem?_lt e1)]; exact e1, e2⟩
  · intro z1 z2 k h1 h2
    rw [allocState_allocOf] at h1 h2
    split at h1
    · rename_i hc1
      split at h2
      · rename_i hc2; exact hc1.1.symm.trans hc2.1
      · cases h1; have := h.tframe_valid h2; omega
    · split at h2
      · cases h2; have := h.tframe_valid h1; omega
      · exact h.tinj z1 z2 k h1 h2
  · rw [allocState_frame_length]; exact h.slen
  · rw [allocState_frame_length]; exact h.tlen
  · intro k al hal
    rw [allocState_getElem?] at hal
    split at hal
    · exact h.tpos k al hal
    · split at hal
      · cases hal; exact haT
      · cases hal

/-- The target alone allocates `x` (a `storageLive x` step of `P`, after freeing `x`). -/
theorem SRel2.alloc_tgt_x {σ τ : State} (h : SRel2 P x D X0 A g σ τ)
    (hsx : x < P.locals.length → σ.allocOf x ≠ none)
    (hnone : τ.allocOf x = none) (aT : Nat) (haT : 0 < aT)
    (hcT : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges aT (P.layout x).size al.base al.size = true) :
    ∃ g', SRel2 P x D X0 A g' σ (allocState τ x (P.layout x) aT) := by
  by_cases hxl : x < P.locals.length
  · obtain ⟨kx, alx, e1, e2, e3, e4⟩ : ∃ (kx : Nat) (al : Alloc), σ.allocOf x = some kx ∧
        σ.mem.allocs[kx]? = some al ∧ al.base = X0 ∧ al.size = (P.layout x).size := by
      rcases h.xS hxl with hn | hx
      · exact absurd hn (hsx hxl)
      · exact hx
    have hfree : ∀ kT bS' bT' (alT : Alloc), g kT = some (kx, bS', bT') → τ.mem.allocs[kT]? = some alT →
        alT.live = true → False := by
      intro kT bS' bT' alT hg he hl
      have := h.xown kT kx bS' bT' alT hg e1 he hl
      rw [hnone] at this; cases this
    have hm := h.mem.alloc_tgt x (P.layout x) aT kx alx e2 e4 hfree hcT
    have hext := GExt.gext h.mem (kx, alx.base, aT)
    have hxs : x < τ.frame.length := h.tlen ▸ hxl
    refine ⟨_, hm, ?_, h.xS, ?_, ?_, ?_, h.sframe, h.sinj, ?_, ?_, h.slen, ?_, ?_⟩
    · intro z hz
      rw [allocState_allocOf, ite_neg' (fun hc => hz hc.1.symm)]
      rcases h.frame z hz with h1 | ⟨kS, kT, bS, bT, h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨kS, kT, bS, bT, h1, h2, hext _ _ h3⟩
    · intro kT hk
      rw [allocState_allocOf, ite_pos' ⟨rfl, hxs⟩] at hk
      cases hk
      exact ⟨kx, alx.base, aT, e1, by simp [gext]⟩
    · intro kT kS bS bT alT hg hsx he hl
      rw [allocState_allocOf]
      simp only [gext] at hg
      split at hg
      · rename_i hk; rw [ite_pos' ⟨rfl, hxs⟩, hk]
      · rw [allocState_getElem?_old (h.mem.gbound hg).2] at he
        have := h.xown kT kS bS bT alT hg hsx he hl
        rw [hnone] at this; cases this
    · intro jS alS he hl hne
      obtain ⟨jT, alT, f1, f2, f3, f4⟩ := h.spre jS alS he hl hne
      exact ⟨jT, alT, hext _ _ f1, by rw [allocState_getElem?_old (getElem?_lt f2)]; exact f2, f3, f4⟩
    · intro z k hk
      rw [allocState_allocOf] at hk
      split at hk
      · cases hk; exact ⟨_, allocState_getElem?_new _ _ _ _, rfl⟩
      · obtain ⟨al, f1, f2⟩ := h.tframe z k hk
        exact ⟨al, by rw [allocState_getElem?_old (getElem?_lt f1)]; exact f1, f2⟩
    · intro z1 z2 k h1 h2
      rw [allocState_allocOf] at h1 h2
      split at h1
      · rename_i hc1
        split at h2
        · rename_i hc2; exact hc1.1.symm.trans hc2.1
        · cases h1; have := h.tframe_valid h2; omega
      · split at h2
        · cases h2; have := h.tframe_valid h1; omega
        · exact h.tinj z1 z2 k h1 h2
    · rw [allocState_frame_length]; exact h.tlen
    · intro k al hal
      rw [allocState_getElem?] at hal
      split at hal
      · exact h.tpos k al hal
      · split at hal
        · cases hal; exact haT
        · cases hal
  · have hxl' : P.locals.length ≤ x := Nat.le_of_not_lt hxl
    have hsz : (P.layout x).size = 0 := by rw [layout_ge hxl']
    have hxs : τ.frame.length ≤ x := by rw [h.tlen]; exact hxl'
    have hnf : ∀ z, (allocState τ x (P.layout x) aT).allocOf z = τ.allocOf z := by
      intro z
      rw [allocState_allocOf, ite_neg' (show ¬ (x = z ∧ x < τ.frame.length) from
        fun hc => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hc.2 hxs))]
    refine ⟨g, h.mem.alloc_tgt_zero x (P.layout x) aT hsz, ?_, h.xS, ?_, ?_, ?_, h.sframe,
      h.sinj, ?_, ?_, h.slen, ?_, ?_⟩
    · intro z hz; rw [hnf]; exact h.frame z hz
    · intro kT hk; rw [hnf] at hk; exact h.xT kT hk
    · intro kT kS bS bT alT hg hsx he hl
      rw [hnf]
      rw [allocState_getElem?_old (h.mem.gbound hg).2] at he
      exact h.xown kT kS bS bT alT hg hsx he hl
    · intro jS alS he hl hne
      obtain ⟨jT, alT, f1, f2, f3, f4⟩ := h.spre jS alS he hl hne
      exact ⟨jT, alT, f1, by rw [allocState_getElem?_old (getElem?_lt f2)]; exact f2, f3, f4⟩
    · intro z k hk
      rw [hnf] at hk
      obtain ⟨al, f1, f2⟩ := h.tframe z k hk
      exact ⟨al, by rw [allocState_getElem?_old (getElem?_lt f1)]; exact f1, f2⟩
    · intro z1 z2 k h1 h2; rw [hnf] at h1 h2; exact h.tinj z1 z2 k h1 h2
    · rw [allocState_frame_length]; exact h.tlen
    · intro k al hal
      rw [allocState_getElem?] at hal
      split at hal
      · exact h.tpos k al hal
      · split at hal
        · cases hal; exact haT
        · cases hal

/-- The source alone allocates `x < P.locals.length` at `X0` (at entry). -/
theorem SRel2.alloc_src_x {σ τ : State} (h : SRel2 P x D X0 A g σ τ) (hxl : x < P.locals.length)
    (hsx : σ.allocOf x = none) (htx : τ.allocOf x = none) (hAX : A < X0)
    (hXD : X0 + (P.layout x).size ≤ D + 1) :
    (∀ (k : Nat) (al : Alloc), σ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges X0 (P.layout x).size al.base al.size = true) ∧
    SRel2 P x D X0 A g (allocState σ x (P.layout x) X0) τ := by
  have hcS : ∀ (k : Nat) (al : Alloc), σ.mem.allocs[k]? = some al → al.live = true →
      disjointRanges X0 (P.layout x).size al.base al.size = true := by
    intro k al he hl
    obtain ⟨jT, alT, f1, f2, f3, f4⟩ := h.spre k al he hl (by rw [hsx]; simp)
    have := h.tpos jT alT f2
    simp only [disjointRanges, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    omega
  have hxs : x < σ.frame.length := h.slen ▸ hxl
  refine ⟨hcS, h.mem.alloc_src x (P.layout x) X0 hAX hcS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.tframe,
    h.tinj, ?_, h.tlen, h.tpos⟩
  · intro z hz
    rw [allocState_allocOf, ite_neg' (fun hc => hz hc.1.symm)]; exact h.frame z hz
  · intro _
    refine Or.inr ⟨_, _, ?_, allocState_getElem?_new _ _ _ _, rfl, rfl⟩
    rw [allocState_allocOf, ite_pos' ⟨rfl, hxs⟩]
  · intro kT hk; rw [htx] at hk; cases hk
  · intro kT kS bS bT alT hg hs he hl
    rw [allocState_allocOf, ite_pos' ⟨rfl, hxs⟩] at hs
    cases hs
    have := (h.mem.gbound hg).1; omega
  · intro jS alS he hl hne
    rw [allocState_allocOf, ite_pos' ⟨rfl, hxs⟩] at hne
    rw [allocState_getElem?] at he
    split at he
    · exact h.spre jS alS he hl (by rw [hsx]; simp)
    · split at he
      · rename_i _ hj; exact absurd (congrArg some hj.symm) hne
      · cases he
  · intro z k hk
    rw [allocState_allocOf] at hk
    split at hk
    · cases hk; exact ⟨_, allocState_getElem?_new _ _ _ _, rfl⟩
    · obtain ⟨al, e1, e2⟩ := h.sframe z k hk
      exact ⟨al, by rw [allocState_getElem?_old (getElem?_lt e1)]; exact e1, e2⟩
  · intro z1 z2 k h1 h2
    rw [allocState_allocOf] at h1 h2
    split at h1
    · rename_i hc1
      split at h2
      · rename_i hc2; exact hc1.1.symm.trans hc2.1
      · cases h1; have := h.frame_valid h2; omega
    · split at h2
      · cases h2; have := h.frame_valid h1; omega
      · exact h.sinj z1 z2 k h1 h2
  · rw [allocState_frame_length]; exact h.slen

end SRel2

end Toy.PlaceEval
