import ToyParMove.Basic

set_option linter.unusedSectionVars false

namespace Toy.ParMove

section Algorithm
variable {Loc : Type} [DecidableEq Loc]

/-- `renameSrc d t P` replaces the source `d` by `t` in every move of `P` (destinations are
untouched). Used after the old value of `d` has been saved in `t`. -/
def renameSrc (d t : Loc) (P : List (Loc × Loc)) : List (Loc × Loc) :=
  P.map fun m => (m.1, if m.2 = d then t else m.2)

/-- A pending move is *ready* when no pending move reads its destination. -/
def isReady (P : List (Loc × Loc)) (m : Loc × Loc) : Bool := decide (m.1 ∉ srcs P)

/-- Main loop of the sequentialization: emit the first ready move if there is one; otherwise
(every pending destination is still read) save the destination `d` of the first pending move
`(d, s)` in `tmp`, emit `d := s`, and redirect the pending readers of `d` to `tmp`. -/
def seqLoop (tmp : Loc) : List (Loc × Loc) → List (Loc × Loc)
  | [] => []
  | m :: rest =>
    match _h : (m :: rest).find? (isReady (m :: rest)) with
    | some r => r :: seqLoop tmp ((m :: rest).erase r)
    | none => (tmp, m.1) :: m :: seqLoop tmp (renameSrc m.1 tmp rest)
termination_by P => P.length
decreasing_by
  · have hr := List.mem_of_find?_eq_some _h
    rw [List.length_erase_of_mem hr]
    simp
  · simp [renameSrc]

/-- **Sequentialization of a parallel move** using scratch location `tmp`: drop self-moves,
then run `seqLoop`. -/
def sequentialize (tmp : Loc) (M : List (Loc × Loc)) : List (Loc × Loc) :=
  seqLoop tmp (M.filter fun m => decide (m.1 ≠ m.2))

end Algorithm

/-! ### Lemmas -/

section Lemmas
variable {Loc V : Type} [DecidableEq Loc]

theorem functional_of_subset {P Q : List (Loc × Loc)} (hF : Functional P) (h : Q ⊆ P) :
    Functional Q := fun d s₁ s₂ h₁ h₂ => hF d s₁ s₂ (h h₁) (h h₂)

theorem dsts_subset_of_subset {P Q : List (Loc × Loc)} (h : Q ⊆ P) : dsts Q ⊆ dsts P := by
  intro x hx
  obtain ⟨s, hs⟩ := mem_dsts.1 hx
  exact mem_dsts.2 ⟨s, h hs⟩

theorem srcs_subset_of_subset {P Q : List (Loc × Loc)} (h : Q ⊆ P) : srcs Q ⊆ srcs P := by
  intro x hx
  obtain ⟨d, hd⟩ := mem_srcs.1 hx
  exact mem_srcs.2 ⟨d, h hd⟩

theorem dsts_renameSrc (d t : Loc) (P : List (Loc × Loc)) : dsts (renameSrc d t P) = dsts P := by
  simp [dsts, renameSrc, List.map_map, Function.comp_def]

theorem mem_renameSrc {d t x y : Loc} {P : List (Loc × Loc)} :
    (x, y) ∈ renameSrc d t P ↔ ∃ s, (x, s) ∈ P ∧ (if s = d then t else s) = y := by
  simp only [renameSrc, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩
    exact ⟨b, h, rfl⟩
  · rintro ⟨s, h, rfl⟩
    exact ⟨(x, s), h, rfl, rfl⟩

theorem functional_renameSrc {d t : Loc} {P : List (Loc × Loc)} (hF : Functional P) :
    Functional (renameSrc d t P) := by
  intro x y₁ y₂ h₁ h₂
  obtain ⟨s₁, hs₁, rfl⟩ := mem_renameSrc.1 h₁
  obtain ⟨s₂, hs₂, rfl⟩ := mem_renameSrc.1 h₂
  rw [hF x s₁ s₂ hs₁ hs₂]

theorem nodup_dsts_of_functional_of_nodup {Q : List (Loc × Loc)} (hF : Functional Q)
    (hQ : Q.Nodup) : (dsts Q).Nodup := by
  induction Q with
  | nil => simp [dsts]
  | cons m Q ih =>
    have hQ' := List.nodup_cons.1 hQ
    rw [dsts_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih (functional_of_subset hF (List.subset_cons_self _ _)) hQ'.2⟩
    obtain ⟨s, hs⟩ := mem_dsts.1 h
    have := hF m.1 m.2 s (by simp) (List.mem_cons_of_mem _ hs)
    exact hQ'.1 (by rw [← this] at hs; exact hs)

/-- In a "stuck" well-formed pending set (every destination is still read), every source is a
destination. Pigeonhole on the equal-length lists of destinations and sources. -/
theorem srcs_subset_dsts_of_stuck_of_nodup {Q : List (Loc × Loc)} (hD : (dsts Q).Nodup)
    (hstuck : ∀ m ∈ Q, m.1 ∈ srcs Q) : ∀ x ∈ srcs Q, x ∈ dsts Q := by
  intro x hx
  apply Classical.byContradiction
  intro hxd
  have hsub : x :: dsts Q ⊆ srcs Q := by
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · obtain ⟨s, hs⟩ := mem_dsts.1 hy
      exact hstuck (y, s) hs
  have := length_le_of_nodup_of_subset (List.nodup_cons.2 ⟨hxd, hD⟩) hsub
  simp only [List.length_cons, length_dsts, length_srcs] at this
  omega

/-- The stuck-state lemma for functional pending sets. -/
theorem srcs_subset_dsts_of_stuck {P : List (Loc × Loc)} (hF : Functional P)
    (hstuck : ∀ m ∈ P, m.1 ∈ srcs P) : ∀ x ∈ srcs P, x ∈ dsts P := by
  have hmem : ∀ m, m ∈ dedupL P ↔ m ∈ P := fun _ => mem_dedupL
  have hsrc : ∀ x, x ∈ srcs (dedupL P) ↔ x ∈ srcs P := by
    intro x; simp only [mem_srcs, hmem]
  have hdst : ∀ x, x ∈ dsts (dedupL P) ↔ x ∈ dsts P := by
    intro x; simp only [mem_dsts, hmem]
  have hFQ : Functional (dedupL P) :=
    functional_of_subset hF (fun m hm => (hmem m).1 hm)
  intro x hx
  exact (hdst x).1 (srcs_subset_dsts_of_stuck_of_nodup
    (nodup_dsts_of_functional_of_nodup hFQ (nodup_dedupL P))
    (fun m hm => (hsrc _).2 (hstuck m ((hmem m).1 hm))) x ((hsrc x).2 hx))

/-- Emitting a ready move first is sound. -/
theorem pmove_erase_ready {P : List (Loc × Loc)} (hF : Functional P) {r : Loc × Loc}
    (hr : r ∈ P) (hready : r.1 ∉ srcs P) (τ : Loc → V) :
    pmove (P.erase r) (seqStep τ r) = pmove P τ := by
  funext l
  have hF' : Functional (P.erase r) := functional_of_subset hF (List.erase_subset)
  by_cases hl : l ∈ dsts (P.erase r)
  · obtain ⟨s, hs⟩ := mem_dsts.1 hl
    have hsP : (l, s) ∈ P := List.mem_of_mem_erase hs
    rw [pmove_of_mem hF' hs, pmove_of_mem hF hsP]
    have hne : s ≠ r.1 := fun e => hready (e ▸ mem_srcs.2 ⟨l, hsP⟩)
    simp [seqStep, upd, hne]
  · rw [pmove_of_not_mem_dsts hl]
    by_cases hlr : l = r.1
    · subst hlr
      rw [pmove_of_mem hF (show (r.1, r.2) ∈ P from hr)]
      simp [seqStep, upd]
    · have hlP : l ∉ dsts P := by
        intro h
        obtain ⟨s, hs⟩ := mem_dsts.1 h
        have hne : (l, s) ≠ r := fun e => hlr (by rw [← e])
        exact hl (mem_dsts.2 ⟨s, (List.mem_erase_of_ne hne).2 hs⟩)
      rw [pmove_of_not_mem_dsts hlP]
      simp [seqStep, upd, hlr]

/-- Breaking a cycle is sound when the scratch location is neither a pending destination nor a
pending source: save `d` in `tmp`, emit `d := s`, and redirect readers of `d` to `tmp`. -/
theorem pmove_break_step {d s tmp : Loc} {rest : List (Loc × Loc)}
    (hF : Functional ((d, s) :: rest)) (hd : tmp ∉ dsts ((d, s) :: rest))
    (hs : tmp ∉ srcs ((d, s) :: rest)) (τ : Loc → V) {l : Loc} (hl : l ≠ tmp) :
    pmove (renameSrc d tmp rest) (seqStep (seqStep τ (tmp, d)) (d, s)) l =
      pmove ((d, s) :: rest) τ l := by
  have hdt : d ≠ tmp := fun e => hd (by simp [e])
  have hst : s ≠ tmp := fun e => hs (by simp [e])
  have hτ1s : seqStep τ (tmp, d) s = τ s := by simp [seqStep, upd, hst]
  by_cases hl' : l ∈ dsts (renameSrc d tmp rest)
  · obtain ⟨y, hy⟩ := mem_dsts.1 hl'
    obtain ⟨s', hs', hy'⟩ := mem_renameSrc.1 hy
    rw [pmove_of_mem (functional_renameSrc (functional_of_subset hF
      (List.subset_cons_self _ _))) hy, pmove_of_mem hF (List.mem_cons_of_mem _ hs')]
    by_cases hsd : s' = d
    · simp only [hsd, ite_true] at hy'
      subst hy'; subst hsd
      simp [seqStep, upd, Ne.symm hdt]
    · simp only [hsd, ite_false] at hy'
      subst hy'
      have hs't : s' ≠ tmp := fun e => hs (by simp [srcs]; exact Or.inr ⟨l, e ▸ hs'⟩)
      simp [seqStep, upd, hsd, hs't]
  · rw [dsts_renameSrc] at hl'
    rw [pmove_of_not_mem_dsts (by rw [dsts_renameSrc]; exact hl')]
    by_cases hld : l = d
    · subst hld
      rw [pmove_of_mem hF (List.mem_cons_self ..)]
      simp only [seqStep, upd_same]
      exact hτ1s
    · rw [pmove_of_not_mem_dsts (by simp [hld, hl'])]
      simp [seqStep, upd, hld, hl]

theorem seqLoop_cons_of_find_some {tmp : Loc} {m r : Loc × Loc} {rest : List (Loc × Loc)}
    (h : (m :: rest).find? (isReady (m :: rest)) = some r) :
    seqLoop tmp (m :: rest) = r :: seqLoop tmp ((m :: rest).erase r) := by
  rw [seqLoop]; split <;> simp_all

theorem seqLoop_cons_of_find_none {tmp : Loc} {m : Loc × Loc} {rest : List (Loc × Loc)}
    (h : (m :: rest).find? (isReady (m :: rest)) = none) :
    seqLoop tmp (m :: rest) = (tmp, m.1) :: m :: seqLoop tmp (renameSrc m.1 tmp rest) := by
  rw [seqLoop]; split <;> simp_all

/-- **Main loop invariant.** For a functional pending set in which `tmp` is not both a
destination and a source, the emitted sequence agrees with the parallel move off `tmp`. -/
theorem seqLoop_agrees_off_tmp (tmp : Loc) :
    ∀ (n : Nat) (P : List (Loc × Loc)), P.length = n → ∀ (τ : Loc → V),
      Functional P → (tmp ∉ dsts P ∨ tmp ∉ srcs P) →
      ∀ l, l ≠ tmp → runSeq (seqLoop tmp P) τ l = pmove P τ l := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro P hlen τ hF htmp l hl
    match P, hlen, hF, htmp with
    | [], _, _, _ => simp [seqLoop, pmove, lookupSrc]
    | m :: rest, hlen, hF, htmp =>
      cases hfind : (m :: rest).find? (isReady (m :: rest)) with
      | some r =>
        rw [seqLoop_cons_of_find_some hfind, runSeq_cons]
        have hr := List.mem_of_find?_eq_some hfind
        have hready : r.1 ∉ srcs (m :: rest) := by
          have := List.find?_some hfind
          simpa [isReady] using this
        have hsub : (m :: rest).erase r ⊆ m :: rest := List.erase_subset
        have hlen' : ((m :: rest).erase r).length < n := by
          rw [List.length_erase_of_mem hr, ← hlen]; simp
        rw [ih _ hlen' _ rfl (seqStep τ r) (functional_of_subset hF hsub)
          (htmp.imp (fun h h' => h (dsts_subset_of_subset hsub h'))
            (fun h h' => h (srcs_subset_of_subset hsub h'))) l hl]
        exact congrFun (pmove_erase_ready hF hr hready τ) l
      | none =>
        rw [seqLoop_cons_of_find_none hfind, runSeq_cons, runSeq_cons]
        have hstuck : ∀ x ∈ m :: rest, x.1 ∈ srcs (m :: rest) := by
          intro x hx
          have := List.find?_eq_none.1 hfind x hx
          unfold isReady at this
          exact Classical.byContradiction fun h => this (decide_eq_true h)
        have hsd := srcs_subset_dsts_of_stuck hF hstuck
        have hd : tmp ∉ dsts (m :: rest) := by
          rcases htmp with h | h
          · exact h
          · intro ht
            obtain ⟨s, hs⟩ := mem_dsts.1 ht
            exact h (hstuck (tmp, s) hs)
        have hs : tmp ∉ srcs (m :: rest) := fun h => hd (hsd tmp h)
        obtain ⟨d, s⟩ := m
        have hlen' : (renameSrc d tmp rest).length < n := by
          rw [← hlen]; simp [renameSrc]
        have hFr : Functional (renameSrc d tmp rest) :=
          functional_renameSrc (functional_of_subset hF (List.subset_cons_self _ _))
        have hdr : tmp ∉ dsts (renameSrc d tmp rest) := by
          rw [dsts_renameSrc]; intro h; exact hd (by simp [h])
        rw [ih _ hlen' _ rfl _ hFr (Or.inl hdr) l hl]
        exact pmove_break_step hF hd hs τ hl

theorem pmove_filter_nonself {M : List (Loc × Loc)} (hF : Functional M) (σ : Loc → V) :
    pmove (M.filter fun m => decide (m.1 ≠ m.2)) σ = pmove M σ := by
  funext l
  have hsub : (M.filter fun m => decide (m.1 ≠ m.2)) ⊆ M := List.filter_sublist.subset
  by_cases hl : l ∈ dsts (M.filter fun m => decide (m.1 ≠ m.2))
  · obtain ⟨s, hs⟩ := mem_dsts.1 hl
    rw [pmove_of_mem (functional_of_subset hF hsub) hs, pmove_of_mem hF (hsub hs)]
  · rw [pmove_of_not_mem_dsts hl]
    by_cases hlM : l ∈ dsts M
    · obtain ⟨s, hs⟩ := mem_dsts.1 hlM
      rw [pmove_of_mem hF hs]
      have : l = s := by
        apply Classical.byContradiction
        intro hne
        exact hl (mem_dsts.2 ⟨s, List.mem_filter.2 ⟨hs, by simpa using hne⟩⟩)
      rw [this]
    · rw [pmove_of_not_mem_dsts hlM]

end Lemmas

/-! ### Soundness of `sequentialize` -/

section Soundness
variable {Loc V : Type} [DecidableEq Loc]

/-- **Sequentialization soundness.** For a functional parallel move `M` (in particular any
well-formed one) and a scratch location `tmp` that is not simultaneously a destination and a
source of `M`, running `sequentialize tmp M` from any store `σ` yields, at every location other
than `tmp`, the value prescribed by the parallel move. -/
theorem sequentialize_agrees_off_tmp {M : List (Loc × Loc)} {tmp : Loc} (hF : Functional M)
    (htmp : tmp ∉ dsts M ∨ tmp ∉ srcs M) (σ : Loc → V) :
    ∀ l, l ≠ tmp → runSeq (sequentialize tmp M) σ l = pmove M σ l := by
  intro l hl
  have hsub : (M.filter fun m => decide (m.1 ≠ m.2)) ⊆ M := List.filter_sublist.subset
  unfold sequentialize
  rw [seqLoop_agrees_off_tmp tmp _ _ rfl σ (functional_of_subset hF hsub)
    (htmp.imp (fun h h' => h (dsts_subset_of_subset hsub h'))
      (fun h h' => h (srcs_subset_of_subset hsub h'))) l hl]
  exact congrFun (pmove_filter_nonself hF σ) l

/-- Corollary in the customary form: well-formed `M` and a scratch location that occurs in `M`
neither as a destination nor as a source. -/
theorem sequentialize_agrees_off_tmp_of_wellFormed_of_fresh {M : List (Loc × Loc)} {tmp : Loc}
    (hM : WellFormed M) (hd : tmp ∉ dsts M) (_hs : tmp ∉ srcs M) (σ : Loc → V) :
    ∀ l, l ≠ tmp → runSeq (sequentialize tmp M) σ l = pmove M σ l :=
  sequentialize_agrees_off_tmp (functional_of_wellFormed hM) (Or.inl hd) σ

end Soundness

/-! ### Definition examples (`isReady`, `sequentialize`) -/

/-- Positive example (`isReady`): no pending move reads location `3`. -/
theorem isReady_example : isReady [((1 : Nat), (2 : Nat)), (3, 0)] (3, 0) = true := by decide

/-- Negative example (`isReady`): in a pending 2-cycle every destination is still read. -/
theorem not_isReady_example : isReady [((1 : Nat), (2 : Nat)), (2, 1)] (1, 2) = false := by
  decide

/-- Positive example (`sequentialize`): a 2-cycle is broken through the scratch location `9`. -/
theorem sequentialize_swap_example :
    sequentialize (9 : Nat) [(1, 2), (2, 1)] = [(9, 1), (1, 2), (2, 9)] := by decide +kernel

/-- Positive example (`sequentialize`): self-moves are dropped; an acyclic chain is emitted
reader-first without touching the scratch location. -/
theorem sequentialize_chain_example :
    sequentialize (9 : Nat) [(0, 0), (1, 0), (2, 1)] = [(2, 1), (1, 0)] := by decide +kernel

/-- Non-claim witness (`sequentialize` does not deduplicate): for the functional but not
well-formed input `[(0,1),(0,1),(1,0)]` the emitted sequence contains the move `0 := 1` twice. -/
theorem sequentialize_emits_duplicates_example :
    sequentialize (9 : Nat) [(0, 1), (0, 1), (1, 0)] = [(9, 0), (0, 1), (0, 1), (1, 9)] := by
  decide +kernel

end Toy.ParMove
