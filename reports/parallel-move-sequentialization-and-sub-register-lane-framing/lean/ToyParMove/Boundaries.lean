import ToyParMove.Necessity
import ToyParMove.Swaps
import ToyParMove.Lanes

/-!
Boundary theorems that delimit three results of the package more precisely.

* A move list that contains all moves of a cycle (possibly among other moves) has no
  topological order, whatever else it contains (`not_topological_of_contains_cycleMoves`).
* Swap sequences only permute the values already present in the store, so they cannot use a
  location outside the cycle as a backup. Hence the swap lower bound for a cycle needs
  injectivity of the store only on the cycle locations
  (`cycle_length_sub_one_le_of_injOn_of_runSwaps`), unlike the plain-move bounds, where an
  untouched location holding a copy of a cycle value can serve as a backup.
* The preserve-upper lane write satisfies PutGet exactly when the lane is empty or fits in the
  register (`putLane_putGet_iff_wid_zero_or_fits`).
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

section CycleContainment
variable {Loc : Type} [DecidableEq Loc]

/-- **A list containing a cycle has no topological order.** If every move of the duplicate-free
cycle `cycleMoves ls` (with `2 ≤ ls.length`) occurs in `M`, then no reordering `ms` of `M` is
topological, whatever other moves `M` contains. -/
theorem not_topological_of_contains_cycleMoves {ls : List Loc} {M ms : List (Loc × Loc)}
    (hn : ls.Nodup) (hk : 2 ≤ ls.length)
    (hsub : ∀ m ∈ cycleMoves ls, m ∈ M) (hp : ms.Perm M) :
    ¬ Topological ms := by
  refine not_topological_of_dsts_read (C := cycleMoves ls) ?_
    (fun m hm => hp.mem_iff.2 (hsub m hm)) ?_
  · intro e
    have := congrArg List.length (dsts_cycleMoves ls)
    rw [e] at this; simp at this; omega
  · intro m hm
    have hm1 : m.1 ∈ ls := by rw [← dsts_cycleMoves ls]; exact mem_dsts.2 ⟨m.2, hm⟩
    obtain ⟨d, hd⟩ := mem_srcs.1 (mem_srcs_cycleMoves hm1)
    refine ⟨(d, m.1), hd, fun e => ?_, rfl⟩
    exact cycleMoves_no_self hn hk m hm (congrArg Prod.snd e)

end CycleContainment

section SwapLocalInjectivity
variable {Loc V : Type} [DecidableEq Loc]

private theorem bnd_swapStore_involutive (σ : Loc → V) (a b : Loc) :
    swapStore (swapStore σ a b) a b = σ := by
  funext l
  by_cases hab : a = b
  · subst hab
    by_cases hl : l = a <;> simp [swapStore, hl]
  · by_cases ha : l = a
    · subst ha; simp [swapStore, Ne.symm hab]
    · by_cases hb : l = b
      · subst hb; simp [swapStore, ha]
      · simp [swapStore, ha, hb]

private theorem bnd_runSwaps_append (xs ys : List (Loc × Loc)) (τ : Loc → V) :
    runSwaps (xs ++ ys) τ = runSwaps ys (runSwaps xs τ) := by
  simp [runSwaps, List.foldl_append]

private theorem bnd_runSwaps_reverse_left_inv :
    ∀ (ss : List (Loc × Loc)) (σ : Loc → V), runSwaps ss.reverse (runSwaps ss σ) = σ
  | [], _ => rfl
  | p :: ss, σ => by
    simp only [List.reverse_cons, runSwaps_cons]
    rw [bnd_runSwaps_append, bnd_runSwaps_reverse_left_inv ss (swapStore σ p.1 p.2)]
    exact bnd_swapStore_involutive σ p.1 p.2

private theorem bnd_runSwaps_outside :
    ∀ (ss : List (Loc × Loc)) (σ : Loc → V) {l : Loc},
      (∀ p ∈ ss, l ≠ p.1 ∧ l ≠ p.2) → runSwaps ss σ l = σ l
  | [], _, _, _ => rfl
  | p :: ss, σ, l, h => by
    have hp := h p (List.mem_cons_self ..)
    rw [runSwaps_cons, bnd_runSwaps_outside ss _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp [swapStore, hp.1, hp.2]

private theorem bnd_nodup_map_of_left_inv {α : Type} {L : List α} (hn : L.Nodup)
    (f g : α → α) (hinv : ∀ x, g (f x) = x) : (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have hn' := List.nodup_cons.1 hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hn'.2⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    have hab : b = a := by have := congrArg g hfb; rwa [hinv, hinv] at this
    exact hn'.1 (hab ▸ hb)

private theorem bnd_getLastD_not_mem_srcs_chain :
    ∀ (h : Loc) (ys : List Loc), (h :: ys).Nodup → ys.getLastD h ∉ srcs (chain h ys)
  | _, [], _ => by simp [chain]
  | h, y :: ys, hn => by
    have hn' := List.nodup_cons.1 hn
    rw [List.getLastD_cons]
    simp only [chain, srcs_cons, List.mem_cons, not_or]
    refine ⟨?_, bnd_getLastD_not_mem_srcs_chain y ys hn'.2⟩
    intro e
    exact hn'.1 (e ▸ List.getLastD_mem_cons)

private theorem bnd_eq_of_same_src_chain :
    ∀ (h : Loc) (ys : List Loc), (h :: ys).Nodup → ∀ {d₁ d₂ s : Loc},
      (d₁, s) ∈ chain h ys → (d₂, s) ∈ chain h ys → d₁ = d₂
  | _, [], _, _, _, _, h₁, _ => by simp [chain] at h₁
  | h, y :: ys, hn, d₁, d₂, s, h₁, h₂ => by
    have hn' := List.nodup_cons.1 hn
    simp only [chain, List.mem_cons, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with ⟨h1d, h1s⟩ | h₁ <;> rcases h₂ with ⟨h2d, h2s⟩ | h₂
    · exact h1d.trans h2d.symm
    · rw [h1s] at h₂
      exact absurd (srcs_chain_subset y ys (mem_srcs.2 ⟨d₂, h₂⟩)) hn'.1
    · rw [h2s] at h₁
      exact absurd (srcs_chain_subset y ys (mem_srcs.2 ⟨d₁, h₁⟩)) hn'.1
    · exact bnd_eq_of_same_src_chain y ys hn'.2 h₁ h₂

private theorem bnd_eq_of_same_src_cycleMoves {ls : List Loc}
    (hn : ls.Nodup) {d₁ d₂ s : Loc}
    (h₁ : (d₁, s) ∈ cycleMoves ls) (h₂ : (d₂, s) ∈ cycleMoves ls) : d₁ = d₂ := by
  cases ls with
  | nil => simp [cycleMoves] at h₁
  | cons l₀ rest =>
    simp only [cycleMoves, List.mem_cons, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with ⟨h1d, h1s⟩ | h₁ <;> rcases h₂ with ⟨h2d, h2s⟩ | h₂
    · exact h1d.trans h2d.symm
    · rw [h1s] at h₂
      exact absurd (mem_srcs.2 ⟨d₂, h₂⟩) (bnd_getLastD_not_mem_srcs_chain l₀ rest hn)
    · rw [h2s] at h₁
      exact absurd (mem_srcs.2 ⟨d₁, h₁⟩) (bnd_getLastD_not_mem_srcs_chain l₀ rest hn)
    · exact bnd_eq_of_same_src_chain l₀ rest hn h₁ h₂

/-- **Swap lower bound under injectivity on the cycle only.** If a list of swaps realizes the
duplicate-free cycle `cycleMoves ls` exactly from a store `σ` that is injective on the cycle
locations (not necessarily on the whole location type), it has at least `ls.length - 1` swaps.
Swaps only permute the values already present, so no location outside the cycle can act as a
backup; compare the plain-move bounds, which need global injectivity
(`cycle_lower_bound_needs_global_injectivity`). -/
theorem cycle_length_sub_one_le_of_injOn_of_runSwaps
    {ls : List Loc} {σ : Loc → V} {ss : List (Loc × Loc)}
    (hn : ls.Nodup)
    (hinj : ∀ x ∈ ls, ∀ y ∈ ls, σ x = σ y → x = y)
    (hreal : runSwaps ss σ = pmove (cycleMoves ls) σ) :
    ls.length - 1 ≤ ss.length := by
  cases ls with
  | nil => simp
  | cons l₀ rest =>
    have hF := functional_of_wellFormed (wellFormed_cycleMoves hn)
    let R := ufRun ss (id : Loc → Loc)
    let π := runSwaps ss (id : Loc → Loc)
    let π_inv := runSwaps ss.reverse (id : Loc → Loc)
    have hrinv : ∀ x, π (π_inv x) = x := by
      intro x
      have e1 := congrFun (runSwaps_comp (runSwaps ss id) ss.reverse id) x
      have e2 := congrFun (bnd_runSwaps_reverse_left_inv ss id) x
      simp only [Function.comp_id, Function.comp] at e1
      exact e1.symm.trans e2
    have hRπ : ∀ x, R (π x) = R x := ufRun_invariant ss id id (fun _ => rfl)
    have hσπ : ∀ x, σ (π x) = pmove (cycleMoves (l₀ :: rest)) σ x := by
      intro x
      have e := congrFun (runSwaps_comp σ ss id) x
      simp only [Function.comp_id, Function.comp] at e
      exact e.symm.trans (congrFun hreal x)
    let S := dedupL ((l₀ :: rest) ++ ss.map Prod.fst ++ ss.map Prod.snd)
    have hSnodup : S.Nodup := nodup_dedupL _
    have hmemS_ls : ∀ x ∈ l₀ :: rest, x ∈ S := fun x hx =>
      mem_dedupL.2 (List.mem_append_left _ (List.mem_append_left _ hx))
    have hπ_out : ∀ x, x ∉ S → π x = x := by
      intro x hx
      apply bnd_runSwaps_outside
      intro p hp
      refine ⟨fun e => hx (mem_dedupL.2 (List.mem_append_left _ (List.mem_append_right _ ?_))),
              fun e => hx (mem_dedupL.2 (List.mem_append_right _ ?_))⟩
      · exact List.mem_map.2 ⟨p, hp, e.symm⟩
      · exact List.mem_map.2 ⟨p, hp, e.symm⟩
    have hπinv_memS : ∀ y ∈ S, π_inv y ∈ S := by
      intro y hy
      apply Classical.byContradiction
      intro hnot
      have hfix : π (π_inv y) = π_inv y := hπ_out (π_inv y) hnot
      rw [hrinv] at hfix
      exact hnot (hfix ▸ hy)
    have hedge : ∀ m ∈ cycleMoves (l₀ :: rest), R m.1 = R m.2 := by
      intro m hm
      apply Classical.byContradiction
      intro hne
      letI : DecidablePred (fun x => R x = R m.2 ∧ σ x = σ m.2) :=
        fun _ => Classical.propDecidable _
      letI : DecidablePred (fun x => R x = R m.2 ∧ σ (π x) = σ m.2) :=
        fun _ => Classical.propDecidable _
      let A := S.filter (fun x => decide (R x = R m.2 ∧ σ x = σ m.2))
      let B := S.filter (fun x => decide (R x = R m.2 ∧ σ (π x) = σ m.2))
      have hAnod : A.Nodup := hSnodup.sublist List.filter_sublist
      have hBnod : B.Nodup := hSnodup.sublist List.filter_sublist
      have hm2_ls : m.2 ∈ l₀ :: rest :=
        srcs_cycleMoves_subset (l₀ :: rest) (mem_srcs.2 ⟨m.1, hm⟩)
      have hm2_A : m.2 ∈ A := List.mem_filter.2 ⟨hmemS_ls m.2 hm2_ls, by simp⟩
      have hB_not_ls : ∀ x ∈ B, x ∉ l₀ :: rest := by
        intro x hxB hxls
        have hxB' : R x = R m.2 ∧ σ (π x) = σ m.2 := by
          simpa using (List.mem_filter.1 hxB).2
        have hxdst : x ∈ dsts (cycleMoves (l₀ :: rest)) := by rwa [dsts_cycleMoves]
        obtain ⟨s, hxs⟩ := mem_dsts.1 hxdst
        have hs_ls : s ∈ l₀ :: rest :=
          srcs_cycleMoves_subset (l₀ :: rest) (mem_srcs.2 ⟨x, hxs⟩)
        have hσs : σ s = σ m.2 := by
          have := hxB'.2
          rwa [hσπ x, pmove_of_mem hF hxs] at this
        have hsm : s = m.2 := hinj s hs_ls m.2 hm2_ls hσs
        have hxm1 : x = m.1 := bnd_eq_of_same_src_cycleMoves hn (hsm ▸ hxs) hm
        exact hne (hxm1 ▸ hxB'.1)
      have hm2_not_B : m.2 ∉ B := fun hb => hB_not_ls m.2 hb hm2_ls
      have hB_sub_A : m.2 :: B ⊆ A := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hxB
        · exact hm2_A
        · have hxS := (List.mem_filter.1 hxB).1
          have hxB' : R x = R m.2 ∧ σ (π x) = σ m.2 := by
            simpa using (List.mem_filter.1 hxB).2
          have hnotls : x ∉ dsts (cycleMoves (l₀ :: rest)) := by
            rw [dsts_cycleMoves]; exact hB_not_ls x hxB
          have hfixval : σ (π x) = σ x := by
            rw [hσπ x, pmove_of_not_mem_dsts hnotls]
          exact List.mem_filter.2 ⟨hxS, by simp [hxB'.1, ← hfixval, hxB'.2]⟩
      have hlen1 : B.length + 1 ≤ A.length := by
        have := length_le_of_nodup_of_subset (List.nodup_cons.2 ⟨hm2_not_B, hBnod⟩) hB_sub_A
        simpa using this
      have hA_map_sub_B : A.map π_inv ⊆ B := by
        intro x hx
        obtain ⟨y, hyA, rfl⟩ := List.mem_map.1 hx
        have hyS := (List.mem_filter.1 hyA).1
        have hyA' : R y = R m.2 ∧ σ y = σ m.2 := by
          simpa using (List.mem_filter.1 hyA).2
        refine List.mem_filter.2 ⟨hπinv_memS y hyS, ?_⟩
        have hRy : R (π_inv y) = R m.2 := by
          have := hRπ (π_inv y); rw [hrinv] at this; exact this.symm.trans hyA'.1
        simp [hRy, hrinv, hyA'.2]
      have hlen2 : A.length ≤ B.length := by
        have := length_le_of_nodup_of_subset
          (bnd_nodup_map_of_left_inv hAnod π_inv π hrinv) hA_map_sub_B
        simpa using this
      omega
    have hall : ∀ x ∈ (l₀ :: rest).map R, x = R l₀ := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rcases List.mem_cons.1 hy with rfl | hy
      · rfl
      · exact chain_connected R l₀ rest
          (fun m hm => hedge m (List.mem_cons_of_mem _ hm)) y hy
    have h1 : (dedupL ((l₀ :: rest).map (ufRun ss id))).length ≤ 1 :=
      length_dedupL_le_one_of_const hall
    have h2 := length_dedupL_ufRun ss id (l₀ :: rest)
    rw [List.map_id, dedupL_eq_self hn] at h2
    simp only [List.length_cons] at h2 ⊢
    omega

/-- Non-vacuity of `cycle_length_sub_one_le_of_injOn_of_runSwaps` at a store that is injective on
the cycle but not globally: the cycle `[0, 1, 2]` over `Nat` values, with the store
`σ l = l` on `0, 1, 2` and `σ l = 0` elsewhere, is realized by its two swaps. -/
theorem nonvacuity_cycle_length_sub_one_le_of_injOn_of_runSwaps :
    let σ : Nat → Nat := fun l => if l ≤ 2 then l else 0
    ([0, 1, 2] : List Nat).Nodup ∧
      (∀ x ∈ ([0, 1, 2] : List Nat), ∀ y ∈ ([0, 1, 2] : List Nat), σ x = σ y → x = y) ∧
      ¬ Function.Injective σ ∧
      runSwaps (cycleSwaps [0, 1, 2]) σ = pmove (cycleMoves [0, 1, 2]) σ := by
  intro σ
  refine ⟨by decide, by decide, fun h => absurd (h (show σ 0 = σ 3 by decide)) (by decide), ?_⟩
  exact runSwaps_cycleSwaps (by decide) σ

end SwapLocalInjectivity

section PutGetExact
variable {n : Nat}

/-- **Exact condition for PutGet of the preserve-upper lane write.** `putLane L` with the getter
`getLane L` satisfies PutGet on `n`-bit words if and only if the lane is empty (`L.wid = 0`, where
PutGet holds trivially on `BitVec 0`) or fits in the register (`L.off + L.wid ≤ n`). -/
theorem putLane_putGet_iff_wid_zero_or_fits (L : Lane) :
    PutGet (getLane (n := n) L) (putLane L) ↔ (L.wid = 0 ∨ L.Fits n) := by
  constructor
  · intro hpg
    by_cases hw : L.wid = 0
    · exact Or.inl hw
    · right
      unfold Lane.Fits
      apply Classical.byContradiction
      intro hnf
      have hge : n ≤ L.off + (L.wid - 1) := by omega
      have hlt : L.wid - 1 < L.wid := by omega
      have e := congrArg (fun x => x.getLsbD (L.wid - 1)) (hpg (BitVec.allOnes L.wid) 0#n)
      rw [getLsbD_getLane, BitVec.getLsbD_of_ge _ _ hge] at e
      simp [hlt] at e
  · rintro (hw | hfit)
    · intro v w
      apply BitVec.eq_of_getLsbD_eq
      intro j hj; omega
    · exact putLane_putGet_of_fits hfit

/-- The empty-lane case of `putLane_putGet_iff_wid_zero_or_fits`: the lane `(9, 0)` lies beyond
an 8-bit register, does not fit, and still satisfies PutGet. -/
theorem putLane_putGet_width_zero_beyond_register :
    ¬ (⟨9, 0⟩ : Lane).Fits 8 ∧ PutGet (getLane (n := 8) ⟨9, 0⟩) (putLane ⟨9, 0⟩) :=
  ⟨by decide, (putLane_putGet_iff_wid_zero_or_fits ⟨9, 0⟩).2 (Or.inl rfl)⟩

end PutGetExact

end Toy.ParMove
