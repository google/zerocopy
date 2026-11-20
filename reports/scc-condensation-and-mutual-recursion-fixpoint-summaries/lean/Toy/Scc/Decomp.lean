/-
Toy.Scc.Decomp
==============

Results about SCC decompositions and their checker (cards `scc-check`,
`scc-char`, `topo-order`): main statements, tightness counterexamples, and
non-vacuity witnesses.
-/
import Toy.Scc.Graph

namespace Toy.Scc

/-! ## Helpers on transitive closures (fully proved) -/

theorem transGen_head {α : Type} {R : α → α → Prop} {a b c : α}
    (hab : R a b) (hbc : Relation.TransGen R b c) : Relation.TransGen R a c := by
  induction hbc with
  | single e => exact Relation.TransGen.tail (Relation.TransGen.single hab) e
  | tail _ e ih => exact Relation.TransGen.tail ih e

theorem transGen_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (hab : Relation.TransGen R a b) (hbc : Relation.TransGen R b c) :
    Relation.TransGen R a c := by
  induction hbc with
  | single e => exact Relation.TransGen.tail hab e
  | tail _ e ih => exact Relation.TransGen.tail ih e

/-! ## Card `scc-check`: the decidable checker -/

/-- If the closure after `k` steps is closed under calls, one more step adds nothing. -/
theorem reachFrom_succ_eq_of_closed {n : Nat} (E : Graph n) (f : Fin n) (k : Nat)
    (hc : ClosedUnder E (reachFrom E f k)) (y : Fin n) :
    reachFrom E f (k + 1) y = reachFrom E f k y := by
  cases h : reachFrom E f k y
  · show reachStep E (reachFrom E f k) y = false
    simp only [reachStep, h, Bool.false_or, List.any_eq_false, List.mem_finRange,
      true_implies, Bool.and_eq_true, not_and]
    intro x hx e
    exact absurd (hc x y hx e) (by simp [h])
  · exact reachFrom_mono_succ E f k y h

/-- The fuel-bounded closure computes reachability exactly once the fuel is at least
`n - 1` (a shortest call chain visits each function at most once). -/
theorem reachFrom_eq_true_iff_reach_of_pred_le {n : Nat} (E : Graph n) (f g : Fin n)
    {fuel : Nat} (hfuel : n - 1 ≤ fuel) : reachFrom E f fuel g = true ↔ Reach E f g := by
  refine ⟨reach_of_reachFrom E f fuel g, fun hr => ?_⟩
  have inv : ∀ k, ClosedUnder E (reachFrom E f k) ∨
      k + 1 ≤ (List.finRange n).countP (reachFrom E f k) := by
    intro k
    induction k with
    | zero =>
        right
        exact List.countP_pos_iff.mpr ⟨f, List.mem_finRange f, reachFrom_self E f 0⟩
    | succ k ih =>
        by_cases hck : ClosedUnder E (reachFrom E f k)
        · left
          intro x y hx e
          rw [reachFrom_succ_eq_of_closed E f k hck] at hx ⊢
          exact hck x y hx e
        · right
          have hk := ih.resolve_left hck
          have hex : ∃ x y, reachFrom E f k x = true ∧ E x y = true ∧
              reachFrom E f k y = false :=
            Classical.byContradiction fun hne => hck fun x y hx e =>
              Classical.byContradiction fun hy => hne ⟨x, y, hx, e, by simpa using hy⟩
          obtain ⟨x, y, hx, e, hy⟩ := hex
          have hlt : (List.finRange n).countP (reachFrom E f k) <
              (List.finRange n).countP (reachFrom E f (k + 1)) := by
            apply countP_lt_countP_of_imp_of_exists
            · intro z _ hz; exact reachFrom_mono_succ E f k z hz
            · refine ⟨y, List.mem_finRange y, ?_, hy⟩
              show reachStep E (reachFrom E f k) y = true
              simp only [reachStep, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
                true_and, Bool.and_eq_true]
              exact Or.inr ⟨x, hx, e⟩
          omega
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) f.isLt)
  have hmem : reachFrom E f (n - 1) g = true := by
    rcases inv (n - 1) with hc | hcnt
    · exact Reach.mem_of_closed hc hr (reachFrom_self E f _)
    · have hall : (List.finRange n).countP (reachFrom E f (n - 1)) =
          (List.finRange n).length := by
        have := List.countP_le_length (p := reachFrom E f (n - 1)) (l := List.finRange n)
        simp only [List.length_finRange] at this ⊢
        omega
      exact List.countP_eq_length.mp hall g (List.mem_finRange g)
  exact reachFrom_mono E f hfuel g hmem

/-- The SCC checker accepts exactly the valid SCC decompositions. -/
theorem checkScc_eq_true_iff_isSccDecomp {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) :
    checkScc E comp = true ↔ IsSccDecomp E comp := by
  have hreach : ∀ f g, reachFrom E f n g = true ↔ Reach E f g := fun f g =>
    reachFrom_eq_true_iff_reach_of_pred_le E f g (Nat.sub_le n 1)
  simp only [checkScc, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    IsSccDecomp, reachB]
  constructor
  · intro h f g
    have hfg := h f g
    rw [← hreach f g, ← hreach g f]
    cases hb1 : reachFrom E f n g <;> cases hb2 : reachFrom E g n f <;>
      simp [hb1, hb2] at hfg ⊢ <;> exact hfg
  · intro h f g
    have hfg := h f g
    rw [← hreach f g, ← hreach g f] at hfg
    cases hb1 : reachFrom E f n g <;> cases hb2 : reachFrom E g n f <;>
      simp [hb1, hb2] at hfg ⊢ <;> exact hfg

/-- Tightness of `hfuel`: with fuel `n - 2` the closure misses a reachable function. -/
theorem reachFrom_tight_fuel :
    ¬ (3 - 1 ≤ 1) ∧ ¬ (reachFrom gPath3 0 1 2 = true ↔ Reach gPath3 0 2) := by
  refine ⟨by decide, fun h => ?_⟩
  have := h.2 reach_gPath3_0_2
  revert this; decide

/-- Non-vacuity: the hypothesis holds and both sides of the equivalence are exercised
(true at one instance, false at another). -/
theorem reachFrom_nonvacuous :
    3 - 1 ≤ 2 ∧ reachFrom gPath3 0 2 2 = true ∧ Reach gPath3 0 2 ∧
      reachFrom gPath3 2 2 0 = false ∧ ¬ Reach gPath3 2 0 :=
  ⟨by decide, by decide, reach_gPath3_0_2, by decide, not_reach_gPath3_2_0⟩

/-- Non-vacuity for the checker: accepted and valid at one instance, rejected and
invalid at two others (a split and a merge). -/
theorem checkScc_nonvacuous :
    (checkScc gPath idComp = true ∧ IsSccDecomp gPath idComp) ∧
      (checkScc gCycle idComp = false ∧ ¬ IsSccDecomp gCycle idComp) ∧
      (checkScc gPath oneComp = false ∧ ¬ IsSccDecomp gPath oneComp) :=
  ⟨⟨by decide, isSccDecomp_gPath_id⟩, ⟨by decide, not_isSccDecomp_gCycle_id⟩,
    ⟨by decide, not_isSccDecomp_gPath_one⟩⟩

/-! ## Card `scc-char`: mutually reachable blocks plus acyclic condensation -/

/-- A decomposition is a valid SCC decomposition iff every block is mutually reachable
(in the whole graph) and the condensation is acyclic. -/
theorem isSccDecomp_iff_blocksMutuallyReachable_and_condensationAcyclic {n k : Nat}
    (E : Graph n) (comp : Fin n → Fin k) :
    IsSccDecomp E comp ↔ BlocksMutuallyReachable E comp ∧ CondensationAcyclic E comp := by
  constructor
  · intro hscc
    refine ⟨fun f g h => (hscc f g).1 h, fun c hcyc => ?_⟩
    have liftReach : ∀ a b, Relation.TransGen (CondEdge E comp) a b →
        ∀ f g, comp f = a → comp g = b → Reach E f g := by
      intro a b htr
      induction htr with
      | single e =>
        obtain ⟨_, u, v, hu, hv, huv⟩ := e
        intro f g hf hg
        exact (((hscc f u).1 (hf.trans hu.symm)).1.trans (Reach.single huv)).trans
          ((hscc v g).1 (hv.trans hg.symm)).1
      | tail _ e ih =>
        obtain ⟨_, u, v, hu, hv, huv⟩ := e
        intro f g hf hg
        exact ((ih f u hf hu).trans (Reach.single huv)).trans
          ((hscc v g).1 (hv.trans hg.symm)).1
    cases hcyc with
    | single e => exact e.1 rfl
    | tail htr e =>
      obtain ⟨hne, u, v, hu, hv, huv⟩ := e
      have hvu : Reach E v u := liftReach _ _ htr v u hv hu
      exact hne (hu.symm.trans (((hscc u v).2 ⟨Reach.single huv, hvu⟩).trans hv))
  · rintro ⟨hmut, hacyc⟩ f g
    refine ⟨hmut f g, fun ⟨hfg, hgf⟩ => ?_⟩
    have proj : ∀ x y, Reach E x y →
        comp x = comp y ∨ Relation.TransGen (CondEdge E comp) (comp x) (comp y) := by
      intro x y hr
      induction hr with
      | refl => exact Or.inl rfl
      | @step a b d hab _ ih =>
        by_cases h : comp a = comp b
        · rw [h]; exact ih
        · have he : CondEdge E comp (comp a) (comp b) := ⟨h, a, b, rfl, rfl, hab⟩
          rcases ih with hbd | hbd
          · rw [← hbd]; exact Or.inr (Relation.TransGen.single he)
          · exact Or.inr (transGen_head he hbd)
    exact Classical.byContradiction fun hne => by
      rcases proj f g hfg with h | h1
      · exact hne h
      · rcases proj g f hgf with h | h2
        · exact hne h.symm
        · exact hacyc (comp f) (transGen_trans h1 h2)

/-- Necessity of the conjunct `CondensationAcyclic`: splitting the 2-cycle keeps blocks
mutually reachable but is not an SCC decomposition. -/
theorem sccChar_tight_acyclic :
    BlocksMutuallyReachable gCycle idComp ∧ ¬ CondensationAcyclic gCycle idComp ∧
      ¬ IsSccDecomp gCycle idComp :=
  ⟨fun f g h => by subst h; exact ⟨Reach.refl _, Reach.refl _⟩,
    not_condensationAcyclic_gCycle_id, not_isSccDecomp_gCycle_id⟩

/-- Necessity of the conjunct `BlocksMutuallyReachable`: merging two unrelated functions
gives an acyclic (one-block) condensation but not an SCC decomposition. -/
theorem sccChar_tight_mutual :
    CondensationAcyclic gEmpty oneComp ∧ ¬ BlocksMutuallyReachable gEmpty oneComp ∧
      ¬ IsSccDecomp gEmpty oneComp := by
  have hnr : ¬ Reach gEmpty 0 1 := fun r =>
    absurd (Reach.mem_of_closed (S := fun x => decide (x = 0)) (by decide) r (by decide))
      (by decide)
  refine ⟨condensationAcyclic_of_calleesFirst (order := [0]) (by decide),
    fun h => hnr (h 0 1 rfl).1, fun h => hnr ((h 0 1).1 rfl).1⟩

/-- Non-vacuity: both sides hold for the singleton decomposition of `0 → 0, 0 → 1, 1 → 1`,
whose condensation has an edge (`0 → 1`) and whose blocks are recursive. -/
theorem sccChar_nonvacuous :
    IsSccDecomp gMix idComp ∧ BlocksMutuallyReachable gMix idComp ∧
      CondensationAcyclic gMix idComp ∧ CondEdge gMix idComp 0 1 :=
  ⟨isSccDecomp_gMix_id, fun f g h => (isSccDecomp_gMix_id f g).1 h,
    condensationAcyclic_of_calleesFirst (order := [1, 0]) (by decide),
    ⟨by decide, 0, 1, rfl, rfl, by decide⟩⟩

/-! ## Card `topo-order`: acyclic condensations are exactly those with a callees-first order -/

/-- The condensation is acyclic iff some duplicate-free processing order of blocks covers
every function's block and is callees-first. -/
theorem condensationAcyclic_iff_exists_nodup_covering_calleesFirst_order {n k : Nat}
    (E : Graph n) (comp : Fin n → Fin k) :
    CondensationAcyclic E comp ↔
      ∃ order : List (Fin k), order.Nodup ∧ Covers comp order ∧ CalleesFirst E comp order := by
  constructor
  · intro hacyc
    classical
    -- Number of strict condensation descendants of a block.
    let desc : Fin k → Nat := fun c =>
      (List.finRange k).countP fun d => decide (Relation.TransGen (CondEdge E comp) c d)
    have hlt : ∀ c d, CondEdge E comp c d → desc d < desc c := by
      intro c d hcd
      apply countP_lt_countP_of_imp_of_exists
      · intro x _ hx
        simp only [decide_eq_true_eq] at hx ⊢
        exact transGen_head hcd hx
      · refine ⟨d, List.mem_finRange d, ?_, ?_⟩
        · simp only [decide_eq_true_eq]; exact Relation.TransGen.single hcd
        · simp only [decide_eq_false_iff_not]; exact hacyc d
    let le : Fin k → Fin k → Bool := fun a b => decide (desc a ≤ desc b)
    let order := (List.finRange k).mergeSort le
    have hperm := List.mergeSort_perm (List.finRange k) le
    have hmem : ∀ c, c ∈ order := fun c => hperm.mem_iff.mpr (List.mem_finRange c)
    have hsorted : order.Pairwise (fun a b => le a b = true) :=
      List.pairwise_mergeSort
        (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at hab hbc ⊢; omega)
        (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _
    refine ⟨order, hperm.nodup_iff.mpr (List.nodup_finRange k), fun f => hmem _, ?_⟩
    intro f g e hne
    refine ⟨hmem _, hmem _, ?_⟩
    have hd : desc (comp g) < desc (comp f) := hlt _ _ ⟨hne, f, g, rfl, rfl, e⟩
    rcases Nat.lt_or_ge (pos order (comp g)) (pos order (comp f)) with h | h
    · exact h
    · exfalso
      rcases Nat.lt_or_eq_of_le h with h' | h'
      · have hpf := pos_lt_length_of_mem (hmem (comp f))
        have hpg := pos_lt_length_of_mem (hmem (comp g))
        have hp := List.pairwise_iff_getElem.mp hsorted _ _ hpf hpg h'
        have ef : order[pos order (comp f)] = comp f := List.getElem_idxOf hpf
        have eg : order[pos order (comp g)] = comp g := List.getElem_idxOf hpg
        rw [ef, eg] at hp
        simp only [le, decide_eq_true_eq] at hp
        omega
      · exact hne (eq_of_pos_eq_of_mem (hmem _) (hmem _) h')
  · rintro ⟨order, _, _, hfirst⟩
    exact condensationAcyclic_of_calleesFirst hfirst

/-- Non-vacuity: both sides hold for `0 → 1` with order `[1, 0]`, and both fail for the
split 2-cycle. -/
theorem topoOrder_nonvacuous :
    (CondensationAcyclic gPath idComp ∧
        ([1, 0] : List (Fin 2)).Nodup ∧ Covers (idComp (n := 2)) [1, 0] ∧
          CalleesFirst gPath idComp [1, 0]) ∧
      (¬ CondensationAcyclic gCycle idComp ∧
        ∀ order : List (Fin 2), ¬ CalleesFirst gCycle idComp order) :=
  ⟨⟨condensationAcyclic_of_calleesFirst (order := [1, 0]) (by decide), by decide, by decide,
      by decide⟩,
    ⟨not_condensationAcyclic_gCycle_id, not_calleesFirst_gCycle_id⟩⟩

end Toy.Scc
