import ToyDataflow.CFG

/-!
# MOP ⊑ MFP (soundness) and MFP = MOP for distributive transfers (exactness)

"Soundness" and "exactness" here relate solutions of the abstract inequations to
the join over all syntactic CFG paths of the given transfer functions. No concrete
program semantics is modeled, and paths include combinations of branches that no
execution may take.
-/

namespace Toy.Dataflow

variable {n : Nat} {α : Type}

/-! ## Soundness -/

/-- Soundness, per path: for monotone transfer functions, the value of every path
from the entry to `v` is below `x v`, for every solution `x` (in particular the
least solution). The only law assumed of `L.le` is transitivity: `L.le` may be any
transitive relation (reflexivity and antisymmetry are not used). -/
theorem walk_val_le_of_isSolution_of_monotone (L : Lat α) (G : CFG n α)
    (htrans : L.LeTrans) (hmono : ∀ u, Monotone L (G.f u))
    {x : Fin n → α} (hx : IsSolution L G x) {v : Fin n} (p : Walk G v) :
    L.le p.val (x v) := by
  induction p with
  | nil => exact hx.1
  | snoc p h ih => exact htrans _ _ _ (hmono _ _ _ ih) (hx.2 _ _ h)

/-- Soundness (MOP ⊑ MFP): for monotone transfer functions and a transitive relation
`L.le`, if `m` is the MOP value at `v` (a least upper bound of all path values),
then `m ≤ x v` for every solution `x`, in particular for the least solution. -/
theorem mop_le_of_isSolution_of_monotone (L : Lat α) (G : CFG n α)
    (htrans : L.LeTrans) (hmono : ∀ u, Monotone L (G.f u))
    {x : Fin n → α} (hx : IsSolution L G x) {v : Fin n} {m : α}
    (hm : IsMOPAt L G v m) : L.le m (x v) :=
  hm.2 (x v) (fun _ ⟨p, hp⟩ => hp ▸ walk_val_le_of_isSolution_of_monotone L G htrans hmono hx p)

/-! ## Auxiliary lattice facts for exactness (proved) -/

theorem wf_exists_minimal {β : Type} {R : β → β → Prop} (hwf : WellFounded R)
    (J : β → Prop) {a : β} (ha : J a) : ∃ m, J m ∧ ∀ b, J b → ¬ R b m := by
  classical
  refine hwf.induction (C := fun a => J a → ∃ m, J m ∧ ∀ b, J b → ¬ R b m) a ?_ ha
  intro a ih ha
  by_cases h : ∃ b, J b ∧ R b a
  · obtain ⟨b, hb, hr⟩ := h
    exact ih b hr hb
  · exact ⟨a, ha, fun b hb hr => h ⟨b, hb, hr⟩⟩

theorem joinList_le {L : Lat α} (hL : L.IsJSL) {l : List α} {u : α}
    (h : ∀ s ∈ l, L.le s u) : L.le (L.joinList l) u := by
  induction l with
  | nil => exact hL.bot_le u
  | cons a l ih =>
    exact Lat.join_le hL (h a (List.mem_cons_self ..))
      (ih (fun s hs => h s (List.mem_cons_of_mem _ hs)))

/-- With the ascending chain condition, every set has a least upper bound, and it
is the join of a finite list of members of the set (`bot` for the empty set). -/
theorem exists_list_isLUB {L : Lat α} (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
    (S : α → Prop) : ∃ l : List α, (∀ s ∈ l, S s) ∧ L.IsLUB S (L.joinList l) := by
  classical
  by_cases hne : ∃ s, S s
  · obtain ⟨s0, hs0⟩ := hne
    let J : α → Prop := fun a => ∃ l : List α, (∀ s ∈ l, S s) ∧ L.joinList l = a
    have hJ : J (L.joinList [s0]) := ⟨[s0], by simpa using hs0, rfl⟩
    obtain ⟨m, ⟨l, hl, rfl⟩, hmax⟩ := wf_exists_minimal hacc J hJ
    refine ⟨l, hl, ?_, fun u hu => joinList_le hL (fun s hs => hu s (hl s hs))⟩
    intro s hs
    have hJ' : J (L.join s (L.joinList l)) := ⟨s :: l, by
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hs
      · exact hl t ht, rfl⟩
    have hle := Lat.le_join_right hL s (L.joinList l)
    have heq : L.join s (L.joinList l) = L.joinList l := by
      apply Classical.byContradiction
      intro hne
      exact hmax _ hJ' ⟨hle, fun h => hne h.symm⟩
    rw [← heq]
    exact Lat.le_join_left hL _ _
  · refine ⟨[], by simp, fun s hs => absurd ⟨s, hs⟩ hne, fun u _ => hL.bot_le u⟩

theorem apply_joinList_le {L : Lat α} (hL : L.IsJSL) {f : α → α} (hf : Distributive L f)
    {l : List α} {u : α} (hbot : L.le (f L.bot) u) (hl : ∀ s ∈ l, L.le (f s) u) :
    L.le (f (L.joinList l)) u := by
  induction l with
  | nil => exact hbot
  | cons a l ih =>
    show L.le (f (L.join a (L.joinList l))) u
    rw [hf]
    exact Lat.join_le hL (hl a (List.mem_cons_self ..))
      (ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)))

/-! ## Existence of MOP values and of the least solution under the ascending chain condition -/

/-- Under the lattice laws and the ascending chain condition, the MOP value exists at
every node. -/
theorem exists_isMOPAt_of_acc (L : Lat α) (G : CFG n α) (hL : L.IsJSL)
    (hacc : L.AscendingChainCondition) (v : Fin n) : ∃ m, IsMOPAt L G v m :=
  let ⟨l, _, hlub⟩ := exists_list_isLUB hL hacc (pathVals G v)
  ⟨L.joinList l, hlub⟩

/-- MFP existence: under the lattice laws, the ascending chain condition, and
monotone transfer functions, the inequations have a least solution. (No
distributivity, height bound or decidability is needed.) -/
theorem exists_isLeastSolution_of_monotone_of_acc (L : Lat α) (G : CFG n α)
    (hL : L.IsJSL) (hacc : L.AscendingChainCondition) (hmono : ∀ u, Monotone L (G.f u)) :
    ∃ x : Fin n → α, IsLeastSolution L G x := by
  classical
  have hpwL := pwLat_isJSL n hL
  have hpwAcc := pwLat_acc n hacc
  let J : (Fin n → α) → Prop := fun x =>
    (∀ y, IsSolution L G y → (pwLat n L).le x y) ∧ (pwLat n L).le x (eqRHS L G x)
  have hbot : J (fun _ => L.bot) :=
    ⟨fun y _ => hpwL.bot_le y, hpwL.bot_le _⟩
  obtain ⟨m, hm, hmax⟩ := wf_exists_minimal hpwAcc J hbot
  have hstep : J (eqRHS L G m) := by
    refine ⟨?_, eqRHS_monotone hL G hmono m (eqRHS L G m) hm.2⟩
    intro y hy
    have hsm := eqRHS_monotone hL G hmono m y (hm.1 y hy)
    have hsy : (pwLat n L).le (eqRHS L G y) y := (eqRHS_le_iff hL G y y).2 hy
    exact hpwL.trans _ _ _ hsm hsy
  have hmeq : m = eqRHS L G m := by
    apply Classical.byContradiction
    intro hne
    exact hmax (eqRHS L G m) hstep ⟨hm.2, hne⟩
  have hsol : IsSolution L G m := by
    have hrefl : (pwLat n L).le (eqRHS L G m) m := by
      rw [← hmeq]; exact hpwL.refl m
    exact (eqRHS_le_iff hL G m m).1 hrefl
  exact ⟨m, hsol, hm.1⟩

/-- With monotone transfer functions, the least solution of the inequations also
satisfies the dataflow equations with equality (it is a fixed point of `eqRHS`). -/
theorem isEquationSolution_of_isLeastSolution_of_monotone {L : Lat α} (hL : L.IsJSL)
    (G : CFG n α) (hmono : ∀ u, Monotone L (G.f u)) {x : Fin n → α}
    (hx : IsLeastSolution L G x) : IsEquationSolution L G x := by
  have h1 : (pwLat n L).le (eqRHS L G x) x := (isSolution_iff_eqRHS_le hL G x).1 hx.1
  have h2 : IsSolution L G (eqRHS L G x) :=
    (isSolution_iff_eqRHS_le hL G _).2 (eqRHS_monotone hL G hmono _ _ h1)
  intro w
  exact hL.antisymm _ _ (hx.2 _ h2 w) (h1 w)

/-! ## Exactness -/

/-- Exactness: in a join-semilattice with the ascending chain condition, if every
transfer function distributes over binary joins and every node unreachable from
the entry has a strict transfer function, then the least solution `x` equals MOP
at every node: `x v` is a least upper bound of all path values at `v`. -/
theorem isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict
    (L : Lat α) (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
    (hdist : ∀ u, Distributive L (G.f u)) (hstrict : UnreachableStrict L G)
    {x : Fin n → α} (hx : IsLeastSolution L G x) (v : Fin n) :
    IsMOPAt L G v (x v) := by
  classical
  have hex := fun w => exists_list_isLUB hL hacc (pathVals G w)
  let ls : Fin n → List α := fun w => Classical.choose (hex w)
  have hls : ∀ w, ∀ s ∈ ls w, pathVals G w s := fun w => (Classical.choose_spec (hex w)).1
  have hlub : ∀ w, L.IsLUB (pathVals G w) (L.joinList (ls w)) :=
    fun w => (Classical.choose_spec (hex w)).2
  have hmono : ∀ u, Monotone L (G.f u) := fun u => monotone_of_distributive hL (hdist u)
  let y : Fin n → α := fun w => L.joinList (ls w)
  have hy : IsSolution L G y := by
    refine ⟨(hlub G.entry).1 _ (pathVals_init G), ?_⟩
    intro u w huw
    apply apply_joinList_le hL (hdist u)
    · by_cases hr : Reachable G u
      · obtain ⟨p⟩ := hr
        exact hL.trans _ _ _ (hmono u _ _ (hL.bot_le _))
          ((hlub w).1 _ (pathVals_step huw ⟨p, rfl⟩))
      · rw [hstrict u hr]; exact hL.bot_le _
    · intro s hs
      exact (hlub w).1 _ (pathVals_step huw (hls u s hs))
  have h1 : L.le (x v) (y v) := hx.2 y hy v
  have h2 : L.le (y v) (x v) := mop_le_of_isSolution_of_monotone L G hL.trans hmono hx.1 (hlub v)
  have : x v = y v := hL.antisymm _ _ h1 h2
  rw [this]
  exact hlub v

/-- Exactness when every node is reachable from the entry. -/
theorem isMOPAt_of_isLeastSolution_of_distributive_of_allReachable
    (L : Lat α) (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
    (hdist : ∀ u, Distributive L (G.f u)) (hreach : AllReachable G)
    {x : Fin n → α} (hx : IsLeastSolution L G x) (v : Fin n) :
    IsMOPAt L G v (x v) :=
  isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict L G hL hacc hdist
    (unreachableStrict_of_allReachable L hreach) hx v

/-- Exactness when every transfer function is strict (`f u bot = bot`); this
covers unreachable nodes, where both sides are `bot`. -/
theorem isMOPAt_of_isLeastSolution_of_distributive_of_strict
    (L : Lat α) (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
    (hdist : ∀ u, Distributive L (G.f u)) (hstrict : ∀ u, Strict L (G.f u))
    {x : Fin n → α} (hx : IsLeastSolution L G x) (v : Fin n) :
    IsMOPAt L G v (x v) :=
  isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict L G hL hacc hdist
    (unreachableStrict_of_strict L hstrict) hx v

/-- Exactness with existence: under the hypotheses of
`isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict`, a least solution
exists, and it equals MOP at every node. -/
theorem exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict
    (L : Lat α) (G : CFG n α) (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
    (hdist : ∀ u, Distributive L (G.f u)) (hstrict : UnreachableStrict L G) :
    ∃ x : Fin n → α, IsLeastSolution L G x ∧ ∀ v, IsMOPAt L G v (x v) := by
  obtain ⟨x, hx⟩ := exists_isLeastSolution_of_monotone_of_acc L G hL hacc
    (fun u => monotone_of_distributive hL (hdist u))
  exact ⟨x, hx, isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict L G hL hacc
    hdist hstrict hx⟩

end Toy.Dataflow
