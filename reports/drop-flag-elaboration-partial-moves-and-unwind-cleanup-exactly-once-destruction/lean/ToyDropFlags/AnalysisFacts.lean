import ToyDropFlags.Elab

/-!
# Structural facts about the one-pass analyses

Index bookkeeping for `reachList` and `analysis`, and the fact that may-init implies forward
reachability and atom membership. All fully proved.
-/

namespace Toy.DropFlags

theorem mem_atomsOf_mem_allAtoms (ls : List Ty) (p a : Place) (h : a ∈ atomsOf ls p) :
    a ∈ allAtoms ls := by
  unfold atomsOf at h
  exact (List.mem_filter.1 h).1

theorem mem_minus {s k : List Place} {a : Place} (h : a ∈ minus s k) : a ∈ s := by
  unfold minus at h
  exact (List.mem_filter.1 h).1

theorem edgeOut_mem_allAtoms (ls : List Ty) (g : Granularity) (n : SNode) (st : List Place)
    (hst : ∀ b ∈ st, b ∈ allAtoms ls) :
    ∀ p ∈ edgeOut ls g n st, ∀ a ∈ p.2, a ∈ allAtoms ls := by
  intro p hp a ha
  unfold edgeOut at hp
  cases n <;> simp at hp
  case init q nx =>
    rcases hp with rfl
    rcases List.mem_append.1 ha with h1 | h2
    · exact hst a h1
    · exact mem_atomsOf_mem_allAtoms ls q a h2
  case move q nx =>
    rcases hp with rfl
    exact hst a (mem_minus ha)
  case branch l1 l2 =>
    rcases hp with rfl | rfl <;> exact hst a ha
  case call args dest nx un =>
    rcases hp with rfl | rfl
    · rcases List.mem_append.1 ha with h1 | h2
      · exact hst a (mem_minus h1)
      · cases dest with
        | none => cases h2
        | some d => exact mem_atomsOf_mem_allAtoms ls d a h2
    · exact hst a (mem_minus ha)

theorem edgeOut_fst_mem_succs (ls : List Ty) (g : Granularity) (n : SNode) (st : List Place) :
    ∀ p ∈ edgeOut ls g n st, p.1 ∈ n.succs := by
  intro p hp
  unfold edgeOut SNode.succs at *
  cases n <;> simp at hp ⊢
  all_goals
    rcases hp with rfl | rfl <;> simp

theorem any_eq_of_forall_mem {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, h x List.mem_cons_self]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem reachAux_prefix (s : SProg) :
    ∀ (k : Nat) (acc : List Bool) (i : Nat), i < acc.length →
      (reachableAux s k acc).getD i false = acc.getD i false := by
  intro k
  induction k with
  | zero => intro acc i _; rfl
  | succ k ih =>
    intro acc i hi
    unfold reachableAux
    rw [ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem reachAux_length (s : SProg) :
    ∀ (k : Nat) (acc : List Bool), (reachableAux s k acc).length = acc.length + k := by
  intro k
  induction k with
  | zero => intro acc; simp [reachableAux]
  | succ k ih => intro acc; unfold reachableAux; rw [ih]; simp; omega

theorem reachList_spec (s : SProg) (j : Nat) (hj : j < s.nodes.length) :
    (reachList s).getD j false =
      (decide (j = 0) ||
        (List.range j).any fun i => (reachList s).getD i false && (s.node i).succs.contains j) := by
  unfold reachList
  have hsplit : ∀ k acc, j = acc.length →
      (reachableAux s (k + 1) acc).getD j false =
        (decide (j = 0) ||
          (List.range j).any fun i => acc.getD i false && (s.node i).succs.contains j) := by
    intro k acc hlen
    unfold reachableAux
    rw [reachAux_prefix s k _ j (by simp; omega)]
    subst hlen
    simp [List.getD_eq_getElem?_getD]
  have stepTo : ∀ m acc, acc.length + m = s.nodes.length → j ≥ acc.length →
      (reachableAux s m acc).getD j false =
        (decide (j = 0) ||
          (List.range j).any fun i =>
            (reachableAux s m acc).getD i false && (s.node i).succs.contains j) := by
    intro m
    induction m with
    | zero => intro acc hsum hge; omega
    | succ m ih =>
      intro acc hsum hge
      by_cases heq : j = acc.length
      · rw [hsplit m acc heq]
        congr 1
        apply any_eq_of_forall_mem
        intro i hi
        have hilt : i < acc.length := by rw [List.mem_range] at hi; omega
        rw [reachAux_prefix s (m + 1) acc i hilt]
      · unfold reachableAux
        exact ih _ (by simp; omega) (by simp; omega)
  exact stepTo s.nodes.length [] (by simp) (Nat.zero_le j)

theorem foldl_append_mem {α : Type} :
    ∀ (xs : List (List α)) (init : List α) (a : α),
      a ∈ xs.foldl (· ++ ·) init → a ∈ init ∨ ∃ y ∈ xs, a ∈ y := by
  intro xs
  induction xs with
  | nil => intro init a h; exact Or.inl h
  | cons y ys ih =>
    intro init a h
    rcases ih (init ++ y) a h with h1 | ⟨z, hz, az⟩
    · rcases List.mem_append.1 h1 with hi | hy
      · exact Or.inl hi
      · exact Or.inr ⟨y, List.mem_cons_self, hy⟩
    · exact Or.inr ⟨z, List.mem_cons_of_mem y hz, az⟩

theorem analysisAux_may_inv (s : SProg) :
    ∀ (k : Nat) (acc : List (List Place)),
      acc.length + k = s.nodes.length →
      (∀ i < acc.length, ∀ a ∈ acc.getD i [],
        (reachList s).getD i false = true ∧ a ∈ allAtoms s.locals) →
      ∀ i < s.nodes.length, ∀ a ∈ (analysisAux s .fine true (reachList s) k acc).getD i [],
        (reachList s).getD i false = true ∧ a ∈ allAtoms s.locals := by
  intro k
  induction k with
  | zero =>
    intro acc hsum hinv i hi a ha
    unfold analysisAux at ha
    exact hinv i (by omega) a ha
  | succ k ih =>
    intro acc hsum hinv
    unfold analysisAux
    apply ih _ (by simp; omega)
    intro idx hidx a ha
    simp only [List.length_append, List.length_singleton] at hidx
    by_cases hlt : idx < acc.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at ha
      exact hinv idx hlt a ha
    · have heq : idx = acc.length := by omega
      subst heq
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at ha
      by_cases hz : acc.length = 0
      · simp [hz] at ha
      · simp only [hz, ite_false] at ha
        generalize hins : flowIn s .fine (reachList s) acc.length acc = ins at ha
        cases ins with
        | nil => simp at ha
        | cons x0 xs =>
          simp only at ha
          have hmem : ∃ y ∈ (x0 :: xs), a ∈ y := by
            rcases foldl_append_mem xs x0 a ha with hx0 | ⟨y, hy, hay⟩
            · exact ⟨x0, List.mem_cons_self, hx0⟩
            · exact ⟨y, List.mem_cons_of_mem x0 hy, hay⟩
          rcases hmem with ⟨y, hy, hay⟩
          rw [← hins] at hy
          unfold flowIn at hy
          rcases List.mem_flatMap.1 hy with ⟨pred, hpredRange, hpredOut⟩
          rw [List.mem_range] at hpredRange
          by_cases hrp : (reachList s).getD pred false = true
          · have hite : (if (reachList s).getD pred false = true then
                ((edgeOut s.locals .fine (s.node pred) (acc.getD pred [])).filter (·.1 == acc.length)).map (·.2)
              else []) =
              ((edgeOut s.locals .fine (s.node pred) (acc.getD pred [])).filter (·.1 == acc.length)).map (·.2) := by
              split
              · rfl
              · contradiction
            rw [hite, List.mem_map] at hpredOut
            rcases hpredOut with ⟨pair, hpairFilt, rfl⟩
            rw [List.mem_filter] at hpairFilt
            rcases hpairFilt with ⟨hpairEdge, hpairDst⟩
            have hAtom : a ∈ allAtoms s.locals := by
              apply edgeOut_mem_allAtoms s.locals .fine (s.node pred) (acc.getD pred []) _ pair hpairEdge a hay
              intro b hb
              exact (hinv pred hpredRange b hb).2
            have hSucc : acc.length ∈ (s.node pred).succs := by
              have hs := edgeOut_fst_mem_succs s.locals .fine (s.node pred) (acc.getD pred []) pair hpairEdge
              have hd : pair.1 = acc.length := eq_of_beq hpairDst
              rwa [hd] at hs
            have hReach : (reachList s).getD acc.length false = true := by
              rw [reachList_spec s acc.length (by omega)]
              apply Bool.or_eq_true_iff.2
              right
              apply List.any_eq_true.2
              refine ⟨pred, List.mem_range.2 hpredRange, ?_⟩
              rw [Bool.and_eq_true]
              exact ⟨hrp, List.contains_iff_exists_mem_beq.2 ⟨acc.length, hSucc, BEq.refl _⟩⟩
            exact ⟨hReach, hAtom⟩
          · have hite : (if (reachList s).getD pred false = true then
                ((edgeOut s.locals .fine (s.node pred) (acc.getD pred [])).filter (·.1 == acc.length)).map (·.2)
              else []) = [] := by
              split
              · contradiction
              · rfl
            rw [hite] at hpredOut
            cases hpredOut

theorem analysisAux_length (s : SProg) (g : Granularity) (may : Bool) (reach : List Bool) :
    ∀ (k : Nat) (acc : List (List Place)),
      (analysisAux s g may reach k acc).length = acc.length + k := by
  intro k
  induction k with
  | zero => intro acc; simp [analysisAux]
  | succ k ih => intro acc; unfold analysisAux; rw [ih]; simp; omega

/-- **May-init implies forward-reachable and atom.** If `a` is may-init at node `i` (fine
analysis), then node `i` is forward-reachable and `a` is an atom of the locals: nodes that are not
forward-reachable do not propagate, and the analysis only ever adds atoms. -/
theorem forwardReachable_and_mem_allAtoms_of_mayInit (s : SProg) (i : Nat) (a : Place)
    (h : mayInit s .fine i a = true) : ForwardReachable s i = true ∧ a ∈ allAtoms s.locals := by
  unfold mayInit analysis at h
  have hmem : a ∈ (analysisAux s .fine true (reachList s) s.nodes.length []).getD i [] := by
    rcases List.contains_iff_exists_mem_beq.1 h with ⟨b, hb, hab⟩
    rwa [eq_of_beq hab]
  have hlt : i < s.nodes.length := by
    apply Classical.byContradiction
    intro hge
    have hlen : (analysisAux s .fine true (reachList s) s.nodes.length []).length = s.nodes.length := by
      simpa using analysisAux_length s .fine true (reachList s) s.nodes.length []
    have hnil : (analysisAux s .fine true (reachList s) s.nodes.length []).getD i [] = [] := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    rw [hnil] at hmem
    cases hmem
  exact analysisAux_may_inv s s.nodes.length [] (by simp) (fun _ h0 => by cases h0) i hlt a hmem

/-- A filter by `p` whose members all pass `q` is no longer than the filter by `q`. -/
theorem filter_length_le_of_subset {α : Type} [DecidableEq α] (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l.filter p, a ∈ l.filter q) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons z zs ih =>
    have ih' : (zs.filter p).length ≤ (zs.filter q).length := by
      apply ih
      intro a ha
      rw [List.mem_filter] at ha ⊢
      have hq := h a (List.mem_filter.2 ⟨List.mem_cons_of_mem z ha.1, ha.2⟩)
      exact ⟨ha.1, (List.mem_filter.1 hq).2⟩
    by_cases hp : p z = true
    · have hqz := (List.mem_filter.1 (h z (by simp [hp]))).2
      simp [hp, hqz]; omega
    · have hp' : p z = false := by simpa using hp
      simp [hp']
      by_cases hq : q z = true <;> simp [hq] <;> omega

end Toy.DropFlags
