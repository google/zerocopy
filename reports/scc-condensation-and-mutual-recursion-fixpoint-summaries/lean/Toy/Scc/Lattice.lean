/-
Toy.Scc.Lattice
===============

Per-function summaries in a finite powerset lattice, transfer functions, the
laws they may satisfy (each a separate named proposition), extremal fixpoints,
Kleene iteration, two families of monotone transfers used by the examples, and
fully proved certification helpers for concrete instances.
-/
import Toy.Scc.Graph

namespace Toy.Scc

/-! ## Summaries -/

/-- An abstract value: a subset of `Fin m` given as a bit vector (the powerset
lattice of `Fin m` ordered by inclusion). -/
abbrev Val (m : Nat) := Fin m → Bool

/-- A summary vector: one abstract value per function. -/
abbrev Summ (n m : Nat) := Fin n → Val m

/-- A transfer function on summary vectors (one equation per function). -/
abbrev Transfer (n m : Nat) := Summ n m → Summ n m

/-- The pointwise inclusion order on summary vectors. -/
def Le {n m : Nat} (σ τ : Summ n m) : Prop := ∀ f i, σ f i = true → τ f i = true

instance {n m : Nat} (σ τ : Summ n m) : Decidable (Le σ τ) :=
  inferInstanceAs (Decidable (∀ f i, σ f i = true → τ f i = true))

/-- Least summary vector (every function summarized by the empty set). -/
def bot {n m : Nat} : Summ n m := fun _ _ => false
/-- Greatest summary vector. -/
def top {n m : Nat} : Summ n m := fun _ _ => true

/-- Boolean equality test on summary vectors. -/
def summEqB {n m : Nat} (σ τ : Summ n m) : Bool :=
  (List.finRange n).all fun f => (List.finRange m).all fun i => σ f i == τ f i

theorem summEqB_eq_true_iff {n m : Nat} (σ τ : Summ n m) : summEqB σ τ = true ↔ σ = τ := by
  simp only [summEqB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  exact ⟨fun h => funext fun f => funext fun i => h f i, fun h f i => by rw [h]⟩

instance instDecidableEqSumm {n m : Nat} : DecidableEq (Summ n m) :=
  fun σ τ => decidable_of_iff _ (summEqB_eq_true_iff σ τ)

theorem Le.refl {n m : Nat} (σ : Summ n m) : Le σ σ := fun _ _ h => h

theorem Le.trans {n m : Nat} {σ τ ρ : Summ n m} (h₁ : Le σ τ) (h₂ : Le τ ρ) : Le σ ρ :=
  fun f i h => h₂ f i (h₁ f i h)

theorem Le.antisymm {n m : Nat} {σ τ : Summ n m} (h₁ : Le σ τ) (h₂ : Le τ σ) : σ = τ := by
  funext f i
  cases hσ : σ f i <;> cases hτ : τ f i
  · rfl
  · exact absurd (h₂ f i hτ) (by simp [hσ])
  · exact absurd (h₁ f i hσ) (by simp [hτ])
  · rfl

theorem bot_le {n m : Nat} (σ : Summ n m) : Le bot σ := fun _ _ h => by simp [bot] at h
theorem le_top {n m : Nat} (σ : Summ n m) : Le σ top := fun _ _ _ => rfl

/-! ## Laws of transfer functions (each a separate proposition) -/

/-- Monotonicity of a transfer function. -/
def Monotone {n m : Nat} (F : Transfer n m) : Prop := ∀ σ τ, Le σ τ → Le (F σ) (F τ)

/-- Locality: the equation of `f` reads only the summaries of the callees of `f`
(this is what makes a transfer function "follow the call graph"). -/
def RespectsCalls {n m : Nat} (E : Graph n) (F : Transfer n m) : Prop :=
  ∀ σ τ f, (∀ g, E f g = true → σ g = τ g) → F σ f = F τ f

/-! ## Extremal fixpoints -/

/-- `σ` is the least fixpoint of `F` (least among all fixpoints). -/
def IsLeastFixpoint {n m : Nat} (F : Transfer n m) (σ : Summ n m) : Prop :=
  F σ = σ ∧ ∀ τ, F τ = τ → Le σ τ

/-- `σ` is the greatest fixpoint of `F` (greatest among all fixpoints). -/
def IsGreatestFixpoint {n m : Nat} (F : Transfer n m) (σ : Summ n m) : Prop :=
  F σ = σ ∧ ∀ τ, F τ = τ → Le τ σ

/-- `k`-fold iteration (Kleene iteration when started at `bot` or `top`). -/
def iter {α : Type} (g : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => iter g k (g a)

theorem iter_succ' {α : Type} (g : α → α) : ∀ k a, iter g (k + 1) a = g (iter g k a)
  | 0, _ => rfl
  | k + 1, a => by
      show iter g (k + 1) (g a) = g (iter g (k + 1) a)
      rw [iter_succ' g k (g a)]; rfl

/-- Iterates of a monotone map stay below any prefixpoint above the start (fully proved). -/
theorem iter_le_of_prefixpoint {n m : Nat} {G : Transfer n m} (hG : Monotone G)
    {x τ : Summ n m} (hx : Le x τ) (hτ : Le (G τ) τ) : ∀ k, Le (iter G k x) τ := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih => rw [iter_succ']; exact (hG _ _ ih).trans hτ

/-- Iterates of a monotone map stay above any postfixpoint below the start (fully proved). -/
theorem le_iter_of_postfixpoint {n m : Nat} {G : Transfer n m} (hG : Monotone G)
    {x τ : Summ n m} (hx : Le τ x) (hτ : Le τ (G τ)) : ∀ k, Le τ (iter G k x) := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih => rw [iter_succ']; exact hτ.trans (hG _ _ ih)

/-- A Kleene iterate from `bot` that is already a fixpoint is the least fixpoint
(fully proved; no height bound involved). -/
theorem isLeastFixpoint_of_iter_fixed {n m : Nat} {F : Transfer n m} (hmono : Monotone F)
    {k : Nat} (hfix : F (iter F k bot) = iter F k bot) : IsLeastFixpoint F (iter F k bot) :=
  ⟨hfix, fun τ hτ => iter_le_of_prefixpoint hmono (bot_le τ) (by rw [hτ]; exact Le.refl τ) k⟩

/-- A Kleene iterate from `top` that is already a fixpoint is the greatest fixpoint. -/
theorem isGreatestFixpoint_of_iter_fixed {n m : Nat} {F : Transfer n m} (hmono : Monotone F)
    {k : Nat} (hfix : F (iter F k top) = iter F k top) : IsGreatestFixpoint F (iter F k top) :=
  ⟨hfix, fun τ hτ => le_iter_of_postfixpoint hmono (le_top τ) (by rw [hτ]; exact Le.refl τ) k⟩

/-! ## Monotone Kleene chains and counting set bits (fully proved helpers) -/

/-- Iterates from `bot` of a monotone map form an ascending chain. -/
theorem iter_bot_le_succ {n m : Nat} {F : Transfer n m} (hmono : Monotone F) :
    ∀ k, Le (iter F k bot) (iter F (k + 1) bot)
  | 0 => bot_le _
  | k + 1 => by
      rw [iter_succ' F k bot, iter_succ' F (k + 1) bot]
      exact hmono _ _ (iter_bot_le_succ hmono k)

theorem iter_bot_mono {n m : Nat} {F : Transfer n m} (hmono : Monotone F)
    {a b : Nat} (hab : a ≤ b) : Le (iter F a bot) (iter F b bot) := by
  induction hab with
  | refl => exact Le.refl _
  | step _ ih => exact ih.trans (iter_bot_le_succ hmono _)

/-- Iterates from `top` of a monotone map form a descending chain. -/
theorem iter_top_succ_le {n m : Nat} {F : Transfer n m} (hmono : Monotone F) :
    ∀ k, Le (iter F (k + 1) top) (iter F k top)
  | 0 => le_top _
  | k + 1 => by
      rw [iter_succ' F k top, iter_succ' F (k + 1) top]
      exact hmono _ _ (iter_top_succ_le hmono k)

/-- Once an iterate is fixed, all later iterates equal it. -/
theorem iter_fixed_add {α : Type} {g : α → α} {k : Nat} {a : α}
    (h : g (iter g k a) = iter g k a) : ∀ j, iter g (k + j) a = iter g k a
  | 0 => rfl
  | j + 1 => by rw [← Nat.add_assoc, iter_succ', iter_fixed_add h j, h]

/-- All coordinates `(f, i)` of a summary vector. -/
def cells (n m : Nat) : List (Fin n × Fin m) :=
  (List.finRange n).flatMap fun f => (List.finRange m).map fun i => (f, i)

theorem mem_cells {n m : Nat} (f : Fin n) (i : Fin m) : (f, i) ∈ cells n m := by
  simp [cells]

theorem length_cells (n m : Nat) : (cells n m).length = n * m := by
  simp [cells, List.length_flatMap, List.map_const']

/-- Number of set bits of a summary vector. -/
def bitCount {n m : Nat} (σ : Summ n m) : Nat := (cells n m).countP fun p => σ p.1 p.2

theorem bitCount_le {n m : Nat} (σ : Summ n m) : bitCount σ ≤ n * m := by
  unfold bitCount; rw [← length_cells]; exact List.countP_le_length

theorem bitCount_lt_of_le_of_ne {n m : Nat} {σ τ : Summ n m} (hle : Le σ τ) (hne : σ ≠ τ) :
    bitCount σ < bitCount τ := by
  apply countP_lt_countP_of_imp_of_exists
  · intro p _ hp; exact hle p.1 p.2 hp
  · have hex : ∃ f i, σ f i ≠ τ f i := Classical.byContradiction fun h =>
      hne (funext fun f => funext fun i =>
        Classical.byContradiction fun hfi => h ⟨f, i, hfi⟩)
    obtain ⟨f, i, hfi⟩ := hex
    refine ⟨(f, i), mem_cells f i, ?_⟩
    cases hσ : σ f i <;> cases hτ : τ f i
    · exact absurd (hσ.trans hτ.symm) hfi
    · exact ⟨rfl, rfl⟩
    · exact absurd (hle f i hσ) (by simp [hτ])
    · exact absurd (hσ.trans hτ.symm) hfi

/-- Iterates of a monotone map from a postfixpoint ascend. -/
theorem iter_ascending_of_postfixpoint {n m : Nat} {G : Transfer n m} (hmono : Monotone G)
    {x : Summ n m} (hx : Le x (G x)) : ∀ k, Le (iter G k x) (iter G (k + 1) x)
  | 0 => hx
  | k + 1 => by
      rw [iter_succ' G k x, iter_succ' G (k + 1) x]
      exact hmono _ _ (iter_ascending_of_postfixpoint hmono hx k)

/-- Iterates of a monotone map from a prefixpoint descend. -/
theorem iter_descending_of_prefixpoint {n m : Nat} {G : Transfer n m} (hmono : Monotone G)
    {x : Summ n m} (hx : Le (G x) x) : ∀ k, Le (iter G (k + 1) x) (iter G k x)
  | 0 => hx
  | k + 1 => by
      rw [iter_succ' G k x, iter_succ' G (k + 1) x]
      exact hmono _ _ (iter_descending_of_prefixpoint hmono hx k)

/-- An ascending iteration chain is fixed after `n * m` rounds (counting set bits). -/
theorem iter_fixed_at_height_of_ascending {n m : Nat} {G : Transfer n m} {x : Summ n m}
    (hasc : ∀ k, Le (iter G k x) (iter G (k + 1) x)) :
    G (iter G (n * m) x) = iter G (n * m) x := by
  have inv : ∀ k, G (iter G k x) = iter G k x ∨ k ≤ bitCount (iter G k x) := by
    intro k
    induction k with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ k ih =>
        by_cases hfix : G (iter G k x) = iter G k x
        · left; rw [iter_succ', hfix]; exact hfix
        · right
          have hk := ih.resolve_left hfix
          have hlt := bitCount_lt_of_le_of_ne (hasc k)
            (by rw [iter_succ']; exact fun e => hfix e.symm)
          omega
  apply Classical.byContradiction
  intro hfix
  have hk := (inv (n * m)).resolve_left hfix
  have hlt := bitCount_lt_of_le_of_ne (hasc (n * m))
    (by rw [iter_succ']; exact fun e => hfix e.symm)
  have hle := bitCount_le (iter G (n * m + 1) x)
  omega

/-- A descending iteration chain is fixed after `n * m` rounds (counting set bits). -/
theorem iter_fixed_at_height_of_descending {n m : Nat} {G : Transfer n m} {x : Summ n m}
    (hdesc : ∀ k, Le (iter G (k + 1) x) (iter G k x)) :
    G (iter G (n * m) x) = iter G (n * m) x := by
  have inv : ∀ k, G (iter G k x) = iter G k x ∨ k + bitCount (iter G k x) ≤ n * m := by
    intro k
    induction k with
    | zero => exact Or.inr (by have := bitCount_le x; simp only [iter]; omega)
    | succ k ih =>
        by_cases hfix : G (iter G k x) = iter G k x
        · left; rw [iter_succ', hfix]; exact hfix
        · right
          have hk := ih.resolve_left hfix
          have hlt := bitCount_lt_of_le_of_ne (hdesc k) (by rw [iter_succ']; exact hfix)
          omega
  apply Classical.byContradiction
  intro hfix
  have hk := (inv (n * m)).resolve_left hfix
  have hlt := bitCount_lt_of_le_of_ne (hdesc (n * m)) (by rw [iter_succ']; exact hfix)
  omega

/-! ## Two families of monotone transfers (used by the examples) -/

/-- Disjunctive transfer with unary-premise rules: bit `i` of `f` holds if it is a seed
(`c f i`) or if some single dependency bit `(g, j)` with `d f i g j` holds.  Every rule
has at most one premise, so these transfers preserve joins (they are additive);
multi-premise Horn clauses such as `σ g₁ j₁ ∧ σ g₂ j₂ → σ f i` are monotone but are not
of this form.  Least fixpoints of such transfers are reachability-style facts. -/
def disjT {n m : Nat} (c : Fin n → Fin m → Bool) (d : Fin n → Fin m → Fin n → Fin m → Bool) :
    Transfer n m :=
  fun σ f i => c f i || (List.finRange n).any fun g => (List.finRange m).any fun j =>
    d f i g j && σ g j

/-- Conjunctive transfer: bit `i` of `f` holds if it is allowed by `c` and every dependency
bit holds.  Greatest fixpoints of such transfers are safety-invariant-style facts. -/
def conjT {n m : Nat} (c : Fin n → Fin m → Bool) (d : Fin n → Fin m → Fin n → Fin m → Bool) :
    Transfer n m :=
  fun σ f i => c f i && (List.finRange n).all fun g => (List.finRange m).all fun j =>
    !d f i g j || σ g j

theorem disjT_monotone {n m : Nat} (c : Fin n → Fin m → Bool)
    (d : Fin n → Fin m → Fin n → Fin m → Bool) : Monotone (disjT c d) := by
  intro σ τ h f i hf
  simp only [disjT, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    List.mem_finRange, true_and] at hf ⊢
  rcases hf with hf | ⟨g, j, hd, hσ⟩
  · exact Or.inl hf
  · exact Or.inr ⟨g, j, hd, h g j hσ⟩

theorem conjT_monotone {n m : Nat} (c : Fin n → Fin m → Bool)
    (d : Fin n → Fin m → Fin n → Fin m → Bool) : Monotone (conjT c d) := by
  intro σ τ h f i hf
  simp only [conjT, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.mem_finRange, true_implies] at hf ⊢
  refine ⟨hf.1, fun g j => ?_⟩
  rcases hf.2 g j with hd | hσ
  · exact Or.inl hd
  · exact Or.inr (h g j hσ)

theorem disjT_respectsCalls {n m : Nat} {E : Graph n} {c : Fin n → Fin m → Bool}
    {d : Fin n → Fin m → Fin n → Fin m → Bool}
    (hd : ∀ f i g j, d f i g j = true → E f g = true) : RespectsCalls E (disjT c d) := by
  intro σ τ f h
  funext i
  have key : ∀ g j, (d f i g j && σ g j) = (d f i g j && τ g j) := by
    intro g j
    cases hdg : d f i g j
    · rfl
    · simp [h g (hd f i g j hdg)]
  simp only [disjT, key]

theorem conjT_respectsCalls {n m : Nat} {E : Graph n} {c : Fin n → Fin m → Bool}
    {d : Fin n → Fin m → Fin n → Fin m → Bool}
    (hd : ∀ f i g j, d f i g j = true → E f g = true) : RespectsCalls E (conjT c d) := by
  intro σ τ f h
  funext i
  have key : ∀ g j, (!d f i g j || σ g j) = (!d f i g j || τ g j) := by
    intro g j
    cases hdg : d f i g j
    · rfl
    · simp [h g (hd f i g j hdg)]
  simp only [conjT, key]

/-! ## Fixture transfers -/

/-- On `gPath` (`0 → 1`): `F 1 = {0}`, `F 0 = σ 1`.  Least fixpoint: everything. -/
def chainLfpT : Transfer 2 1 :=
  disjT (fun f _ => decide (f.val = 1)) (fun f _ g _ => decide (f.val = 0 ∧ g.val = 1))

/-- On `gPath`: `F 1 = ∅`, `F 0 = σ 1`.  Greatest fixpoint: nothing. -/
def chainGfpT : Transfer 2 1 :=
  conjT (fun f _ => decide (f.val = 0)) (fun f _ g _ => decide (f.val = 0 ∧ g.val = 1))

/-- On `gLoop`: the identity equation `σ 0 = σ 0` (least fixpoint `bot`, greatest `top`). -/
def idT : Transfer 1 1 := disjT (fun _ _ => false) (fun _ i _ j => decide (i = j))

/-- On `gLoop`: negation, which is not monotone and has no fixpoint. -/
def negT : Transfer 1 1 := fun σ f i => !σ f i

/-- Constant `top` (reads nothing). -/
def topT {n m : Nat} : Transfer n m := fun _ => top

theorem chainLfpT_monotone : Monotone chainLfpT := disjT_monotone _ _
theorem chainGfpT_monotone : Monotone chainGfpT := conjT_monotone _ _
theorem idT_monotone : Monotone idT := disjT_monotone _ _

theorem chainLfpT_respectsCalls : RespectsCalls gPath chainLfpT :=
  disjT_respectsCalls (by decide)
theorem chainGfpT_respectsCalls : RespectsCalls gPath chainGfpT :=
  conjT_respectsCalls (by decide)
theorem idT_respectsCalls : RespectsCalls gLoop idT := disjT_respectsCalls (by decide)

theorem negT_respectsCalls : RespectsCalls gLoop negT := by
  intro σ τ f h
  have : σ f = τ f := h f rfl
  funext i; simp [negT, this]

theorem topT_monotone {n m : Nat} : Monotone (topT (n := n) (m := m)) :=
  fun _ _ _ => Le.refl _

theorem topT_respectsCalls {n m : Nat} (E : Graph n) : RespectsCalls E (topT (m := m)) :=
  fun _ _ _ _ => rfl

theorem negT_no_fixpoint (σ : Summ 1 1) : negT σ ≠ σ := by
  intro h
  have := congrFun (congrFun h 0) 0
  cases hσ : σ 0 0 <;> simp_all [negT]

-- `Le`: positive and negative examples.
example : Le (bot : Summ 2 1) top := bot_le _
example : ¬ Le (top : Summ 2 1) bot := by decide

-- `Monotone`: positive and negative examples.
example : Monotone chainLfpT := chainLfpT_monotone
theorem not_monotone_negT : ¬ Monotone negT := by
  intro h
  have := h bot top (bot_le _) 0 0
  simp [negT, bot, top] at this

-- `RespectsCalls`: positive and negative examples.
example : RespectsCalls gPath chainLfpT := chainLfpT_respectsCalls
/-- On the call-free graph, `chainLfpT` reads a non-callee. -/
theorem not_respectsCalls_gEmpty_chainLfpT : ¬ RespectsCalls gEmpty chainLfpT := by
  intro h
  have := h (fun f _ => decide (f.val = 1)) bot 0 (fun g e => by simp [gEmpty] at e)
  have := congrFun this 0
  revert this; decide

-- `IsLeastFixpoint` / `IsGreatestFixpoint`: positive and negative examples.
theorem isLeastFixpoint_chainLfpT_top : IsLeastFixpoint chainLfpT top := by
  have h := isLeastFixpoint_of_iter_fixed chainLfpT_monotone (k := 2) (by decide)
  have e : iter chainLfpT 2 bot = top := by decide
  rw [e] at h; exact h

theorem isGreatestFixpoint_chainGfpT_bot : IsGreatestFixpoint chainGfpT bot := by
  have h := isGreatestFixpoint_of_iter_fixed chainGfpT_monotone (k := 2) (by decide)
  have e : iter chainGfpT 2 top = bot := by decide
  rw [e] at h; exact h

theorem isLeastFixpoint_idT_bot : IsLeastFixpoint idT bot :=
  isLeastFixpoint_of_iter_fixed (k := 0) idT_monotone (by decide)
theorem isGreatestFixpoint_idT_top : IsGreatestFixpoint idT top :=
  isGreatestFixpoint_of_iter_fixed (k := 0) idT_monotone (by decide)

theorem not_isLeastFixpoint_idT_top : ¬ IsLeastFixpoint idT top := fun h =>
  absurd (h.2 bot (by decide)) (by decide)
theorem not_isGreatestFixpoint_idT_bot : ¬ IsGreatestFixpoint idT bot := fun h =>
  absurd (h.2 top (by decide)) (by decide)

end Toy.Scc
