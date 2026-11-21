import ToyDataflow.CFG

/-!
# The diamond CFG and the characterization of MFP = MOP on diamonds

`diamond a g h f` is the five-node CFG

```
        0 (entry, value a, transfer id)
       / \
      1   2        transfers g and h (the two branches)
       \ /
        3          join node, transfer f
        |
        4          exit (its transfer is irrelevant)
```

MFP and MOP always agree at nodes 0–3; at node 4 MFP is `f (g a ⊔ h a)` and MOP
is `f (g a) ⊔ f (h a)` (`⊔` is `L.join`).

The entry transfer is fixed to `id`, whatever the family `F` of transfers in
`DiamondExact`; the branches are single nodes. Results about `DiamondExact` say
nothing about diamonds whose entry transfer or branch chains lie outside this
shape.
-/

namespace Toy.Dataflow

variable {α : Type}

/-- The diamond CFG with initial value `a`, branch transfers `g`, `h`, and
join-node transfer `f`. -/
def diamond (a : α) (g h f : α → α) : CFG 5 α where
  edges := [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]
  entry := 0
  init := a
  f := fun v => if v = 1 then g else if v = 2 then h else if v = 3 then f else id

/-- The explicit least solution of the diamond (for monotone transfers). -/
def diamondSol (L : Lat α) (a : α) (g h f : α → α) : Fin 5 → α :=
  fun v => if v = 3 then L.join (g a) (h a) else if v = 4 then f (L.join (g a) (h a)) else a

/-- The explicit MOP values of the diamond. -/
def diamondMOP (L : Lat α) (a : α) (g h f : α → α) : Fin 5 → α :=
  fun v => if v = 3 then L.join (g a) (h a) else if v = 4 then L.join (f (g a)) (f (h a)) else a

section paths

variable (a : α) (g h f : α → α)

@[simp] theorem diamond_entry : (diamond a g h f).entry = 0 := rfl
@[simp] theorem diamond_init : (diamond a g h f).init = a := rfl
@[simp] theorem diamond_f0 : (diamond a g h f).f 0 = id := rfl
@[simp] theorem diamond_f1 : (diamond a g h f).f 1 = g := rfl
@[simp] theorem diamond_f2 : (diamond a g h f).f 2 = h := rfl
@[simp] theorem diamond_f3 : (diamond a g h f).f 3 = f := rfl

theorem diamond_edges_mem (u w : Fin 5) : (u, w) ∈ (diamond a g h f).edges ↔
    (u = 0 ∧ w = 1) ∨ (u = 0 ∧ w = 2) ∨ (u = 1 ∧ w = 3) ∨ (u = 2 ∧ w = 3) ∨
      (u = 3 ∧ w = 4) := by
  simp [diamond]

theorem diamond_pathVals_zero (b : α) : pathVals (diamond a g h f) 0 b ↔ b = a := by
  rw [pathVals_iff]; simp [diamond_edges_mem]

theorem diamond_pathVals_one (b : α) : pathVals (diamond a g h f) 1 b ↔ b = a := by
  rw [pathVals_iff]; simp [diamond_edges_mem, diamond_pathVals_zero]

theorem diamond_pathVals_two (b : α) : pathVals (diamond a g h f) 2 b ↔ b = a := by
  rw [pathVals_iff]; simp [diamond_edges_mem, diamond_pathVals_zero]

theorem diamond_pathVals_three (b : α) :
    pathVals (diamond a g h f) 3 b ↔ b = g a ∨ b = h a := by
  rw [pathVals_iff]
  simp [diamond_edges_mem, diamond_pathVals_one, diamond_pathVals_two]

theorem diamond_pathVals_four (b : α) :
    pathVals (diamond a g h f) 4 b ↔ b = f (g a) ∨ b = f (h a) := by
  rw [pathVals_iff]
  simp [diamond_edges_mem, diamond_pathVals_three, or_and_right, exists_or]

end paths

theorem fin5_cases (v : Fin 5) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by
  revert v; decide

/-- Every node of the diamond is reachable from the entry. -/
theorem diamond_allReachable (a : α) (g h f : α → α) : AllReachable (diamond a g h f) := by
  intro v
  rw [reachable_iff_exists_pathVals]
  rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl
  · exact ⟨a, (diamond_pathVals_zero a g h f a).2 rfl⟩
  · exact ⟨a, (diamond_pathVals_one a g h f a).2 rfl⟩
  · exact ⟨a, (diamond_pathVals_two a g h f a).2 rfl⟩
  · exact ⟨g a, (diamond_pathVals_three a g h f _).2 (Or.inl rfl)⟩
  · exact ⟨f (g a), (diamond_pathVals_four a g h f _).2 (Or.inl rfl)⟩

/-- The MOP values of the diamond (no hypothesis on the transfers). -/
theorem diamond_isMOPAt {L : Lat α} (hL : L.IsJSL) (a : α) (g h f : α → α) (v : Fin 5) :
    IsMOPAt L (diamond a g h f) v (diamondMOP L a g h f v) := by
  unfold IsMOPAt
  rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl
  · rw [show pathVals (diamond a g h f) 0 = fun b => b = a from
      funext fun b => propext (diamond_pathVals_zero a g h f b)]
    exact Lat.isLUB_singleton hL a
  · rw [show pathVals (diamond a g h f) 1 = fun b => b = a from
      funext fun b => propext (diamond_pathVals_one a g h f b)]
    exact Lat.isLUB_singleton hL a
  · rw [show pathVals (diamond a g h f) 2 = fun b => b = a from
      funext fun b => propext (diamond_pathVals_two a g h f b)]
    exact Lat.isLUB_singleton hL a
  · rw [show pathVals (diamond a g h f) 3 = fun b => b = g a ∨ b = h a from
      funext fun b => propext (diamond_pathVals_three a g h f b)]
    exact Lat.isLUB_pair hL _ _
  · rw [show pathVals (diamond a g h f) 4 = fun b => b = f (g a) ∨ b = f (h a) from
      funext fun b => propext (diamond_pathVals_four a g h f b)]
    exact Lat.isLUB_pair hL _ _

theorem diamondSol_isSolution {L : Lat α} (hL : L.IsJSL) (a : α) (g h f : α → α) :
    IsSolution L (diamond a g h f) (diamondSol L a g h f) := by
  refine ⟨by simpa [diamond, diamondSol] using hL.refl a, ?_⟩
  intro u w huw
  simp only [diamond, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at huw
  rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
  · simpa [diamond, diamondSol] using hL.refl a
  · simpa [diamond, diamondSol] using hL.refl a
  · simpa [diamond, diamondSol] using Lat.le_join_left hL (g a) (h a)
  · simpa [diamond, diamondSol] using Lat.le_join_right hL (g a) (h a)
  · simpa [diamond, diamondSol] using hL.refl (f (L.join (g a) (h a)))
  · exact h.elim

/-- With monotone transfers, `diamondSol` is the least solution of the diamond. -/
theorem diamondSol_isLeastSolution_of_monotone {L : Lat α} (hL : L.IsJSL) (a : α)
    {g h f : α → α} (hg : Monotone L g) (hh : Monotone L h) (hf : Monotone L f) :
    IsLeastSolution L (diamond a g h f) (diamondSol L a g h f) := by
  refine ⟨diamondSol_isSolution hL a g h f, ?_⟩
  intro y ⟨hy0, hy⟩
  have e01 : (0, 1) ∈ (diamond a g h f).edges := by simp [diamond]
  have e02 : (0, 2) ∈ (diamond a g h f).edges := by simp [diamond]
  have e13 : (1, 3) ∈ (diamond a g h f).edges := by simp [diamond]
  have e23 : (2, 3) ∈ (diamond a g h f).edges := by simp [diamond]
  have e34 : (3, 4) ∈ (diamond a g h f).edges := by simp [diamond]
  have h0 : L.le a (y 0) := hy0
  have h1 : L.le a (y 1) := hL.trans _ _ _ h0 (by simpa [diamond] using hy 0 1 e01)
  have h2 : L.le a (y 2) := hL.trans _ _ _ h0 (by simpa [diamond] using hy 0 2 e02)
  have h3 : L.le (L.join (g a) (h a)) (y 3) :=
    Lat.join_le hL (hL.trans _ _ _ (hg _ _ h1) (by simpa [diamond] using hy 1 3 e13))
      (hL.trans _ _ _ (hh _ _ h2) (by simpa [diamond] using hy 2 3 e23))
  have h4 : L.le (f (L.join (g a) (h a))) (y 4) :=
    hL.trans _ _ _ (hf _ _ h3) (by simpa [diamond] using hy 3 4 e34)
  intro v
  rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl
  · simpa [diamondSol] using h0
  · simpa [diamondSol] using h1
  · simpa [diamondSol] using h2
  · simpa [diamondSol] using h3
  · simpa [diamondSol] using h4

/-- Any least solution of the diamond equals `diamondSol` (no monotonicity needed:
the least solution is squeezed between the equations and `diamondSol`). -/
theorem diamond_isLeastSolution_eq {L : Lat α} (hL : L.IsJSL) (a : α) (g h f : α → α)
    {x : Fin 5 → α} (hx : IsLeastSolution L (diamond a g h f) x) :
    x = diamondSol L a g h f := by
  have hle := hx.2 _ (diamondSol_isSolution hL a g h f)
  obtain ⟨hx0, hxe⟩ := hx.1
  have e01 : (0, 1) ∈ (diamond a g h f).edges := by simp [diamond]
  have e02 : (0, 2) ∈ (diamond a g h f).edges := by simp [diamond]
  have e13 : (1, 3) ∈ (diamond a g h f).edges := by simp [diamond]
  have e23 : (2, 3) ∈ (diamond a g h f).edges := by simp [diamond]
  have e34 : (3, 4) ∈ (diamond a g h f).edges := by simp [diamond]
  have x0 : x 0 = a := hL.antisymm _ _ (by simpa [diamondSol] using hle 0) hx0
  have x1 : x 1 = a := hL.antisymm _ _ (by simpa [diamondSol] using hle 1)
    (by simpa [diamond, x0] using hxe 0 1 e01)
  have x2 : x 2 = a := hL.antisymm _ _ (by simpa [diamondSol] using hle 2)
    (by simpa [diamond, x0] using hxe 0 2 e02)
  have x3 : x 3 = L.join (g a) (h a) := hL.antisymm _ _ (by simpa [diamondSol] using hle 3)
    (Lat.join_le hL (by simpa [diamond, x1] using hxe 1 3 e13)
      (by simpa [diamond, x2] using hxe 2 3 e23))
  have x4 : x 4 = f (L.join (g a) (h a)) := hL.antisymm _ _ (by simpa [diamondSol] using hle 4)
    (by simpa [diamond, x3] using hxe 3 4 e34)
  funext v
  rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl <;> simp [diamondSol, *]

/-- On the diamond, the least solution is MOP at every node iff the join-node
transfer distributes over the particular pair of branch outputs `(g a, h a)`. -/
theorem diamond_isMOPAt_iff {L : Lat α} (hL : L.IsJSL) (a : α) (g h f : α → α)
    {x : Fin 5 → α} (hx : IsLeastSolution L (diamond a g h f) x) :
    (∀ v, IsMOPAt L (diamond a g h f) v (x v)) ↔
      f (L.join (g a) (h a)) = L.join (f (g a)) (f (h a)) := by
  rw [diamond_isLeastSolution_eq hL a g h f hx]
  constructor
  · intro H
    have := IsMOPAt.unique hL (H 4) (diamond_isMOPAt hL a g h f 4)
    simpa [diamondSol, diamondMOP] using this
  · intro heq v
    have hv := diamond_isMOPAt hL a g h f v
    rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl <;>
      simpa [diamondSol, diamondMOP, heq] using hv

/-! ## The characterization over a family of transfer functions -/

/-- MFP = MOP holds at every node of every diamond whose initial value lies in `I`
and whose three transfers `g`, `h`, `f` are drawn from the family `F`. -/
def DiamondExact (L : Lat α) (I : α → Prop) (F : (α → α) → Prop) : Prop :=
  ∀ a g h f, I a → F g → F h → F f →
    ∀ x, IsLeastSolution L (diamond a g h f) x → ∀ v, IsMOPAt L (diamond a g h f) v (x v)

/-- Every `f ∈ F` distributes over every *realizable* pair: a pair `(g a, h a)` of
branch outputs with `g, h ∈ F` and `a ∈ I`. Weaker than distributivity over all
pairs. -/
def DistributiveOnRealizable (L : Lat α) (I : α → Prop) (F : (α → α) → Prop) : Prop :=
  ∀ a g h f, I a → F g → F h → F f → f (L.join (g a) (h a)) = L.join (f (g a)) (f (h a))

/-- Characterization, sufficiency (no monotonicity needed). -/
theorem diamondExact_of_distributiveOnRealizable {L : Lat α} (hL : L.IsJSL)
    {I : α → Prop} {F : (α → α) → Prop} (hd : DistributiveOnRealizable L I F) :
    DiamondExact L I F :=
  fun a g h f ha hg hh hf _ hx =>
    (diamond_isMOPAt_iff hL a g h f hx).2 (hd a g h f ha hg hh hf)

/-- Characterization, necessity (needs every member of `F` monotone, so that each
diamond built from `F` has a least solution). -/
theorem distributiveOnRealizable_of_diamondExact_of_monotone {L : Lat α} (hL : L.IsJSL)
    {I : α → Prop} {F : (α → α) → Prop} (hmono : ∀ φ, F φ → Monotone L φ)
    (he : DiamondExact L I F) : DistributiveOnRealizable L I F := by
  intro a g h f ha hg hh hf
  have hx := diamondSol_isLeastSolution_of_monotone hL a (hmono g hg) (hmono h hh) (hmono f hf)
  exact (diamond_isMOPAt_iff hL a g h f hx).1 (he a g h f ha hg hh hf _ hx)

/-- Characterization (diamond): for a family `F` of monotone transfer functions
and a set `I` of initial values, MFP = MOP on every diamond built from `F` and `I`
iff every `f ∈ F` distributes over every realizable pair of branch outputs. -/
theorem diamondExact_iff_distributiveOnRealizable_of_monotone {L : Lat α} (hL : L.IsJSL)
    (I : α → Prop) (F : (α → α) → Prop) (hmono : ∀ φ, F φ → Monotone L φ) :
    DiamondExact L I F ↔ DistributiveOnRealizable L I F :=
  ⟨distributiveOnRealizable_of_diamondExact_of_monotone hL hmono,
    diamondExact_of_distributiveOnRealizable hL⟩

/-- When `F` consists of monotone functions, contains every constant function, and
`I` is non-empty, every pair is realizable, so the characterization becomes full
distributivity of every member. -/
theorem diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty {L : Lat α}
    (hL : L.IsJSL)
    (I : α → Prop) (F : (α → α) → Prop) (hmono : ∀ φ, F φ → Monotone L φ)
    (hconst : ∀ b, F (fun _ => b)) (hI : ∃ a, I a) :
    DiamondExact L I F ↔ ∀ f, F f → Distributive L f := by
  rw [diamondExact_iff_distributiveOnRealizable_of_monotone hL I F hmono]
  constructor
  · intro hd f hf b c
    obtain ⟨a, ha⟩ := hI
    exact hd a (fun _ => b) (fun _ => c) f ha (hconst b) (hconst c) hf
  · intro hd a g h f _ _ _ hf
    exact hd f hf _ _

/-- A one-element family always satisfies the realizable-pair condition (both
branches produce the same value), whether or not its member is distributive. -/
theorem distributiveOnRealizable_singleton {L : Lat α} (hL : L.IsJSL) (I : α → Prop)
    (φ : α → α) : DistributiveOnRealizable L I (fun ψ => ψ = φ) := by
  rintro a g h f _ rfl rfl rfl
  rw [Lat.join_self hL, Lat.join_self hL]

/-- Under the ascending chain condition, if `F` contains every constant and `I` is
non-empty, exactness on every diamond forces every member of `F` to be monotone.
(A non-monotone member has a maximal witness `u < v` with `f u ≰ f v`; the diamond
with constant branches `u`, `v` then has a least solution, and exactness there
gives `f v = f u ⊔ f v`.) -/
theorem monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty {L : Lat α}
    (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
    {I : α → Prop} {F : (α → α) → Prop}
    (hconst : ∀ b, F (fun _ => b)) (hI : ∃ a, I a)
    (he : DiamondExact L I F) : ∀ f, F f → Monotone L f := by
  classical
  intro f hf
  apply Classical.byContradiction
  intro hnot
  have hex : ∃ u v, L.lt u v ∧ ¬ L.le (f u) (f v) := by
    apply Classical.byContradiction
    intro hno
    apply hnot
    intro u v huv
    by_cases heq : u = v
    · subst heq; exact hL.refl _
    · apply Classical.byContradiction
      intro hfn
      exact hno ⟨u, v, ⟨huv, heq⟩, hfn⟩
  obtain ⟨u0, v0, hlt0, hfn0⟩ := hex
  let Bad : α → Prop := fun u => ∃ v, L.lt u v ∧ ¬ L.le (f u) (f v)
  have hwf : WellFounded (fun a b : α => L.lt b a) := hacc
  have hmin : ∃ m, Bad m ∧ ∀ b, Bad b → ¬ L.lt m b := by
    refine hwf.induction (C := fun a => Bad a → ∃ m, Bad m ∧ ∀ b, Bad b → ¬ L.lt m b) u0 ?_
      ⟨v0, hlt0, hfn0⟩
    intro a ih ha
    by_cases h : ∃ b, Bad b ∧ L.lt a b
    · obtain ⟨b, hb, hr⟩ := h
      exact ih b hr hb
    · exact ⟨a, ha, fun b hb hr => h ⟨b, hb, hr⟩⟩
  obtain ⟨u, ⟨v, hlt, hfn⟩, hmax⟩ := hmin
  have hnbad : ¬ Bad v := fun hbad => hmax v hbad hlt
  have hfv : ∀ z, L.le v z → L.le (f v) (f z) := by
    intro z hvz
    by_cases heqv : v = z
    · subst heqv; exact hL.refl _
    · apply Classical.byContradiction
      intro hfz
      exact hnbad ⟨z, ⟨hvz, heqv⟩, hfz⟩
  obtain ⟨a0, ha0⟩ := hI
  have hleast : IsLeastSolution L (diamond a0 (fun _ => u) (fun _ => v) f)
      (diamondSol L a0 (fun _ => u) (fun _ => v) f) := by
    refine ⟨diamondSol_isSolution hL a0 _ _ _, fun y hy w => ?_⟩
    have e01 : ((0 : Fin 5), (1 : Fin 5)) ∈ (diamond a0 (fun _ => u) (fun _ => v) f).edges := by
      simp [diamond]
    have e02 : ((0 : Fin 5), (2 : Fin 5)) ∈ (diamond a0 (fun _ => u) (fun _ => v) f).edges := by
      simp [diamond]
    have e13 : ((1 : Fin 5), (3 : Fin 5)) ∈ (diamond a0 (fun _ => u) (fun _ => v) f).edges := by
      simp [diamond]
    have e23 : ((2 : Fin 5), (3 : Fin 5)) ∈ (diamond a0 (fun _ => u) (fun _ => v) f).edges := by
      simp [diamond]
    have e34 : ((3 : Fin 5), (4 : Fin 5)) ∈ (diamond a0 (fun _ => u) (fun _ => v) f).edges := by
      simp [diamond]
    have h0 : L.le a0 (y 0) := hy.1
    have h1 : L.le a0 (y 1) := hL.trans _ _ _ h0 (by simpa [diamond] using hy.2 0 1 e01)
    have h2 : L.le a0 (y 2) := hL.trans _ _ _ h0 (by simpa [diamond] using hy.2 0 2 e02)
    have hu3 : L.le u (y 3) := by simpa [diamond] using hy.2 1 3 e13
    have hv3 : L.le v (y 3) := by simpa [diamond] using hy.2 2 3 e23
    have hj3 : L.le (L.join u v) (y 3) := Lat.join_le hL hu3 hv3
    have hjv : L.join u v = v := Lat.join_eq_right_of_le hL hlt.1
    have h4 : L.le (f (L.join u v)) (y 4) := by
      rw [hjv]
      exact hL.trans _ _ _ (hfv (y 3) hv3) (by simpa [diamond] using hy.2 3 4 e34)
    rcases fin5_cases w with rfl | rfl | rfl | rfl | rfl
    · simpa [diamondSol] using h0
    · simpa [diamondSol] using h1
    · simpa [diamondSol] using h2
    · simpa [diamondSol] using hj3
    · simpa [diamondSol] using h4
  have hdist := (diamond_isMOPAt_iff hL a0 (fun _ => u) (fun _ => v) f hleast).1
    (he a0 (fun _ => u) (fun _ => v) f ha0 (hconst u) (hconst v) hf _ hleast)
  rw [Lat.join_eq_right_of_le hL hlt.1] at hdist
  apply hfn
  rw [hdist]
  exact Lat.le_join_left hL (f u) (f v)

/-- Constant-closed characterization without assuming monotonicity, under the
ascending chain condition: if `F` contains every constant and `I` is non-empty,
MFP = MOP on every diamond built from `F` and `I` iff every member of `F` is
distributive. -/
theorem diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty {L : Lat α}
    (hL : L.IsJSL) (hacc : L.AscendingChainCondition)
    (I : α → Prop) (F : (α → α) → Prop)
    (hconst : ∀ b, F (fun _ => b)) (hI : ∃ a, I a) :
    DiamondExact L I F ↔ ∀ f, F f → Distributive L f := by
  constructor
  · intro he
    have hmono := monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty hL hacc hconst hI he
    exact (diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty hL I F hmono
      hconst hI).1 he
  · intro hd
    exact diamondExact_of_distributiveOnRealizable hL (fun _ _ _ f _ _ _ hf => hd f hf _ _)

end Toy.Dataflow
