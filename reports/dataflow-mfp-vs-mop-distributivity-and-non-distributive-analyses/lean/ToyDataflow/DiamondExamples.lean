import ToyDataflow.Examples

/-!
# Further witnesses for the diamond characterization

* tightness of monotonicity (and of the ascending chain condition) in the
  constant-closed corollaries;
* non-vacuity of the constant-closed corollaries;
* the role of the fixed entry transfer `id`;
* diamond exactness does not extend to two-path acyclic CFGs with two transfers
  per branch.
-/

namespace Toy.Dataflow

/-- Negation on `Int ∪ {⊥}` (strict). -/
def wbNeg : WithBotInt → WithBotInt
  | .bot => .bot
  | .val z => .val (-z)

/-- All constants plus negation. -/
def wbNegFamily : (WithBotInt → WithBotInt) → Prop :=
  fun φ => (∃ b, φ = fun _ => b) ∨ φ = wbNeg

/-- Counterexample for the constant-closed corollaries: on `Int ∪ {⊥}` (no ascending
chain condition), the family of all constants plus negation contains every constant,
has a non-empty set of initial values, and is exact on every diamond (each diamond
whose join node negates a non-`⊥` value has no least solution), although negation
is neither monotone nor distributive. So monotonicity cannot be dropped from
`diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty`, and the ascending
chain condition cannot be dropped from
`diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty`. -/
theorem diamondExact_const_mem_needs_monotone :
    withBotIntLat.IsJSL ∧ ¬ withBotIntLat.AscendingChainCondition ∧
    ¬ (∀ φ, wbNegFamily φ → Monotone withBotIntLat φ) ∧
    (∀ b, wbNegFamily (fun _ => b)) ∧
    (∃ a : WithBotInt, (fun _ => True) a) ∧
    DiamondExact withBotIntLat (fun _ => True) wbNegFamily ∧
    ¬ (∀ f, wbNegFamily f → Distributive withBotIntLat f) := by
  refine ⟨withBotIntLat_isJSL, withBotIntLat_not_acc, ?_, fun b => Or.inl ⟨b, rfl⟩,
    ⟨.bot, trivial⟩, ?_, ?_⟩
  · intro hm
    have h01 := hm wbNeg (Or.inr rfl) (.val 0) (.val 1) (by simp [withBotIntLat, WithBotInt.le])
    simp [wbNeg, withBotIntLat, WithBotInt.le] at h01
  · intro a g h f _ _ _ hf x hx
    rcases hf with ⟨b, rfl⟩ | rfl
    · exact (diamond_isMOPAt_iff withBotIntLat_isJSL a g h _ hx).2
        (Lat.join_self withBotIntLat_isJSL b).symm
    · cases hj : withBotIntLat.join (g a) (h a) with
      | bot =>
        have hga : g a = .bot := by
          have := hj ▸ Lat.le_join_left withBotIntLat_isJSL (g a) (h a)
          cases hg : g a <;> simp [withBotIntLat, WithBotInt.le, hg] at this
          rfl
        have hha : h a = .bot := by
          have := hj ▸ Lat.le_join_right withBotIntLat_isJSL (g a) (h a)
          cases hh : h a <;> simp [withBotIntLat, WithBotInt.le, hh] at this
          rfl
        exact (diamond_isMOPAt_iff withBotIntLat_isJSL a g h wbNeg hx).2
          (by simp [hga, hha, wbNeg, withBotIntLat, WithBotInt.join])
      | val m =>
        exfalso
        let y : Fin 5 → WithBotInt :=
          fun v => if v = 3 then .val (m + 1) else if v = 4 then .val (-(m + 1)) else a
        have hy : IsSolution withBotIntLat (diamond a g h wbNeg) y := by
          refine ⟨by simp [diamond, y]; exact withBotIntLat_isJSL.refl a, ?_⟩
          intro u w huw
          simp only [diamond, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at huw
          rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hbot
          · simpa [diamond, y] using withBotIntLat_isJSL.refl a
          · simpa [diamond, y] using withBotIntLat_isJSL.refl a
          · have h1 := hj ▸ Lat.le_join_left withBotIntLat_isJSL (g a) (h a)
            have h2 : withBotIntLat.le (.val m) (.val (m + 1)) := by
              simp [withBotIntLat, WithBotInt.le]; omega
            simpa [diamond, y] using withBotIntLat_isJSL.trans _ _ _ h1 h2
          · have h1 := hj ▸ Lat.le_join_right withBotIntLat_isJSL (g a) (h a)
            have h2 : withBotIntLat.le (.val m) (.val (m + 1)) := by
              simp [withBotIntLat, WithBotInt.le]; omega
            simpa [diamond, y] using withBotIntLat_isJSL.trans _ _ _ h1 h2
          · simpa [diamond, y, wbNeg] using withBotIntLat_isJSL.refl (.val (-(m + 1)))
          · exact hbot.elim
        have heq := diamond_isLeastSolution_eq withBotIntLat_isJSL a g h wbNeg hx
        have h4 := hx.2 y hy 4
        rw [heq] at h4
        simp only [diamondSol] at h4
        rw [hj] at h4
        simp [wbNeg, y, withBotIntLat, WithBotInt.le] at h4
        omega
  · intro hd
    have h := hd wbNeg (Or.inr rfl) (.val 0) (.val 1)
    simp [wbNeg, withBotIntLat, WithBotInt.join, Int.max_def] at h

/-- Non-vacuity of the constant-closed corollaries, with both sides true (all gen/kill
functions on `bvLat 1`, which include every constant) and both sides false (all
constants plus the constant-propagation family). -/
theorem diamondExact_const_mem_nonvacuous :
    ((bvLat 1).IsJSL ∧ (bvLat 1).AscendingChainCondition ∧
        (∀ φ, (∃ gen kill, φ = genKill gen kill) → Monotone (bvLat 1) φ) ∧
        (∀ b : Fin 1 → Bool, ∃ gen kill, (fun _ => b) = genKill gen kill) ∧
        (∃ a : Fin 1 → Bool, (fun _ => True) a) ∧
        DiamondExact (bvLat 1) (fun _ => True) (fun φ => ∃ gen kill, φ = genKill gen kill) ∧
        DistributiveOnRealizable (bvLat 1) (fun _ => True) (fun φ => ∃ gen kill, φ = genKill gen kill) ∧
        ∀ f, (∃ gen kill, f = genKill gen kill) → Distributive (bvLat 1) f) ∧
      (cpLat.IsJSL ∧ cpLat.AscendingChainCondition ∧
        (∀ φ, ((∃ b, φ = fun _ => b) ∨ cpFamily φ) → Monotone cpLat φ) ∧
        (∀ b : St, (∃ b', (fun _ : St => b) = fun _ => b') ∨ cpFamily (fun _ => b)) ∧
        (∃ a : St, (fun _ => True) a) ∧
        ¬ DiamondExact cpLat (fun _ => True) (fun φ => (∃ b, φ = fun _ => b) ∨ cpFamily φ) ∧
        ¬ DistributiveOnRealizable cpLat (fun _ => True) (fun φ => (∃ b, φ = fun _ => b) ∨ cpFamily φ) ∧
        ¬ ∀ f, ((∃ b, f = fun _ => b) ∨ cpFamily f) → Distributive cpLat f) := by
  refine ⟨⟨bvLat_isJSL 1, bvLat_acc 1, ?_, ?_, ⟨fun _ => false, trivial⟩, ?_, ?_, ?_⟩,
    ⟨cpLat_isJSL, cpLat_acc, ?_, fun b => Or.inl ⟨b, rfl⟩, ⟨⟨.bot, .bot, .bot⟩, trivial⟩, ?_, ?_,
      ?_⟩⟩
  · rintro φ ⟨gen, kill, rfl⟩
    exact monotone_of_distributive (bvLat_isJSL 1) (genKill_distributive gen kill)
  · intro b
    refine ⟨b, fun _ => true, ?_⟩
    funext a i
    simp [genKill]
  · refine diamondExact_of_distributiveOnRealizable (bvLat_isJSL 1) ?_
    rintro a g h f _ _ _ ⟨gen, kill, rfl⟩
    exact genKill_distributive gen kill _ _
  · rintro a g h f _ _ _ ⟨gen, kill, rfl⟩
    exact genKill_distributive gen kill _ _
  · rintro f ⟨gen, kill, rfl⟩; exact genKill_distributive gen kill
  · rintro φ (⟨b, rfl⟩ | rfl | rfl | rfl)
    · exact fun _ _ _ => cpLat_isJSL.refl _
    · exact assignYZ_monotone 1 2
    · exact assignYZ_monotone 2 1
    · exact assignXYZ_monotone
  · intro h
    have := h ⟨.top, .top, .top⟩ (assignYZ 1 2) (assignYZ 2 1) assignXYZ trivial
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
      _ (cpDiamond_isLeastSolution _) 4
    exact (cpDiamond_mfp_x_top_ne_mop_x_const3 _ (cpDiamond_isLeastSolution _)).2.2 this
  · intro h
    have := h ⟨.top, .top, .top⟩ (assignYZ 1 2) (assignYZ 2 1) assignXYZ trivial
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
    revert this; decide
  · intro h
    exact assignXYZ_not_distributive (h _ (Or.inr (Or.inr (Or.inr rfl))))

/-- The diamond with an arbitrary entry transfer `k` instead of `id`. -/
def diamondWithEntry {α : Type} (k : α → α) (a : α) (g h f : α → α) : CFG 5 α where
  edges := [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]
  entry := 0
  init := a
  f := fun v => if v = 0 then k else if v = 1 then g else if v = 2 then h else if v = 3 then f else id

/-- Members of the family used in `diamond_entry_id_matters`. -/
def bv3G (s : Fin 3 → Bool) : Fin 3 → Bool := fun i => decide (i = 0) && s 2
def bv3H (s : Fin 3 → Bool) : Fin 3 → Bool := fun i => decide (i = 1) && s 2
def bv3F (s : Fin 3 → Bool) : Fin 3 → Bool := fun _ => s 0 && s 1
def bv3Family : ((Fin 3 → Bool) → Fin 3 → Bool) → Prop :=
  fun φ => φ = bv3G ∨ φ = bv3H ∨ φ = bv3F

/-- The fixed entry transfer `id` matters: for a monotone family `F` on `bvLat 3` with
`id ∉ F`, the diamonds of `DiamondExact` (entry transfer `id`) are not all exact,
while every diamond whose entry transfer is also drawn from `F` is exact. So
`DiamondExact` is not the same as exactness on diamonds all of whose transfers
come from `F`. -/
theorem diamond_entry_id_matters :
    let I : (Fin 3 → Bool) → Prop := fun a => a = fun i => decide (i = 2)
    (∀ φ, bv3Family φ → Monotone (bvLat 3) φ) ∧
      ¬ DiamondExact (bvLat 3) I bv3Family ∧
      ∀ k a g h f, bv3Family k → I a → bv3Family g → bv3Family h → bv3Family f →
        ∀ x, IsLeastSolution (bvLat 3) (diamondWithEntry k a g h f) x →
          ∀ v, IsMOPAt (bvLat 3) (diamondWithEntry k a g h f) v (x v) := by
  intro I
  have hmono : ∀ φ, bv3Family φ → Monotone (bvLat 3) φ := by
    rintro φ (rfl | rfl | rfl) a b hab i hi
    · simp only [bv3G, Bool.and_eq_true] at hi ⊢
      exact ⟨hi.1, hab 2 hi.2⟩
    · simp only [bv3H, Bool.and_eq_true] at hi ⊢
      exact ⟨hi.1, hab 2 hi.2⟩
    · simp only [bv3F, Bool.and_eq_true] at hi ⊢
      exact ⟨hab 0 hi.1, hab 1 hi.2⟩
  refine ⟨hmono, fun hex => ?_, ?_⟩
  · have hls : IsLeastSolution (bvLat 3)
        (diamond (fun i => decide (i = 2)) bv3G bv3H bv3F)
        (diamondSol (bvLat 3) (fun i => decide (i = 2)) bv3G bv3H bv3F) :=
      diamondSol_isLeastSolution_of_monotone (bvLat_isJSL 3) _
        (hmono _ (Or.inl rfl)) (hmono _ (Or.inr (Or.inl rfl))) (hmono _ (Or.inr (Or.inr rfl)))
    have hmop := (diamond_isMOPAt_iff (bvLat_isJSL 3) _ _ _ _ hls).1
      (hex _ bv3G bv3H bv3F rfl (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) _ hls)
    have := congrFun hmop 0
    revert this; decide
  · intro k a g h f hk ha hg hh hf x hx v
    subst ha
    have hka2 : k (fun i => decide (i = 2)) 2 = false := by
      rcases hk with rfl | rfl | rfl <;> decide
    have hkill : ∀ φ, bv3Family φ → φ (k (fun i => decide (i = 2))) = fun _ => false := by
      rintro φ (rfl | rfl | rfl) <;> funext i
      · simp [bv3G, hka2]
      · simp [bv3H, hka2]
      · have hk01 : k (fun i => decide (i = 2)) 0 = false ∨ k (fun i => decide (i = 2)) 1 = false := by
          rcases hk with rfl | rfl | rfl <;> decide
        rcases hk01 with h0 | h1
        · simp [bv3F, h0]
        · simp [bv3F, h1]
    have hg0 : g (k (fun i => decide (i = 2))) = fun _ => false := hkill g hg
    have hh0 : h (k (fun i => decide (i = 2))) = fun _ => false := hkill h hh
    have hf0 : f (fun _ => false) = fun _ => false := by
      funext i
      rcases hf with rfl | rfl | rfl <;> simp [bv3G, bv3H, bv3F]
    let G := diamondWithEntry k (fun i => decide (i = 2)) g h f
    let ka := k (fun i => decide (i = 2))
    let sol : Fin 5 → Fin 3 → Bool := fun w =>
      if w = 0 then (fun i => decide (i = 2))
      else if w = 1 then ka
      else if w = 2 then ka
      else fun _ => false
    have hsol : IsSolution (bvLat 3) G sol := by
      refine ⟨(bvLat_isJSL 3).refl _, ?_⟩
      intro u w huw
      simp only [G, diamondWithEntry, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at huw
      rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hbot
      · exact (bvLat_isJSL 3).refl _
      · exact (bvLat_isJSL 3).refl _
      · simp [G, diamondWithEntry, sol, ka, hg0]; exact (bvLat_isJSL 3).refl _
      · simp [G, diamondWithEntry, sol, ka, hh0]; exact (bvLat_isJSL 3).refl _
      · simp [G, diamondWithEntry, sol, hf0]; exact (bvLat_isJSL 3).refl _
      · exact hbot.elim
    have hle := hx.2 sol hsol
    obtain ⟨hx0, hxe⟩ := hx.1
    have e01 : ((0 : Fin 5), (1 : Fin 5)) ∈ G.edges := by simp [G, diamondWithEntry]
    have e02 : ((0 : Fin 5), (2 : Fin 5)) ∈ G.edges := by simp [G, diamondWithEntry]
    have e13 : ((1 : Fin 5), (3 : Fin 5)) ∈ G.edges := by simp [G, diamondWithEntry]
    have e23 : ((2 : Fin 5), (3 : Fin 5)) ∈ G.edges := by simp [G, diamondWithEntry]
    have e34 : ((3 : Fin 5), (4 : Fin 5)) ∈ G.edges := by simp [G, diamondWithEntry]
    have x0 : x 0 = fun i => decide (i = 2) :=
      (bvLat_isJSL 3).antisymm _ _ (by simpa [sol] using hle 0) hx0
    have x1 : x 1 = ka :=
      (bvLat_isJSL 3).antisymm _ _ (by simpa [sol] using hle 1)
        (by simpa [G, diamondWithEntry, x0, ka] using hxe 0 1 e01)
    have x2 : x 2 = ka :=
      (bvLat_isJSL 3).antisymm _ _ (by simpa [sol] using hle 2)
        (by simpa [G, diamondWithEntry, x0, ka] using hxe 0 2 e02)
    have x3 : x 3 = fun _ => false :=
      (bvLat_isJSL 3).antisymm _ _ (by simpa [sol] using hle 3) ((bvLat_isJSL 3).bot_le _)
    have x4 : x 4 = fun _ => false :=
      (bvLat_isJSL 3).antisymm _ _ (by simpa [sol] using hle 4) ((bvLat_isJSL 3).bot_le _)
    have edges_mem : ∀ u w : Fin 5, (u, w) ∈ G.edges ↔
        (u = 0 ∧ w = 1) ∨ (u = 0 ∧ w = 2) ∨ (u = 1 ∧ w = 3) ∨ (u = 2 ∧ w = 3) ∨
          (u = 3 ∧ w = 4) := by
      intro u w; simp [G, diamondWithEntry]
    have gf0 : G.f 0 = k := rfl
    have gf1 : G.f 1 = g := rfl
    have gf2 : G.f 2 = h := rfl
    have gf3 : G.f 3 = f := rfl
    have ge0 : G.entry = 0 := rfl
    have gi0 : G.init = fun i => decide (i = 2) := rfl
    have pv0 : ∀ b, pathVals G 0 b ↔ b = fun i => decide (i = 2) := fun b => by
      rw [pathVals_iff]; simp [edges_mem, ge0, gi0]
    have pv1 : ∀ b, pathVals G 1 b ↔ b = ka := fun b => by
      rw [pathVals_iff]; simp [edges_mem, ge0, pv0, gf0, ka]
    have pv2 : ∀ b, pathVals G 2 b ↔ b = ka := fun b => by
      rw [pathVals_iff]; simp [edges_mem, ge0, pv0, gf0, ka]
    have pv3 : ∀ b, pathVals G 3 b ↔ b = fun _ => false := fun b => by
      rw [pathVals_iff]
      simp [edges_mem, ge0, pv1, pv2, gf1, gf2, ka, hg0, hh0]
    have pv4 : ∀ b, pathVals G 4 b ↔ b = fun _ => false := fun b => by
      rw [pathVals_iff]; simp [edges_mem, ge0, pv3, gf3, hf0]
    unfold IsMOPAt
    rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl
    · rw [x0, show pathVals G 0 = fun b => b = fun i => decide (i = 2) from funext fun b => propext (pv0 b)]
      exact Lat.isLUB_singleton (bvLat_isJSL 3) _
    · rw [x1, show pathVals G 1 = fun b => b = ka from funext fun b => propext (pv1 b)]
      exact Lat.isLUB_singleton (bvLat_isJSL 3) _
    · rw [x2, show pathVals G 2 = fun b => b = ka from funext fun b => propext (pv2 b)]
      exact Lat.isLUB_singleton (bvLat_isJSL 3) _
    · rw [x3, show pathVals G 3 = fun b => b = fun _ => false from funext fun b => propext (pv3 b)]
      exact Lat.isLUB_singleton (bvLat_isJSL 3) _
    · rw [x4, show pathVals G 4 = fun b => b = fun _ => false from funext fun b => propext (pv4 b)]
      exact Lat.isLUB_singleton (bvLat_isJSL 3) _

/-! ## Two transfers per branch -/

/-- A two-path acyclic CFG with two transfers on each branch:
`0 → 1 → 2 → 5`, `0 → 3 → 4 → 5`, `5 → 6`, with transfers `g1, g2` on the first
branch, `h1, h2` on the second, `f` at the join node 5, and `id` at nodes 0 and 6. -/
def diamond2 {α : Type} (a : α) (g1 g2 h1 h2 f : α → α) : CFG 7 α where
  edges := [(0, 1), (1, 2), (2, 5), (0, 3), (3, 4), (4, 5), (5, 6)]
  entry := 0
  init := a
  f := fun v => if v = 1 then g1 else if v = 2 then g2 else if v = 3 then h1 else
    if v = 4 then h2 else if v = 5 then f else id

/-- The explicit least solution of `diamond2` (for monotone transfers). -/
def diamond2Sol {α : Type} (L : Lat α) (a : α) (g1 g2 h1 h2 f : α → α) : Fin 7 → α :=
  fun v => if v = 2 then g1 a else if v = 4 then h1 a else
    if v = 5 then L.join (g2 (g1 a)) (h2 (h1 a)) else
    if v = 6 then f (L.join (g2 (g1 a)) (h2 (h1 a))) else a

theorem fin7_cases (v : Fin 7) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by
  revert v; decide

section diamond2

variable {α : Type} (a : α) (g1 g2 h1 h2 f : α → α)

@[simp] theorem diamond2_entry : (diamond2 a g1 g2 h1 h2 f).entry = 0 := rfl
@[simp] theorem diamond2_init : (diamond2 a g1 g2 h1 h2 f).init = a := rfl
@[simp] theorem diamond2_f0 : (diamond2 a g1 g2 h1 h2 f).f 0 = id := rfl
@[simp] theorem diamond2_f1 : (diamond2 a g1 g2 h1 h2 f).f 1 = g1 := rfl
@[simp] theorem diamond2_f2 : (diamond2 a g1 g2 h1 h2 f).f 2 = g2 := rfl
@[simp] theorem diamond2_f3 : (diamond2 a g1 g2 h1 h2 f).f 3 = h1 := rfl
@[simp] theorem diamond2_f4 : (diamond2 a g1 g2 h1 h2 f).f 4 = h2 := rfl
@[simp] theorem diamond2_f5 : (diamond2 a g1 g2 h1 h2 f).f 5 = f := rfl

theorem diamond2_edges_mem (u w : Fin 7) : (u, w) ∈ (diamond2 a g1 g2 h1 h2 f).edges ↔
    (u = 0 ∧ w = 1) ∨ (u = 1 ∧ w = 2) ∨ (u = 2 ∧ w = 5) ∨ (u = 0 ∧ w = 3) ∨
      (u = 3 ∧ w = 4) ∨ (u = 4 ∧ w = 5) ∨ (u = 5 ∧ w = 6) := by
  simp [diamond2]

theorem diamond2_pathVals_six (b : α) :
    pathVals (diamond2 a g1 g2 h1 h2 f) 6 b ↔ b = f (g2 (g1 a)) ∨ b = f (h2 (h1 a)) := by
  have p0 : ∀ b, pathVals (diamond2 a g1 g2 h1 h2 f) 0 b ↔ b = a := fun b => by
    rw [pathVals_iff]; simp [diamond2_edges_mem]
  have p1 : ∀ b, pathVals (diamond2 a g1 g2 h1 h2 f) 1 b ↔ b = a := fun b => by
    rw [pathVals_iff]; simp [diamond2_edges_mem, p0]
  have p2 : ∀ b, pathVals (diamond2 a g1 g2 h1 h2 f) 2 b ↔ b = g1 a := fun b => by
    rw [pathVals_iff]; simp [diamond2_edges_mem, p1]
  have p3 : ∀ b, pathVals (diamond2 a g1 g2 h1 h2 f) 3 b ↔ b = a := fun b => by
    rw [pathVals_iff]; simp [diamond2_edges_mem, p0]
  have p4 : ∀ b, pathVals (diamond2 a g1 g2 h1 h2 f) 4 b ↔ b = h1 a := fun b => by
    rw [pathVals_iff]; simp [diamond2_edges_mem, p3]
  have p5 : ∀ b, pathVals (diamond2 a g1 g2 h1 h2 f) 5 b ↔ b = g2 (g1 a) ∨ b = h2 (h1 a) :=
    fun b => by
      rw [pathVals_iff]
      simp [diamond2_edges_mem, p2, p4, or_and_right, exists_or]
  rw [pathVals_iff]
  simp [diamond2_edges_mem, p5, or_and_right, exists_or]

theorem diamond2Sol_isLeastSolution_of_monotone {L : Lat α} (hL : L.IsJSL)
    (hg1 : Monotone L g1) (hg2 : Monotone L g2) (hh1 : Monotone L h1) (hh2 : Monotone L h2)
    (hf : Monotone L f) :
    IsLeastSolution L (diamond2 a g1 g2 h1 h2 f) (diamond2Sol L a g1 g2 h1 h2 f) := by
  have hm : ∀ u w, (u, w) ∈ (diamond2 a g1 g2 h1 h2 f).edges ↔ _ := diamond2_edges_mem a g1 g2 h1 h2 f
  refine ⟨⟨by simpa [diamond2Sol] using hL.refl a, ?_⟩, ?_⟩
  · intro u w huw
    rcases (hm u w).1 huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [diamond2Sol] using hL.refl a
    · simpa [diamond2Sol] using hL.refl (g1 a)
    · simpa [diamond2Sol] using Lat.le_join_left hL (g2 (g1 a)) (h2 (h1 a))
    · simpa [diamond2Sol] using hL.refl a
    · simpa [diamond2Sol] using hL.refl (h1 a)
    · simpa [diamond2Sol] using Lat.le_join_right hL (g2 (g1 a)) (h2 (h1 a))
    · simpa [diamond2Sol] using hL.refl (f (L.join (g2 (g1 a)) (h2 (h1 a))))
  · intro y ⟨hy0, hy⟩
    have e : ∀ u w, (u, w) ∈ (diamond2 a g1 g2 h1 h2 f).edges →
        L.le ((diamond2 a g1 g2 h1 h2 f).f u (y u)) (y w) := hy
    have k0 : L.le a (y 0) := hy0
    have k1 : L.le a (y 1) :=
      hL.trans _ _ _ k0 (by simpa using e 0 1 ((hm 0 1).2 (by decide)))
    have k2 : L.le (g1 a) (y 2) :=
      hL.trans _ _ _ (hg1 _ _ k1) (by simpa using e 1 2 ((hm 1 2).2 (by decide)))
    have k3 : L.le a (y 3) :=
      hL.trans _ _ _ k0 (by simpa using e 0 3 ((hm 0 3).2 (by decide)))
    have k4 : L.le (h1 a) (y 4) :=
      hL.trans _ _ _ (hh1 _ _ k3) (by simpa using e 3 4 ((hm 3 4).2 (by decide)))
    have k5 : L.le (L.join (g2 (g1 a)) (h2 (h1 a))) (y 5) :=
      Lat.join_le hL
        (hL.trans _ _ _ (hg2 _ _ k2) (by simpa using e 2 5 ((hm 2 5).2 (by decide))))
        (hL.trans _ _ _ (hh2 _ _ k4) (by simpa using e 4 5 ((hm 4 5).2 (by decide))))
    have k6 : L.le (f (L.join (g2 (g1 a)) (h2 (h1 a)))) (y 6) :=
      hL.trans _ _ _ (hf _ _ k5) (by simpa using e 5 6 ((hm 5 6).2 (by decide)))
    intro v
    rcases fin7_cases v with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [diamond2Sol] using k0
    · simpa [diamond2Sol] using k1
    · simpa [diamond2Sol] using k2
    · simpa [diamond2Sol] using k3
    · simpa [diamond2Sol] using k4
    · simpa [diamond2Sol] using k5
    · simpa [diamond2Sol] using k6

end diamond2

/-- Transfer of `y := c`. -/
def setY (c : Int) (s : St) : St := { s with y := .const c }

/-- Transfer of `z := c`. -/
def setZ (c : Int) (s : St) : St := { s with z := .const c }

theorem setY_distributive (c : Int) : Distributive cpLat (setY c) := by
  intro s t; simp [setY, cpLat, Flat.join]

theorem setZ_distributive (c : Int) : Distributive cpLat (setZ c) := by
  intro s t; simp [setZ, cpLat, Flat.join]

/-- Single-variable assignments `y := 1`, `z := 2`, `y := 2`, `z := 1`, `x := y + z`. -/
def twoStepFamily : (St → St) → Prop :=
  fun φ => φ = setY 1 ∨ φ = setZ 2 ∨ φ = setY 2 ∨ φ = setZ 1 ∨ φ = assignXYZ

/-- Diamond exactness does not extend to two transfers per branch. For the
single-variable assignments `F = {y := 1, z := 2, y := 2, z := 1, x := y + z}` and
the initial value `⟨⊤, ⊤, ⊤⟩`, every diamond built from `F` is exact (each branch
output has `x = ⊤` and `y = ⊤` or `z = ⊤`). Yet on the two-path acyclic CFG running
`y := 1; z := 2` on one branch and `y := 2; z := 1` on the other before `x := y + z`
(every transfer except the identity at the entry and exit drawn from `F`), the least
solution at the exit is `⟨⊤, ⊤, ⊤⟩` while MOP there is `⟨3, ⊤, ⊤⟩`. The family is
not closed under composition. -/
theorem diamondExact_not_exact_on_two_step_branches :
    cpLat.IsJSL ∧ cpLat.AscendingChainCondition ∧
      (∀ φ, twoStepFamily φ → Monotone cpLat φ) ∧
      DiamondExact cpLat (· = ⟨.top, .top, .top⟩) twoStepFamily ∧
      (∀ v : Fin 7, v ≠ 0 → v ≠ 6 → twoStepFamily
        ((diamond2 ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ).f v)) ∧
      IsLeastSolution cpLat
        (diamond2 ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ)
        (diamond2Sol cpLat ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ) ∧
      diamond2Sol cpLat ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ 6 =
        ⟨.top, .top, .top⟩ ∧
      IsMOPAt cpLat (diamond2 ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ)
        6 ⟨.const 3, .top, .top⟩ ∧
      ¬ IsMOPAt cpLat (diamond2 ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ)
        6 (diamond2Sol cpLat ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ 6) := by
  have hmono : ∀ φ, twoStepFamily φ → Monotone cpLat φ := by
    rintro φ (rfl | rfl | rfl | rfl | rfl)
    · exact monotone_of_distributive cpLat_isJSL (setY_distributive 1)
    · exact monotone_of_distributive cpLat_isJSL (setZ_distributive 2)
    · exact monotone_of_distributive cpLat_isJSL (setY_distributive 2)
    · exact monotone_of_distributive cpLat_isJSL (setZ_distributive 1)
    · exact assignXYZ_monotone
  have hmop : IsMOPAt cpLat
      (diamond2 ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ)
      6 ⟨.const 3, .top, .top⟩ := by
    unfold IsMOPAt
    rw [show pathVals (diamond2 ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ) 6 =
        fun b => b = assignXYZ (setZ 2 (setY 1 ⟨.top, .top, .top⟩)) ∨
          b = assignXYZ (setZ 1 (setY 2 ⟨.top, .top, .top⟩)) from
      funext fun b => propext (diamond2_pathVals_six _ _ _ _ _ _ b)]
    have hl := Lat.isLUB_pair cpLat_isJSL (assignXYZ (setZ 2 (setY 1 ⟨.top, .top, .top⟩)))
      (assignXYZ (setZ 1 (setY 2 ⟨.top, .top, .top⟩)))
    have hj : cpLat.join (assignXYZ (setZ 2 (setY 1 ⟨.top, .top, .top⟩)))
        (assignXYZ (setZ 1 (setY 2 ⟨.top, .top, .top⟩))) = ⟨.const 3, .top, .top⟩ := by decide
    rwa [hj] at hl
  have h6 : diamond2Sol cpLat ⟨.top, .top, .top⟩ (setY 1) (setZ 2) (setY 2) (setZ 1) assignXYZ 6 =
      ⟨.top, .top, .top⟩ := by decide
  refine ⟨cpLat_isJSL, cpLat_acc, hmono, ?_, ?_, ?_, h6, hmop, fun h => ?_⟩
  · apply diamondExact_of_distributiveOnRealizable cpLat_isJSL
    rintro a g h f rfl hg hh hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact setY_distributive 1 _ _
    · exact setZ_distributive 2 _ _
    · exact setY_distributive 2 _ _
    · exact setZ_distributive 1 _ _
    · rcases hg with rfl | rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl | rfl <;>
        decide
  · intro v h0 h6'
    rcases fin7_cases v with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact absurd rfl h6'
  · exact diamond2Sol_isLeastSolution_of_monotone _ _ _ _ _ _ cpLat_isJSL
      (hmono _ (Or.inl rfl)) (hmono _ (Or.inr (Or.inl rfl))) (hmono _ (Or.inr (Or.inr (Or.inl rfl))))
      (hmono _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (hmono _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · have := IsMOPAt.unique cpLat_isJSL h hmop
    rw [h6] at this
    simp at this

end Toy.Dataflow
