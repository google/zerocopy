/-
Toy.SCT.Exactness
=================

Proof that the closure criterion is exact for the abstraction over `Nat`: if some idempotent loop
graph `G` of the closure has no strict self-arc, there is an infinite call sequence with
natural-number arguments consistent with the graphs.

Construction. Repeat the factor path `F 0, …, F (m - 1)` of `G` forever. Because `G = G ; G` has
no strict self-arc, its strict arcs form a strict partial order on parameters, ranked by the
number `hc q` of strict arcs out of `q`. Block boundaries get the values
`V q = (m + 1) * hc q + m`; inside a block, a parameter gets the largest value it must exceed
along the remaining arcs of the block (backward dynamic programming, `wv`). Every arc of every
step is then respected.
-/
import Toy.SCT.Threads

namespace Toy.SCT

variable {nf k : Nat}

/-! ### Finite maxima -/

theorem foldl_max_ge {β : Type} (f : β → Nat) :
    ∀ (xs : List β) (acc : Nat),
      acc ≤ xs.foldl (fun acc q => max acc (f q)) acc ∧
        ∀ x ∈ xs, f x ≤ xs.foldl (fun acc q => max acc (f q)) acc
  | [], acc => ⟨Nat.le_refl _, fun _ hx => absurd hx List.not_mem_nil⟩
  | y :: ys, acc => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f ys (max acc (f y))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

theorem foldl_max_cases {β : Type} (f : β → Nat) :
    ∀ (xs : List β) (acc : Nat),
      xs.foldl (fun acc q => max acc (f q)) acc = acc ∨
        ∃ x ∈ xs, xs.foldl (fun acc q => max acc (f q)) acc = f x
  | [], acc => Or.inl rfl
  | y :: ys, acc => by
    rcases foldl_max_cases f ys (max acc (f y)) with h | ⟨x, hx, h⟩
    · rw [List.foldl_cons, h]
      rcases Nat.le_total acc (f y) with hle | hle
      · exact Or.inr ⟨y, by simp, Nat.max_eq_right hle⟩
      · exact Or.inl (Nat.max_eq_left hle)
    · exact Or.inr ⟨x, by simp [hx], h⟩

/-- The maximum of `f` over `Fin k` (`0` if `k = 0`). -/
def finMax (f : Fin k → Nat) : Nat := (List.finRange k).foldl (fun acc q => max acc (f q)) 0

theorem le_finMax (f : Fin k → Nat) (q : Fin k) : f q ≤ finMax f :=
  (foldl_max_ge f _ 0).2 q (List.mem_finRange q)

theorem finMax_cases (f : Fin k → Nat) : finMax f = 0 ∨ ∃ q, finMax f = f q := by
  rcases foldl_max_cases f (List.finRange k) 0 with h | ⟨x, -, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, h⟩

/-! ### Counting -/

theorem countP_lt_of_imp {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
      l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | y :: ys, himp, ⟨x, hx, hqx, hpx⟩ => by
    rw [List.countP_cons, List.countP_cons]
    have himp' : ∀ z ∈ ys, p z = true → q z = true := fun z hz => himp z (by simp [hz])
    have hmono := List.countP_mono_left himp'
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [hqx, hpx, ite_true]
      simp
      omega
    · have hlt := countP_lt_of_imp himp' ⟨x, hx', hqx, hpx⟩
      by_cases hpy : p y = true
      · simp only [hpy, himp y (by simp) hpy, ite_true]
        omega
      · have e : (if p y = true then 1 else 0) = 0 := by simp [hpy]
        rw [e]
        have : 0 ≤ (if q y = true then 1 else 0) := Nat.zero_le _
        omega

/-! ### The backward values inside a block -/

/-- The value contributed by an arc with label `l` towards a callee value `x`. -/
def arcVal (l : Label) (x : Nat) : Nat :=
  match l with
  | .absent => 0
  | .nonstrict => x
  | .strict => x + 1

/-- Values at offset `r` of a block `F 0, …, F (m - 1)` whose end values are `V`: the least
value that respects every arc of the remaining steps of the block. -/
def wv (F : Nat → SCG nf k) (m : Nat) (V : Fin k → Nat) (r : Nat) (q : Fin k) : Nat :=
  if r < m then finMax (fun q' => arcVal ((F r).lab q q') (wv F m V (r + 1) q')) else V q
termination_by m - r

theorem wv_lt (F : Nat → SCG nf k) (m : Nat) (V : Fin k → Nat) {r : Nat} (hr : r < m)
    (q : Fin k) :
    wv F m V r q = finMax (fun q' => arcVal ((F r).lab q q') (wv F m V (r + 1) q')) := by
  rw [wv, ite_eq_left hr]

theorem wv_ge (F : Nat → SCG nf k) (m : Nat) (V : Fin k → Nat) {r : Nat} (hr : ¬ r < m)
    (q : Fin k) : wv F m V r q = V q := by
  rw [wv, ite_eq_right hr]

theorem wv_respects (F : Nat → SCG nf k) (m : Nat) (V : Fin k → Nat) {r : Nat} (hr : r < m)
    (q q' : Fin k) :
    ((F r).lab q q' = Label.strict → wv F m V (r + 1) q' < wv F m V r q) ∧
    ((F r).lab q q' = Label.nonstrict → wv F m V (r + 1) q' ≤ wv F m V r q) := by
  have hle := le_finMax (fun q' => arcVal ((F r).lab q q') (wv F m V (r + 1) q')) q'
  rw [← wv_lt F m V hr q] at hle
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [h, arcVal] at hle
    omega
  · simp only [h, arcVal] at hle
    exact hle

/-- Each value inside a block is either small or is witnessed by a thread to the end of the
block (with `+ (remaining length)` slack if the thread has a strict arc). -/
theorem wv_inv (F : Nat → SCG nf k) (m : Nat) (V : Fin k → Nat) :
    ∀ (d r : Nat), r + d = m → ∀ q : Fin k,
      wv F m V r q ≤ d ∨
        ∃ j b, SegThread F r d q j b ∧ wv F m V r q ≤ V j + (if b then d else 0) := by
  intro d
  induction d with
  | zero =>
    intro r hr q
    rw [Nat.add_zero] at hr
    subst hr
    refine Or.inr ⟨q, false, ⟨rfl, rfl⟩, ?_⟩
    rw [wv_ge F r V (Nat.lt_irrefl r)]
    simp
  | succ d ih =>
    intro r hr q
    have hrm : r < m := by omega
    rw [wv_lt F m V hrm]
    rcases finMax_cases (fun q' => arcVal ((F r).lab q q') (wv F m V (r + 1) q')) with h0 | ⟨q', hq'⟩
    · exact Or.inl (by rw [h0]; exact Nat.zero_le _)
    · rw [hq']
      have ih' := ih (r + 1) (by omega) q'
      cases hl : (F r).lab q q' with
      | absent => exact Or.inl (by simp [arcVal])
      | nonstrict =>
        simp only [arcVal]
        rcases ih' with h | ⟨j, b, hs, hb⟩
        · exact Or.inl (by omega)
        · refine Or.inr ⟨j, b, ⟨q', false, b, ?_, hs, by simp⟩, ?_⟩
          · rw [hl]; exact (Label.ok_false _).mpr (by decide)
          · cases b <;> simp at hb ⊢ <;> omega
      | strict =>
        simp only [arcVal]
        rcases ih' with h | ⟨j, b, hs, hb⟩
        · exact Or.inl (by omega)
        · refine Or.inr ⟨j, true, ⟨q', true, b, ?_, hs, by simp⟩, ?_⟩
          · rw [hl]; exact (Label.ok_true _).mpr rfl
          · cases b <;> simp at hb ⊢ <;> omega

/-! ### Arithmetic of the period -/

theorem succ_mod_cases (m t : Nat) (hm : 0 < m) :
    (t % m + 1 < m ∧ (t + 1) % m = t % m + 1) ∨ (t % m + 1 = m ∧ (t + 1) % m = 0) := by
  have hlt := Nat.mod_lt t hm
  rcases Nat.lt_or_ge (t % m + 1) m with h | h
  · refine Or.inl ⟨h, ?_⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < m by omega), Nat.mod_eq_of_lt h]
  · have e : t % m + 1 = m := by omega
    refine Or.inr ⟨e, ?_⟩
    rw [Nat.add_mod]
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, e, Nat.mod_self]
    · have : m = 1 := by omega
      subst this
      simp [Nat.mod_one]

/-! ### Exactness -/

/-- **Exactness over `Nat`.** -/
theorem consistent_nat_run_of_not_closureCriterion_proof (P : Prog nf k)
    (hnc : ¬ ClosureCriterion P) : ConsistentRunIn Nat P := by
  have ⟨G, hG, hloop, hidem, hns⟩ : ∃ G, InClosure P G ∧ G.src = G.dst ∧ G.comp G = G ∧
      ¬ G.HasStrictSelfArc :=
    Classical.byContradiction fun hne => hnc fun G hG hloop hidem =>
      Classical.byContradiction fun hs => hne ⟨G, hG, hloop, hidem, hs⟩
  obtain ⟨m, F, hm, hcalls, hchain, hsrc, hdst, hsem⟩ := hasFactorPath_of_inClosure hG
  have hsemF : ∀ q j b, (G.lab q j).Ok b ↔ SegThread F 0 m q j b :=
    hsem F 0 (fun t _ => by rw [Nat.zero_add])
  -- strict arcs of the idempotent `G` propagate along present arcs
  have hprop : ∀ q j l, G.lab q j ≠ Label.absent → G.lab j l = Label.strict →
      G.lab q l = Label.strict := by
    intro q j l h1 h2
    have := (SCG.comp_ok' G G q l true).mpr
      ⟨j, false, true, (Label.ok_false _).mpr h1, (Label.ok_true _).mpr h2, rfl⟩
    rw [hidem] at this
    exact (Label.ok_true _).mp this
  let hc : Fin k → Nat := fun q =>
    (List.finRange k).countP (fun l => decide (G.lab q l = Label.strict))
  have hc_le : ∀ q j, G.lab q j ≠ Label.absent → hc j ≤ hc q := by
    intro q j h
    apply List.countP_mono_left
    intro l _ hl
    simp only [decide_eq_true_eq] at hl ⊢
    exact hprop q j l h hl
  have hc_lt : ∀ q j, G.lab q j = Label.strict → hc j < hc q := by
    intro q j h
    apply countP_lt_of_imp
    · intro l _ hl
      simp only [decide_eq_true_eq] at hl ⊢
      exact hprop q j l (by rw [h]; decide) hl
    · refine ⟨j, List.mem_finRange j, by simp [h], ?_⟩
      simp only [decide_eq_false_iff_not]
      exact fun hjj => hns ⟨j, hjj⟩
  let V : Fin k → Nat := fun q => (m + 1) * hc q + m
  have hw0 : ∀ q, wv F m V 0 q ≤ V q := by
    intro q
    rcases wv_inv F m V m 0 (Nat.zero_add m) q with h | ⟨j, b, hs, hb⟩
    · exact Nat.le_trans h (Nat.le_add_left m _)
    · have hok := (hsemF q j b).mpr hs
      cases b with
      | true =>
        have hlt := hc_lt q j ((Label.ok_true _).mp hok)
        have hmul : (m + 1) * (hc j + 1) ≤ (m + 1) * hc q := Nat.mul_le_mul_left _ hlt
        rw [Nat.mul_succ] at hmul
        simp only [ite_true, V] at hb ⊢
        omega
      | false =>
        have hle := hc_le q j ((Label.ok_false _).mp hok)
        have hmul : (m + 1) * hc j ≤ (m + 1) * hc q := Nat.mul_le_mul_left _ hle
        simp only [V] at hb ⊢
        simp at hb
        omega
  refine ⟨fun t => (F (t % m)).src, fun t q => if t % m = 0 then V q else wv F m V (t % m) q,
    fun t => F (t % m), fun t => ⟨hcalls _ (Nat.mod_lt _ hm), rfl, ?_, ?_⟩⟩
  · show (F (t % m)).dst = (F ((t + 1) % m)).src
    rcases succ_mod_cases m t hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      exact hchain _ h1
    · rw [h2, show t % m = m - 1 by omega, hdst, ← hloop, ← hsrc]
  · have hr : t % m < m := Nat.mod_lt _ hm
    have hnext : ∀ j, (if (t + 1) % m = 0 then V j else wv F m V ((t + 1) % m) j) =
        wv F m V (t % m + 1) j := by
      intro j
      rcases succ_mod_cases m t hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, ite_eq_right (by omega)]
      · rw [h2, ite_eq_left rfl, h1, wv_ge F m V (Nat.lt_irrefl m)]
    have hcur : ∀ i, wv F m V (t % m) i ≤ (if t % m = 0 then V i else wv F m V (t % m) i) := by
      intro i
      by_cases h0 : t % m = 0
      · rw [ite_eq_left h0, h0]
        exact hw0 i
      · rw [ite_eq_right h0]
        exact Nat.le_refl _
    intro i j
    dsimp only
    rw [hnext j]
    obtain ⟨hs, hn⟩ := wv_respects F m V hr i j
    exact ⟨fun h => Nat.lt_of_lt_of_le (hs h) (hcur i),
      fun h => Nat.le_trans (hn h) (hcur i)⟩

end Toy.SCT
