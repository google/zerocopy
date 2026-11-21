import ToySsa.Examples

/-!
Join sets versus iterated dominance frontiers, and the correctness and minimality of
φ placement measured by reaching definitions.
-/
namespace Toy.Ssa

variable {n : Nat}


/-- `DF⁺` is monotone in its argument set. -/
theorem IDF.mono {G : Cfg n} {S S' : Fin n → Prop} (h : ∀ x, S x → S' x) {y : Fin n}
    (hy : IDF G S y) : IDF G S' y := by
  induction hy with
  | base hx hdf => exact IDF.base (h _ hx) hdf
  | step _ hdf ih => exact IDF.step ih hdf

/-- Concatenation of a walk from `a` to `b` with a walk from `b` to `c`. -/
theorem Walk.append {G : Cfg n} {a b c : Fin n} {p q : List (Fin n)} (hp : Walk G a b p)
    (hq : Walk G b c q) : Walk G a c (p ++ q.tail) := by
  induction hp with
  | single a =>
    cases hq with
    | single => exact Walk.single _
    | cons he hw => exact Walk.cons he hw
  | cons he _ ih => exact Walk.cons he (ih hq)

/-! ### Proof infrastructure for join closure and `DF⁺ ⊆ J`

A nonnull walk to `z` is presented by the list of its nodes before the final `z`: a walk from
its start to some predecessor `u` of `z`, followed by the edge `u → z`. Two such walks converge
in the sense of `Converge` exactly when these lists are disjoint (`inJoin_iff_preWalks`). -/

/-- `PreWalk G x z A`: `A` is a walk from `x` to a predecessor of `z`, i.e. `A ++ [z]` is a
nonnull walk from `x` to `z` and `A` lists its nodes before the final `z`. -/
def PreWalk (G : Cfg n) (x z : Fin n) (A : List (Fin n)) : Prop :=
  ∃ u, Walk G x u A ∧ G.edge u z = true

/-- `J(S)` expressed through pre-walks with disjoint node lists. -/
def InJoinPre (G : Cfg n) (S : Fin n → Prop) (z : Fin n) : Prop :=
  ∃ x y A B, S x ∧ S y ∧ x ≠ y ∧ PreWalk G x z A ∧ PreWalk G y z B ∧ ∀ v, v ∈ A → v ∉ B

theorem PreWalk.head_mem {G : Cfg n} {x z : Fin n} {A : List (Fin n)} (h : PreWalk G x z A) :
    x ∈ A := by
  obtain ⟨_, hw, _⟩ := h
  exact hw.head_mem

theorem PreWalk.length_pos {G : Cfg n} {x z : Fin n} {A : List (Fin n)} (h : PreWalk G x z A) :
    0 < A.length := by
  obtain ⟨_, hw, _⟩ := h
  exact hw.length_pos

/-- `InJoin` is the pre-walk formulation with disjoint node lists. -/
theorem inJoin_iff_preWalks (G : Cfg n) (S : Fin n → Prop) (z : Fin n) :
    InJoin G S z ↔ InJoinPre G S z := by
  constructor
  · rintro ⟨x, y, p, q, hx, hy, hxy, hp, hq, lp, lq, hdis⟩
    rcases hp.single_or_snoc with ⟨rfl, _⟩ | ⟨A, u, rfl, hA, hu⟩
    · simp at lp
    rcases hq.single_or_snoc with ⟨rfl, _⟩ | ⟨B, u', rfl, hB, hu'⟩
    · simp at lq
    refine ⟨x, y, A, B, hx, hy, hxy, ⟨u, hA, hu⟩, ⟨u', hB, hu'⟩, ?_⟩
    intro v hvA hvB
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvA
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hvB
    have e1 : (A ++ [z])[i]'(by simp; omega) = A[i] := List.getElem_append_left hi
    have e2 : (B ++ [z])[j]'(by simp; omega) = B[j] := List.getElem_append_left hj
    have h := hdis ⟨i, by simp; omega⟩ ⟨j, by simp; omega⟩ (by
      show (A ++ [z])[i]'(by simp; omega) = (B ++ [z])[j]'(by simp; omega)
      rw [e1, e2]; exact hji.symm)
    simp at h
    omega
  · rintro ⟨x, y, A, B, hx, hy, hxy, ⟨u, hA, hu⟩, ⟨u', hB, hu'⟩, hAB⟩
    refine ⟨x, y, A ++ [z], B ++ [z], hx, hy, hxy, hA.append_edge hu, hB.append_edge hu',
      by simp; exact hA.length_pos, by simp; exact hB.length_pos, ?_⟩
    intro i j heq
    have hi := i.isLt
    have hj := j.isLt
    simp only [List.length_append, List.length_singleton] at hi hj
    by_cases hiA : i.val < A.length
    · by_cases hjB : j.val < B.length
      · exfalso
        have h1 : (A ++ [z])[i.val] = A[i.val] := List.getElem_append_left hiA
        have h2 : (B ++ [z])[j.val] = B[j.val] := List.getElem_append_left hjB
        have heq' : A[i.val] = B[j.val] := by rw [← h1, ← h2]; exact heq
        exact hAB _ (List.getElem_mem hiA) (heq' ▸ List.getElem_mem hjB)
      · right; simp; omega
    · left; simp; omega

theorem InJoinPre.mono {G : Cfg n} {S S' : Fin n → Prop} (h : ∀ x, S x → S' x) {z : Fin n}
    (hz : InJoinPre G S z) : InJoinPre G S' z := by
  obtain ⟨x, y, A, B, hx, hy, hxy, hA, hB, hAB⟩ := hz
  exact ⟨x, y, A, B, h _ hx, h _ hy, hxy, hA, hB, hAB⟩

/-- Concatenation of a walk ending at a predecessor of `w` with a walk starting at `w`. -/
theorem Walk.append_of_edge {G : Cfg n} {x u w v : Fin n} {A R : List (Fin n)}
    (hA : Walk G x u A) (he : G.edge u w = true) (hR : Walk G w v R) : Walk G x v (A ++ R) := by
  induction hA with
  | single a => exact Walk.cons he hR
  | cons hab _ ih => exact Walk.cons hab (ih he)

theorem PreWalk.append {G : Cfg n} {x w z : Fin n} {A R : List (Fin n)}
    (hA : PreWalk G x w A) (hR : PreWalk G w z R) : PreWalk G x z (A ++ R) := by
  obtain ⟨u, hA, hu⟩ := hA
  obtain ⟨v, hR, hv⟩ := hR
  exact ⟨v, hA.append_of_edge hu hR, hv⟩

/-- Split a walk at the first node satisfying `Q`. -/
theorem Walk.first_hit {G : Cfg n} (Q : Fin n → Prop) {a b : Fin n} {L : List (Fin n)}
    (h : Walk G a b L) :
    (∀ v ∈ L, ¬ Q v) ∨
      ∃ L₁ t L₂, L = L₁ ++ t :: L₂ ∧ Q t ∧ (∀ v ∈ L₁, ¬ Q v) ∧
        ((L₁ = [] ∧ a = t) ∨ ∃ u, Walk G a u L₁ ∧ G.edge u t = true) ∧ Walk G t b (t :: L₂) := by
  induction h with
  | single a =>
    by_cases hq : Q a
    · exact Or.inr ⟨[], a, [], rfl, hq, by simp, Or.inl ⟨rfl, rfl⟩, Walk.single a⟩
    · exact Or.inl (by simpa using hq)
  | @cons a c b p he hw ih =>
    by_cases hq : Q a
    · exact Or.inr ⟨[], a, p, rfl, hq, by simp, Or.inl ⟨rfl, rfl⟩, Walk.cons he hw⟩
    · rcases ih with hnone | ⟨L₁, t, L₂, rfl, hqt, hL₁, hpre, hsuf⟩
      · left
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hq
        · exact hnone v hv
      · right
        refine ⟨a :: L₁, t, L₂, rfl, hqt, ?_, Or.inr ?_, hsuf⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hq
          · exact hL₁ v hv
        · rcases hpre with ⟨rfl, rfl⟩ | ⟨u, hu, hut⟩
          · exact ⟨a, Walk.single a, he⟩
          · exact ⟨u, Walk.cons he hu, hut⟩

/-- Split a walk at the last node satisfying `Q`. -/
theorem Walk.last_hit {G : Cfg n} (Q : Fin n → Prop) {a b : Fin n} {L : List (Fin n)}
    (h : Walk G a b L) :
    (∀ v ∈ L, ¬ Q v) ∨
      ∃ L₁ t L₂, L = L₁ ++ t :: L₂ ∧ Q t ∧ (∀ v ∈ L₂, ¬ Q v) ∧ Walk G t b (t :: L₂) := by
  induction h with
  | single a =>
    by_cases hq : Q a
    · exact Or.inr ⟨[], a, [], rfl, hq, by simp, Walk.single a⟩
    · exact Or.inl (by simpa using hq)
  | @cons a c b p he hw ih =>
    rcases ih with hnone | ⟨L₁, t, L₂, rfl, hqt, hL₂, hsuf⟩
    · by_cases hq : Q a
      · exact Or.inr ⟨[], a, p, rfl, hq, hnone, Walk.cons he hw⟩
      · left
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hq
        · exact hnone v hv
    · exact Or.inr ⟨a :: L₁, t, L₂, rfl, hqt, hL₂, hsuf⟩

/-- A suffix walk from any node of a walk, using only nodes of the walk. -/
theorem Walk.suffix_sub {G : Cfg n} {a b v : Fin n} {L : List (Fin n)} (h : Walk G a b L)
    (hv : v ∈ L) : ∃ T, Walk G v b T ∧ ∀ t ∈ T, t ∈ L := by
  induction h with
  | single a' =>
    have : v = a' := by simpa using hv
    subst this
    exact ⟨[v], Walk.single _, fun t ht => ht⟩
  | @cons a' b' c' p' he hw ih =>
    by_cases hva : v = a'
    · subst hva; exact ⟨_, Walk.cons he hw, fun t ht => ht⟩
    · rcases List.mem_cons.mp hv with h | h
      · exact absurd h hva
      · obtain ⟨T, hT, hsub⟩ := ih h
        exact ⟨T, hT, fun t ht => List.mem_cons_of_mem _ (hsub t ht)⟩

/-- Shorten a pre-walk to `w` so that `w` does not occur before the end, unless it starts at `w`. -/
theorem PreWalk.first_visit {G : Cfg n} {x w : Fin n} {A : List (Fin n)} (h : PreWalk G x w A)
    (hxw : x ≠ w) : ∃ A', PreWalk G x w A' ∧ (∀ v ∈ A', v ∈ A) ∧ w ∉ A' := by
  obtain ⟨u, hA, hu⟩ := h
  rcases hA.first_hit (fun v => v = w) with hnone | ⟨L₁, t, L₂, rfl, rfl, hL₁, hpre, _⟩
  · exact ⟨A, ⟨u, hA, hu⟩, fun v hv => hv, fun hw => hnone w hw rfl⟩
  · rcases hpre with ⟨_, hxt⟩ | ⟨u', hu', hut⟩
    · exact absurd hxt hxw
    · exact ⟨L₁, ⟨u', hu', hut⟩, fun v hv => by simp [hv], fun hw => hL₁ _ hw rfl⟩

/-- A pre-walk to a node `t` of a walk from `x`, through nodes of that walk, unless `t = x`. -/
theorem Walk.prefix_pre {G : Cfg n} {x b t : Fin n} {A : List (Fin n)} (h : Walk G x b A)
    (ht : t ∈ A) : t = x ∨ ∃ A₀, PreWalk G x t A₀ ∧ ∀ v ∈ A₀, v ∈ A := by
  obtain ⟨q, hq, hsub, _⟩ := h.prefix_to ht
  rcases hq.single_or_snoc with ⟨_, rfl⟩ | ⟨w', p, rfl, hw', hp⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨w', ⟨p, hw', hp⟩, fun v hv => hsub v (List.mem_append_left _ hv)⟩

/-- **Core step of join closure.** If `w ∈ J(S)` (witnessed by disjoint pre-walks `A`, `B` from
`x ≠ y ∈ S`), and pre-walks `C` from `a ∈ S` and `R` from `w` to `z` are disjoint, then
`z ∈ J(S)`. Strong induction on the length of `R`: if `R` meets `A ∪ B`, restart from its first
meeting point, which is again in `J(S)`; otherwise reroute through the last node of `C` in
`A ∪ B`. -/
theorem inJoinPre_of_join_point (G : Cfg n) (S : Fin n → Prop) :
    ∀ (N : Nat) (w z a x y : Fin n) (A B C R : List (Fin n)), R.length ≤ N →
      S x → S y → x ≠ y → PreWalk G x w A → PreWalk G y w B → (∀ v, v ∈ A → v ∉ B) →
      S a → PreWalk G a z C → PreWalk G w z R → (∀ v, v ∈ C → v ∉ R) →
      InJoinPre G S z := by
  intro N
  induction N with
  | zero =>
    intro w z a x y A B C R hlen _ _ _ _ _ _ _ _ hR _
    have := hR.length_pos; omega
  | succ N ih =>
    intro w z a x y A B C R hlen hx hy hxy hA hB hAB ha hC hR hCR
    have haw : a ≠ w := fun h => hCR a hC.head_mem (h ▸ hR.head_mem)
    by_cases hSw : S w
    · exact ⟨a, w, C, R, ha, hSw, haw, hC, hR, hCR⟩
    have hxw : x ≠ w := fun h => hSw (h ▸ hx)
    have hyw : y ≠ w := fun h => hSw (h ▸ hy)
    obtain ⟨A', hA', hA'A, hwA'⟩ := hA.first_visit hxw
    obtain ⟨B', hB', hB'B, hwB'⟩ := hB.first_visit hyw
    have hA'B' : ∀ v, v ∈ A' → v ∉ B' := fun v h1 h2 => hAB v (hA'A v h1) (hB'B v h2)
    obtain ⟨vR, hRw, hvR⟩ := hR
    obtain ⟨vC, hCw, hvC⟩ := hC
    obtain ⟨uA, hAw, huA⟩ := hA'
    obtain ⟨uB, hBw, huB⟩ := hB'
    rcases hRw.first_hit (fun v => v ∈ A' ∨ v ∈ B') with hnone |
      ⟨R₁, t, R₂, hReq, hQt, hR₁, hpre, hsuf⟩
    · -- `R` avoids `A' ∪ B'`.
      rcases hCw.last_hit (fun v => v ∈ A' ∨ v ∈ B') with hnoneC | ⟨C₁, t, C₂, hCeq, hQt, hC₂, hsufC⟩
      · -- `C` avoids `A' ∪ B'`: converge `C` from `a` with `A' ++ R` from `x`.
        refine ⟨a, x, C, A' ++ R, ha, hx, ?_, ⟨vC, hCw, hvC⟩,
          PreWalk.append ⟨uA, hAw, huA⟩ ⟨vR, hRw, hvR⟩, ?_⟩
        · intro h
          exact hnoneC a hCw.head_mem (Or.inl (h ▸ hAw.head_mem))
        · intro v hvC hv
          rcases List.mem_append.mp hv with h | h
          · exact hnoneC v hvC (Or.inl h)
          · exact hCR v hvC h
      · have hC₂C : ∀ v ∈ C₂, v ∈ C := fun v hv => by rw [hCeq]; simp [hv]
        rcases hQt with htA | htB
        · -- reroute `x` along `A'` up to `t`, then along `C` from `t`.
          obtain ⟨A₁, hA₁, hA₁sub, _⟩ := hAw.prefix_to htA
          refine ⟨x, y, A₁ ++ C₂, B' ++ R, hx, hy, hxy, ⟨vC, hA₁.append hsufC, hvC⟩,
            PreWalk.append ⟨uB, hBw, huB⟩ ⟨vR, hRw, hvR⟩, ?_⟩
          intro v hv1 hv2
          rcases List.mem_append.mp hv1 with h1 | h1 <;> rcases List.mem_append.mp hv2 with h2 | h2
          · exact hA'B' v (hA₁sub v h1) h2
          · exact hnone v h2 (Or.inl (hA₁sub v h1))
          · exact hC₂ v h1 (Or.inr h2)
          · exact hCR v (hC₂C v h1) h2
        · obtain ⟨B₁, hB₁, hB₁sub, _⟩ := hBw.prefix_to htB
          refine ⟨x, y, A' ++ R, B₁ ++ C₂, hx, hy, hxy,
            PreWalk.append ⟨uA, hAw, huA⟩ ⟨vR, hRw, hvR⟩, ⟨vC, hB₁.append hsufC, hvC⟩, ?_⟩
          intro v hv1 hv2
          rcases List.mem_append.mp hv1 with h1 | h1 <;> rcases List.mem_append.mp hv2 with h2 | h2
          · exact hA'B' v h1 (hB₁sub v h2)
          · exact hC₂ v h2 (Or.inl h1)
          · exact hnone v h1 (Or.inr (hB₁sub v h2))
          · exact hCR v (hC₂C v h2) h1
    · -- `R` first meets `A' ∪ B'` at `t`, after a nonempty prefix `R₁`.
      rcases hpre with ⟨_, rfl⟩ | ⟨u, hR₁w, hut⟩
      · rcases hQt with h | h
        · exact absurd h hwA'
        · exact absurd h hwB'
      have hsubR : ∀ v ∈ t :: R₂, v ∈ R := fun v hv => by rw [hReq]; simp_all
      have hCt : ∀ v, v ∈ C → v ∉ t :: R₂ := fun v hv h => hCR v hv (hsubR v h)
      have hlen' : (t :: R₂).length ≤ N := by
        have := hR₁w.length_pos
        rw [hReq] at hlen; simp at hlen ⊢; omega
      rcases hQt with htA | htB
      · rcases hAw.prefix_pre htA with rfl | ⟨A₀, hA₀, hA₀sub⟩
        · exact ⟨a, t, C, t :: R₂, ha, hx, fun h => hCt a hCw.head_mem (h ▸ List.mem_cons_self),
            ⟨vC, hCw, hvC⟩, ⟨vR, hsuf, hvR⟩, hCt⟩
        · refine ih t z a x y A₀ (B' ++ R₁) C (t :: R₂) hlen' hx hy hxy hA₀
            (PreWalk.append ⟨uB, hBw, huB⟩ ⟨u, hR₁w, hut⟩) ?_ ha ⟨vC, hCw, hvC⟩ ⟨vR, hsuf, hvR⟩ hCt
          intro v h1 h2
          rcases List.mem_append.mp h2 with h2 | h2
          · exact hA'B' v (hA₀sub v h1) h2
          · exact hR₁ v h2 (Or.inl (hA₀sub v h1))
      · rcases hBw.prefix_pre htB with rfl | ⟨B₀, hB₀, hB₀sub⟩
        · exact ⟨a, t, C, t :: R₂, ha, hy, fun h => hCt a hCw.head_mem (h ▸ List.mem_cons_self),
            ⟨vC, hCw, hvC⟩, ⟨vR, hsuf, hvR⟩, hCt⟩
        · refine ih t z a x y (A' ++ R₁) B₀ C (t :: R₂) hlen' hx hy hxy
            (PreWalk.append ⟨uA, hAw, huA⟩ ⟨u, hR₁w, hut⟩) hB₀ ?_ ha ⟨vC, hCw, hvC⟩
            ⟨vR, hsuf, hvR⟩ hCt
          intro v h1 h2
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hA'B' v h1 (hB₀sub v h2)
          · exact hR₁ v h1 (Or.inr (hB₀sub v h2))

/-- If `w ∈ J(S)` and `z ∈ J(S ∪ {w})`, then `z ∈ J(S)`. -/
theorem inJoinPre_of_insert_join {G : Cfg n} {S : Fin n → Prop} {w z : Fin n}
    (hw : InJoinPre G S w) (hz : InJoinPre G (fun t => S t ∨ t = w) z) : InJoinPre G S z := by
  obtain ⟨x, y, A, B, hx, hy, hxy, hA, hB, hAB⟩ := hw
  obtain ⟨u, v, U, V, hu, hv, huv, hU, hV, hUV⟩ := hz
  rcases hu with hu | rfl <;> rcases hv with hv | rfl
  · exact ⟨u, v, U, V, hu, hv, huv, hU, hV, hUV⟩
  · exact inJoinPre_of_join_point G S _ _ _ _ x y A B U V (Nat.le_refl _) hx hy hxy hA hB hAB
      hu hU hV hUV
  · exact inJoinPre_of_join_point G S _ _ _ _ x y A B V U (Nat.le_refl _) hx hy hxy hA hB hAB
      hv hV hU (fun t h1 h2 => hUV t h2 h1)
  · exact absurd rfl huv


/-- A node of a walk to `pr` after the last visit to `x`, with `x` dominating `pr`, is dominated
by `x`. -/
theorem dom_of_walk_avoid {G : Cfg n} {x v pr : Fin n} {T : List (Fin n)} (hdom : Dom G x pr)
    (hT : Walk G v pr T) (hx : x ∉ T) : Dom G x v := by
  intro V hV
  have hmem := hdom _ (hV.append hT)
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · exact absurd (List.mem_of_mem_tail h) hx

/-- **`y ∈ DF(x)` gives converging pre-walks from `x` and from the entry** (Cytron et al.,
Lemma 7 setting), when every node is reachable and no edge enters the entry. -/
theorem df_preWalks_of_allReachable_of_entryNoPreds {G : Cfg n} (hreach : AllReachable G)
    (hnp : EntryNoPreds G) {x y : Fin n} (hdf : DF G x y) :
    x ≠ G.entry ∧ ∃ A B, PreWalk G x y A ∧ PreWalk G G.entry y B ∧ ∀ v, v ∈ A → v ∉ B := by
  have hne : x ≠ G.entry := by
    intro h
    rw [h] at hdf
    exact not_df_entry hnp y hdf
  refine ⟨hne, ?_⟩
  obtain ⟨⟨pr, hpr, hdom⟩, hns⟩ := hdf
  obtain ⟨W, hW⟩ := hreach pr
  rcases hW.last_hit (fun v => v = x) with hnone | ⟨W₁, t, W₂, _, rfl, hW₂, hσ⟩
  · exact absurd rfl (hnone _ (hdom W hW))
  -- `σ = t :: W₂` runs from `t = x` to `pr` and every node on it is dominated by `x`.
  have hdomσ : ∀ v ∈ t :: W₂, Dom G t v := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact dom_refl G v
    · cases hσ with
      | single => exact absurd ‹v ∈ []› List.not_mem_nil
      | cons _ hw =>
        obtain ⟨T, hT, hsub⟩ := hw.suffix_sub hv
        exact dom_of_walk_avoid hdom hT (fun h => hW₂ _ (hsub _ h) rfl)
  -- A walk from the entry that avoids `x` avoids every node of `σ`.
  have havoid : ∀ (u : Fin n) (τ : List (Fin n)), Walk G G.entry u τ → t ∉ τ →
      ∀ v, v ∈ t :: W₂ → v ∉ τ := by
    intro u τ hτ htτ v hv hvτ
    obtain ⟨q, hq, hsub, _⟩ := hτ.prefix_to hvτ
    exact htτ (hsub _ (hdomσ v hv q hq))
  by_cases hd : Dom G t y
  · -- `t = y`: a walk from the entry to its first visit of `t`.
    have hty : t = y := Classical.byContradiction fun h => hns ⟨hd, h⟩
    subst hty
    obtain ⟨Wt, hWt⟩ := hreach t
    rcases hWt.first_hit (fun v => v = t) with hnone | ⟨L₁, s, L₂, _, rfl, hL₁, hpre, _⟩
    · exact absurd rfl (hnone _ hWt.last_mem)
    rcases hpre with ⟨_, hes⟩ | ⟨u, hu, hus⟩
    · exact absurd hes.symm hne
    exact ⟨s :: W₂, L₁, ⟨pr, hσ, hpr⟩, ⟨u, hu, hus⟩,
      havoid u L₁ hu (fun h => hL₁ _ h rfl)⟩
  · -- `¬ Dom t y`: a walk from the entry to `y` avoiding `t`.
    have hex : ∃ τ, Walk G G.entry y τ ∧ t ∉ τ :=
      Classical.byContradiction fun h => hd fun τ hτ =>
        Classical.byContradiction fun ht => h ⟨τ, hτ, ht⟩
    obtain ⟨τ, hτ, htτ⟩ := hex
    rcases hτ.single_or_snoc with ⟨rfl, hye⟩ | ⟨τ₀, u, rfl, hτ₀, hu⟩
    · rw [hye] at hpr
      simp [hnp pr] at hpr
    · have ht₀ : t ∉ τ₀ := fun h => htτ (List.mem_append_left _ h)
      exact ⟨t :: W₂, τ₀, ⟨pr, hσ, hpr⟩, ⟨u, hτ₀, hu⟩, havoid u τ₀ hτ₀ ht₀⟩

/-! ## Join sets and iterated dominance frontiers -/

/-- **`DF⁺(S) ⊆ J(S)`** when `S` contains the entry, no edge enters the entry, and every node is
reachable (Cytron et al., Lemma 7 iterated). Proof: induction on `DF⁺`; each step `y ∈ DF(x)`
gives converging walks from `x` and from the entry (`df_preWalks_of_allReachable_of_entryNoPreds`),
and a step from `x ∈ J(S)` is absorbed by join closure (`inJoinPre_of_insert_join`). -/
theorem iteratedDF_subset_join_of_allReachable_of_entryNoPreds_of_entry_mem (G : Cfg n) (S : Fin n → Prop)
    (hreach : AllReachable G) (hnp : EntryNoPreds G) (hS : S G.entry) :
    ∀ z, IDF G S z → InJoin G S z := by
  intro z hz
  rw [inJoin_iff_preWalks]
  induction hz with
  | @base x y hx hdf =>
    obtain ⟨hne, A, B, hA, hB, hAB⟩ := df_preWalks_of_allReachable_of_entryNoPreds hreach hnp hdf
    exact ⟨x, G.entry, A, B, hx, hS, hne, hA, hB, hAB⟩
  | @step x y _ hdf ih =>
    obtain ⟨hne, A, B, hA, hB, hAB⟩ := df_preWalks_of_allReachable_of_entryNoPreds hreach hnp hdf
    exact inJoinPre_of_insert_join ih ⟨x, G.entry, A, B, Or.inr rfl, Or.inl hS, hne, hA, hB, hAB⟩

/-- **Join sets are closed: `J(S ∪ J(S)) ⊆ J(S)`** (Weiss; Bilardi–Pingali), for every finite
CFG and every set `S`, with no reachability or entry hypothesis. Proof: in the disjoint-pre-walk
form of convergence (`inJoin_iff_preWalks`), a start node in `J(S)` is replaced by walks from `S`
(`inJoinPre_of_join_point`, by strong induction on the length of the walk leaving it). -/
theorem join_union_join_subset_join (G : Cfg n) (S : Fin n → Prop) :
    ∀ z, InJoin G (fun x => S x ∨ InJoin G S x) z → InJoin G S z := by
  intro z hz
  rw [inJoin_iff_preWalks] at hz ⊢
  obtain ⟨u, v, U, V, hu, hv, huv, hU, hV, hUV⟩ := hz
  simp only [inJoin_iff_preWalks] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact ⟨u, v, U, V, hu, hv, huv, hU, hV, hUV⟩
  · obtain ⟨x, y, A, B, hx, hy, hxy, hA, hB, hAB⟩ := hv
    exact inJoinPre_of_join_point G S _ _ _ _ x y A B U V (Nat.le_refl _) hx hy hxy hA hB hAB
      hu hU hV hUV
  · obtain ⟨x, y, A, B, hx, hy, hxy, hA, hB, hAB⟩ := hu
    exact inJoinPre_of_join_point G S _ _ _ _ x y A B V U (Nat.le_refl _) hx hy hxy hA hB hAB
      hv hV hU (fun t h1 h2 => hUV t h2 h1)
  · -- Both endpoints in `J(S)`: first absorb `u` into `J(S ∪ {v})`, then `v` into `J(S)`.
    have hu' : InJoinPre G (fun t => S t ∨ t = v) u := hu.mono fun t ht => Or.inl ht
    obtain ⟨x, y, A, B, hx, hy, hxy, hA, hB, hAB⟩ := hu'
    have hz1 : InJoinPre G (fun t => S t ∨ t = v) z :=
      inJoinPre_of_join_point G _ _ _ _ _ x y A B V U (Nat.le_refl _) hx hy hxy hA hB hAB
        (Or.inr rfl) hV hU (fun t h1 h2 => hUV t h2 h1)
    exact inJoinPre_of_insert_join hv hz1

/-! ### Counterexamples and witnesses for the join/frontier results -/

/-- Unreachable blocks `1 → 3 ← 2` beside an isolated entry `0`. -/
def unreachJoin4 : Cfg 4 := Cfg.ofEdges 4 [(1, 3), (2, 3)] 0

/-- Reachability is necessary for `J(S) ⊆ DF⁺(S)`: with `1, 2, 3` unreachable, `3 ∈ J({1,2})`
but `3 ∉ DF⁺({1,2})` (both `1` and `2` vacuously strictly dominate the unreachable `3`). -/
theorem join_subset_iteratedDF_needs_allReachable :
    ¬ AllReachable unreachJoin4 ∧
    InJoin unreachJoin4 (fun x => x = 1 ∨ x = 2) 3 ∧
    ¬ IDF unreachJoin4 (fun x => x = 1 ∨ x = 2) 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨p, hp⟩ := h 3
    have := not_walk_of_closed unreachJoin4 (fun v => decide (v = 0)) (by decide) hp (by decide)
    exact absurd this (by decide)
  · exact ⟨1, 2, [1, 3], [2, 3], Or.inl rfl, Or.inr rfl, by decide,
      walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩
  · intro h
    have := idf_subset_of_check (G := unreachJoin4) (S := fun x => decide (x = 1) || decide (x = 2))
      (T := fun _ => false) (by decide)
      (y := 3) (by
        have hS : (fun x : Fin 4 => x = 1 ∨ x = 2) =
            (fun x => (decide (x = 1) || decide (x = 2)) = true) := by
          funext x; simp [Bool.or_eq_true]
        rw [← hS]; exact h)
    exact absurd this (by decide)

/-- Single node `0` with a self-loop. -/
def entryLoop1 : Cfg 1 := Cfg.ofEdges 1 [(0, 0)] 0

/-- `EntryNoPreds` is necessary for `DF⁺(S) ⊆ J(S)`: with a self-loop on the entry,
`0 ∈ DF⁺({0})` but `J({0}) = ∅`. -/
theorem iteratedDF_subset_join_needs_entryNoPreds :
    AllReachable entryLoop1 ∧ ¬ EntryNoPreds entryLoop1 ∧
    (fun x => x = (0 : Fin 1)) entryLoop1.entry ∧
    IDF entryLoop1 (fun x => x = 0) 0 ∧ ¬ InJoin entryLoop1 (fun x => x = 0) 0 := by
  refine ⟨?_, fun h => absurd (h 0) (by decide), rfl,
    IDF.base rfl (df_of_check (p := 0) (by decide)), ?_⟩
  · intro b; exact ⟨[0], by
      have : b = 0 := by revert b; decide
      subst this; exact walk_of_isWalkB (by decide)⟩
  · rintro ⟨x, y, _, _, hx, hy, hxy, _⟩
    exact hxy (hx.trans hy.symm)

/-- `S ∋ entry` is necessary for `DF⁺(S) ⊆ J(S)`: in `0 → 1 ↺`, `1 ∈ DF⁺({1})` but
`J({1}) = ∅`. -/
theorem iteratedDF_subset_join_needs_entry_mem :
    AllReachable selfLoop2 ∧ EntryNoPreds selfLoop2 ∧ ¬ (fun x => x = (1 : Fin 2)) selfLoop2.entry ∧
    IDF selfLoop2 (fun x => x = 1) 1 ∧ ¬ InJoin selfLoop2 (fun x => x = 1) 1 := by
  refine ⟨?_, by unfold EntryNoPreds; decide, by decide,
    IDF.base rfl (df_of_check (p := 1) (by decide)), ?_⟩
  · intro b
    have : b = 0 ∨ b = 1 := by revert b; decide
    rcases this with rfl | rfl
    · exact ⟨[0], walk_of_isWalkB (by decide)⟩
    · exact ⟨[0, 1], walk_of_isWalkB (by decide)⟩
  · rintro ⟨x, y, _, _, hx, hy, hxy, _⟩
    exact hxy (hx.trans hy.symm)

/-- Entry `0` (no edges) and an unreachable self-loop on `1`. -/
def unreachLoop2 : Cfg 2 := Cfg.ofEdges 2 [(1, 1)] 0

/-- Reachability is necessary for `DF⁺(S) ⊆ J(S)`: `1 ∈ DF⁺({0,1})` (vacuous dominance at the
unreachable `1`) but `1` has one predecessor, so `1 ∉ J({0,1})`. -/
theorem iteratedDF_subset_join_needs_allReachable :
    ¬ AllReachable unreachLoop2 ∧
    EntryNoPreds unreachLoop2 ∧ (fun x => x = (0 : Fin 2) ∨ x = 1) unreachLoop2.entry ∧
    IDF unreachLoop2 (fun x => x = 0 ∨ x = 1) 1 ∧
    ¬ InJoin unreachLoop2 (fun x => x = 0 ∨ x = 1) 1 := by
  refine ⟨fun h => by
      obtain ⟨p, hp⟩ := h 1
      have := not_walk_of_closed unreachLoop2 (fun v => decide (v = 0)) (by decide) hp (by decide)
      exact absurd this (by decide),
    by unfold EntryNoPreds; decide, Or.inl rfl,
    IDF.base (Or.inr rfl) (df_of_check (p := 1) (by decide)), ?_⟩
  intro h
  obtain ⟨a, b, hab, ha, hb⟩ := inJoin_two_preds h
  revert a b; decide

/-- Non-vacuity of both inclusions: the diamond with `S = {0, 1}`. -/
theorem join_iteratedDF_hyps_nonvacuous :
    AllReachable diamond ∧ EntryNoPreds diamond ∧ (fun x => x = (0 : Fin 4) ∨ x = 1) diamond.entry :=
  ⟨allReachable_diamond, entryNoPreds_diamond, Or.inl rfl⟩

/-- Non-vacuity of join closure: the premise `z ∈ J(S ∪ J(S))` is met in the diamond with
`S = {1, 2}` at `z = 3`. -/
theorem join_union_join_premise_nonvacuous :
    InJoin diamond (fun x => (x = 1 ∨ x = 2) ∨ InJoin diamond (fun x => x = 1 ∨ x = 2) x) 3 :=
  ⟨1, 2, [1, 3], [2, 3], Or.inl (Or.inl rfl), Or.inl (Or.inr rfl), by decide,
    walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩

/-! ## Reaching definitions and φ placement -/

/-- Every walk from `a` to `b` is either clear of `Defs` before `b` or contains a node, at an index
before the last, that reaches the top of `b`. -/
theorem walk_clear_or_reachesTop {G : Cfg n} (Defs : Fin n → Prop)
    {a b : Fin n} {p : List (Fin n)} (hw : Walk G a b p) :
    Clear G Defs a b ∨
      ∃ (i : Fin p.length), i.val + 1 < p.length ∧ ReachesTop G Defs p[i] b := by
  induction hw with
  | single c => exact Or.inl (Clear.here c)
  | @cons a' w' b' p' he hw' ih =>
    rcases ih with hc | ⟨i, hi, hrt⟩
    · by_cases ha : Defs a'
      · have hlen : 0 < p'.length := hw'.length_pos
        exact Or.inr ⟨⟨0, by simp⟩, by simp; exact hlen, ha, w', he, hc⟩
      · exact Or.inl (Clear.step ha he hc)
    · exact Or.inr ⟨⟨i.val + 1, by simp⟩, by simp; exact hi, hrt⟩

/-- A nonnull walk starting in `Defs` has a node, at an index before the last, that reaches the
top of its end. -/
theorem reachesTop_mem_of_walk {G : Cfg n} {Defs : Fin n → Prop}
    {x b : Fin n} {p : List (Fin n)} (hx : Defs x) (hw : Walk G x b p) (hlen : 2 ≤ p.length) :
    ∃ (i : Fin p.length), i.val + 1 < p.length ∧ ReachesTop G Defs p[i] b := by
  cases hw with
  | single => simp at hlen
  | @cons _ w _ p' he hw' =>
    rcases walk_clear_or_reachesTop Defs hw' with hc | ⟨i, hi, hrt⟩
    · exact ⟨⟨0, by simp⟩, by simp; exact hw'.length_pos, hx, w, he, hc⟩
    · exact ⟨⟨i.val + 1, by simp⟩, by simp; exact hi, hrt⟩

/-- Single reaching definitions without the entry exemption: at the top of every block without a
φ (the entry included), at most one definition point of `D ∪ P` reaches. -/
def SingleReachingDefAll (G : Cfg n) (D P : Fin n → Prop) : Prop :=
  ∀ b, ¬ P b → ∀ u v,
    ReachesTop G (fun w => D w ∨ P w) u b → ReachesTop G (fun w => D w ∨ P w) v b → u = v

private theorem edge_pred_of_edge_clear {G : Cfg n} {Defs : Fin n → Prop} {u v b : Fin n}
    (he : G.edge u v = true) (hc : Clear G Defs v b) : ∃ w, G.edge w b = true := by
  induction hc generalizing u with
  | here => exact ⟨u, he⟩
  | step _ he' _ ih => exact ih he'

/-- With no edge into the entry, nothing reaches the top of the entry. -/
theorem not_reachesTop_entry_of_entryNoPreds {G : Cfg n} (hnp : EntryNoPreds G)
    (Defs : Fin n → Prop) (u : Fin n) : ¬ ReachesTop G Defs u G.entry := by
  rintro ⟨_, v, he, hc⟩
  obtain ⟨w, hw⟩ := edge_pred_of_edge_clear he hc
  simp [hnp w] at hw

/-- With no edge into the entry, exempting the entry in `SingleReachingDef` changes nothing. -/
theorem srdAll_iff_srd_of_entryNoPreds {G : Cfg n} (hnp : EntryNoPreds G) (D P : Fin n → Prop) :
    SingleReachingDefAll G D P ↔ SingleReachingDef G D P := by
  constructor
  · intro h b hb _ u v hu hv
    exact h b hb u v hu hv
  · intro h b hb u v hu hv
    by_cases hbe : b = G.entry
    · subst hbe
      exact absurd hu (not_reachesTop_entry_of_entryNoPreds hnp _ u)
    · exact h b hb hbe u v hu hv

/-- **Single reaching definitions without the entry exemption force join closure**, with no
hypothesis on the CFG. -/
theorem joinClosed_of_singleReachingDefAll (G : Cfg n) (D P : Fin n → Prop)
    (h : SingleReachingDefAll G D P) : ∀ z, InJoin G (fun w => D w ∨ P w) z → P z := by
  intro z ⟨x, y, p, q, hx, hy, _, hwp, hwq, lp, lq, hdis⟩
  apply Classical.byContradiction
  intro hnz
  obtain ⟨i, hi, hpi⟩ := reachesTop_mem_of_walk (Defs := fun w => D w ∨ P w) hx hwp lp
  obtain ⟨j, hj, hqj⟩ := reachesTop_mem_of_walk (Defs := fun w => D w ∨ P w) hy hwq lq
  have heq : p[i] = q[j] := h z hnz p[i] q[j] hpi hqj
  rcases hdis i j heq with h1 | h2
  · omega
  · omega


/-- A `Clear` derivation as a list: a walk whose nodes before the last lie outside `Defs`. -/
theorem Clear.exists_walk {G : Cfg n} {Defs : Fin n → Prop} {v b : Fin n} (h : Clear G Defs v b) :
    ∃ p, Walk G v b p ∧ ∀ (k : Nat) (hk : k + 1 < p.length), ¬ Defs (p[k]'(by omega)) := by
  induction h with
  | here b => exact ⟨[b], Walk.single _, fun k hk => by simp at hk⟩
  | @step v w b hv he _ ih =>
    obtain ⟨p, hp, hcl⟩ := ih
    refine ⟨v :: p, Walk.cons he hp, fun k hk => ?_⟩
    cases k with
    | zero => simpa using hv
    | succ k => simpa using hcl k (by simp at hk; omega)

/-- The walk behind `ReachesTop G Defs u b`: nonnull, from `u` to `b`, interior nodes outside
`Defs`. -/
theorem ReachesTop.exists_walk {G : Cfg n} {Defs : Fin n → Prop} {u b : Fin n}
    (h : ReachesTop G Defs u b) :
    ∃ p, Walk G u b p ∧ 2 ≤ p.length ∧
      ∀ (k : Nat) (hk : k + 1 < p.length), 1 ≤ k → ¬ Defs (p[k]'(by omega)) := by
  obtain ⟨_, w, he, hc⟩ := h
  obtain ⟨p, hp, hcl⟩ := hc.exists_walk
  refine ⟨u :: p, Walk.cons he hp, by simp; exact hp.length_pos, fun k hk h1 => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simpa using hcl k' (by simp at hk; omega)

/-- A prefix of a walk is a walk to the prefix's last node. -/
theorem Walk.take_succ {G : Cfg n} {a c : Fin n} {p : List (Fin n)} (h : Walk G a c p) :
    ∀ (i : Nat) (hi : i < p.length), Walk G a (p[i]) (p.take (i + 1)) := by
  induction h with
  | single a =>
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    exact Walk.single a
  | @cons a' b' c' p' he hw ih =>
    intro i hi
    cases i with
    | zero => exact Walk.single a'
    | succ i =>
      have := ih i (by simp at hi; omega)
      simpa using Walk.cons he this

private theorem exists_min_nat {Q : Nat → Prop} (h : ∃ i, Q i) : ∃ i, Q i ∧ ∀ k < i, ¬ Q k := by
  have key : ∀ N, ∀ i ≤ N, Q i → ∃ i, Q i ∧ ∀ k < i, ¬ Q k := by
    intro N
    induction N with
    | zero =>
      intro i hi hq
      have : i = 0 := by omega
      subst this
      exact ⟨0, hq, fun k hk => absurd hk (by omega)⟩
    | succ N ih =>
      intro i hi hq
      by_cases hlt : ∃ k < i, Q k
      · obtain ⟨k, hk, hqk⟩ := hlt
        exact ih k (by omega) hqk
      · exact ⟨i, hq, fun k hk hqk => hlt ⟨k, hk, hqk⟩⟩
  obtain ⟨i, hi⟩ := h
  exact key i i (Nat.le_refl _) hi

/-- Every node on a walk starts a suffix walk to the same end. -/
theorem Walk.suffix_from {G : Cfg n} {a b v : Fin n} {p : List (Fin n)} (h : Walk G a b p)
    (hv : v ∈ p) : ∃ q, Walk G v b q := by
  induction h with
  | single a' =>
    have : v = a' := by simpa using hv
    subst this
    exact ⟨[v], Walk.single _⟩
  | @cons a' b' c' p' he hw ih =>
    by_cases hva : v = a'
    · subst hva; exact ⟨_, Walk.cons he hw⟩
    · rcases List.mem_cons.mp hv with h | h
      · exact absurd h hva
      · exact ih h

/-- If `w` dominates `d ≠ w` and `w` is reachable, some walk from the entry to `w` avoids `d` (a
shortest walk to `w` does). -/
theorem exists_walk_avoid_of_dom {G : Cfg n} {w d : Fin n} (hwd : Dom G w d) (hne : w ≠ d)
    (hw : Reachable G w) : ∃ q, Walk G G.entry w q ∧ d ∉ q := by
  have hex : ∃ k, ∃ q, Walk G G.entry w q ∧ q.length = k := by
    obtain ⟨q, hq⟩ := hw; exact ⟨q.length, q, hq, rfl⟩
  obtain ⟨k, ⟨q, hq, hql⟩, hmin⟩ := exists_min_nat hex
  refine ⟨q, hq, fun hd => ?_⟩
  obtain ⟨r, hr, _, _, hrl⟩ := hq.prefix_to hd
  obtain ⟨t, ht, _, htl, _⟩ := hr.prefix_to (hwd r hr)
  have := hrl (Ne.symm hne)
  exact hmin t.length (by omega) ⟨t, ht, rfl⟩

/-- **A join-closed placement has single reaching definitions at every block without a φ, the
entry included**: if `J(D ∪ P) ⊆ P` then at most one definition point of `D ∪ P` reaches the top
of any block outside `P`. Two distinct reaching definitions are cut at the first node of the
first walk that occurs (at a positive index) on the second; the cut walks converge there, so that
node is in `J(D ∪ P) ⊆ P`, which is impossible for an interior node of a definition-free walk and
for the end block `b ∉ P`. -/
theorem singleReachingDefAll_of_joinClosed (G : Cfg n) (D P : Fin n → Prop)
    (hclosed : ∀ z, InJoin G (fun w => D w ∨ P w) z → P z) : SingleReachingDefAll G D P := by
  intro b hb u v hu hv
  apply Classical.byContradiction
  intro huv
  have hDu := hu.1
  have hDv := hv.1
  obtain ⟨p, hwp, lp, hip⟩ := hu.exists_walk
  obtain ⟨q, hwq, lq, hiq⟩ := hv.exists_walk
  have hp0 : ∀ (k : Nat) (hk : k < p.length), k = 0 → p[k] = u := by
    intro k hk h; subst h; exact hwp.getElem_zero hk
  have hq0 : ∀ (k : Nat) (hk : k < q.length), k = 0 → q[k] = v := by
    intro k hk h; subst h; exact hwq.getElem_zero hk
  have hex : ∃ i, ∃ (hi : i < p.length) (j : Nat) (hj : j < q.length),
      1 ≤ i ∧ 1 ≤ j ∧ p[i] = q[j] :=
    ⟨p.length - 1, by omega, q.length - 1, by omega, by omega, by omega,
      by rw [hwp.getElem_last, hwq.getElem_last]⟩
  obtain ⟨i, ⟨hi, j, hj, hi1, hj1, hpq⟩, hmin⟩ := exists_min_nat hex
  have hconv : Converge G u v p[i] (p.take (i + 1)) (q.take (j + 1)) := by
    refine ⟨huv, hwp.take_succ i hi, by rw [hpq]; exact hwq.take_succ j hj, by simp; omega,
      by simp; omega, ?_⟩
    intro i' j' heq
    have hi' : i'.val < i + 1 := by have := i'.isLt; simp at this; omega
    have hj' : j'.val < j + 1 := by have := j'.isLt; simp at this; omega
    have heq' : p[i'.val]'(by omega) = q[j'.val]'(by omega) := by simpa using heq
    by_cases hli : i'.val = i
    · left; simp; omega
    by_cases hlj : j'.val = j
    · right; simp; omega
    exfalso
    rcases Nat.eq_zero_or_pos i'.val with h0 | h0
    · rcases Nat.eq_zero_or_pos j'.val with h0' | h0'
      · exact huv ((hp0 _ _ h0).symm.trans (heq'.trans (hq0 _ _ h0')))
      · apply hiq j'.val (by omega) h0'
        rw [← heq', hp0 _ _ h0]
        exact hDu
    · rcases Nat.eq_zero_or_pos j'.val with h0' | h0'
      · apply hip i'.val (by omega) h0
        rw [heq', hq0 _ _ h0']
        exact hDv
      · exact hmin i'.val (by omega) ⟨by omega, j'.val, by omega, h0, h0', heq'⟩
  have hPz : P p[i] := hclosed _ ⟨u, v, _, _, hDu, hDv, hconv⟩
  by_cases hlast : i + 1 < p.length
  · exact hip i hlast hi1 (Or.inr hPz)
  · have : i = p.length - 1 := by omega
    subst this
    rw [hwp.getElem_last] at hPz
    exact hb hPz

/-- **A join-closed placement has single reaching definitions**: if `J(D ∪ P) ⊆ P` then at the
top of every non-entry block without a φ at most one definition point of `D ∪ P` reaches.
No reachability or entry hypothesis. -/
theorem singleReachingDef_of_joinClosed (G : Cfg n) (D P : Fin n → Prop)
    (hclosed : ∀ z, InJoin G (fun w => D w ∨ P w) z → P z) : SingleReachingDef G D P :=
  fun b hb _ u v hu hv => singleReachingDefAll_of_joinClosed G D P hclosed b hb u v hu hv

/-- **Single reaching definitions force join closure** when no edge enters the entry:
`SingleReachingDef G D P → J(D ∪ P) ⊆ P`. -/
theorem joinClosed_of_entryNoPreds_of_singleReachingDef (G : Cfg n) (D P : Fin n → Prop)
    (hnp : EntryNoPreds G) (h : SingleReachingDef G D P) :
    ∀ z, InJoin G (fun w => D w ∨ P w) z → P z :=
  joinClosed_of_singleReachingDefAll G D P ((srdAll_iff_srd_of_entryNoPreds hnp D P).mpr h)

/-- **Placing φs at `J(D)` gives single reaching definitions**, for every CFG and every `D`.
Derived from join closure and `singleReachingDef_of_joinClosed`. -/
theorem singleReachingDef_at_join (G : Cfg n) (D : Fin n → Prop) :
    SingleReachingDef G D (InJoin G D) :=
  singleReachingDef_of_joinClosed G D (InJoin G D) (join_union_join_subset_join G D)

/-- `DF⁺(S ∪ DF⁺(S)) ⊆ DF⁺(S)`. -/
theorem idf_union_idf_subset {G : Cfg n} {S : Fin n → Prop} {y : Fin n}
    (h : IDF G (fun x => S x ∨ IDF G S x) y) : IDF G S y := by
  induction h with
  | base hx hdf =>
    rcases hx with hx | hx
    · exact IDF.base hx hdf
    · exact IDF.step hx hdf
  | step _ hdf ih => exact IDF.step ih hdf

/-- **Some definition reaches every reachable non-entry block** once the entry is a definition
point (it carries the initial value), for any placement `P`. -/
theorem exists_reachesTop_of_entry_mem (G : Cfg n) (D P : Fin n → Prop) (hD : D G.entry)
    {b : Fin n} (hb : Reachable G b) (hbe : b ≠ G.entry) :
    ∃ u, ReachesTop G (fun w => D w ∨ P w) u b := by
  obtain ⟨p, hw⟩ := hb
  have hlen : 2 ≤ p.length := by
    cases hw with
    | single => exact absurd rfl hbe
    | cons _ hw' => simp; exact hw'.length_pos
  obtain ⟨i, _, hrt⟩ := reachesTop_mem_of_walk (Defs := fun w => D w ∨ P w) (Or.inl hD) hw hlen
  exact ⟨p[i], hrt⟩

/-- **Dominator-tree renaming reads the reaching definition**: with every node reachable and φs
at `DF⁺(D)`, at the top of every block `b ∉ DF⁺(D)` the definition points of `D ∪ DF⁺(D)` that
reach are exactly the nearest strictly dominating definition point (so there is none when no
definition point strictly dominates `b`). -/
theorem reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf (G : Cfg n) (D : Fin n → Prop)
    (hreach : AllReachable G) {b : Fin n} (hb : ¬ IDF G D b) (u : Fin n) :
    ReachesTop G (fun w => D w ∨ IDF G D w) u b ↔
      NearestSDomDef G (fun w => D w ∨ IDF G D w) b u := by
  -- A definition point reaching the top of `b ∉ DF⁺(D)` strictly dominates `b` (Cytron et al.,
  -- Lemma 5 along the definition-free walk).
  have hsdom : ∀ w, ReachesTop G (fun w => D w ∨ IDF G D w) w b → SDom G w b := by
    intro w hw
    apply Classical.byContradiction
    intro hns
    obtain ⟨c, hc, lc, hic⟩ := hw.exists_walk
    have hex : ∃ k, ∃ (hk : k < c.length), 1 ≤ k ∧ ¬ SDom G w c[k] :=
      ⟨c.length - 1, by omega, by omega, by rw [hc.getElem_last]; exact hns⟩
    obtain ⟨k, ⟨hk, hk1, hnk⟩, hmin⟩ := exists_min_nat hex
    have hpred : Dom G w (c[k - 1]'(by omega)) := by
      by_cases h1 : k - 1 = 0
      · have h0 : ∀ (j : Nat) (hj : j < c.length), j = 0 → c[j] = w := by
          intro j hj hj0; subst hj0; exact hc.getElem_zero hj
        rw [h0 (k - 1) (by omega) h1]
        exact dom_refl _ _
      · apply Classical.byContradiction
        intro hnd
        exact hmin (k - 1) (by omega) ⟨by omega, by omega, fun hs => hnd hs.1⟩
    have he := hc.edge_getElem (k - 1) (by omega)
    have hk' : k - 1 + 1 = k := by omega
    simp only [hk'] at he
    have hdf : DF G w c[k] := ⟨⟨_, he, hpred⟩, hnk⟩
    have hidf : IDF G D c[k] := by
      rcases hw.1 with hD | hI
      · exact IDF.base hD hdf
      · exact IDF.step hI hdf
    by_cases hlast : k + 1 < c.length
    · exact hic k hlast hk1 (Or.inr hidf)
    · have : k = c.length - 1 := by omega
      subst this
      rw [hc.getElem_last] at hidf
      exact hb hidf
  -- Nodes after the first on a definition-free walk to `b` are `b` or lie outside the
  -- definition points.
  have htail : ∀ w (c : List (Fin n)), Walk G w b c →
      (∀ (k : Nat) (hk : k + 1 < c.length), 1 ≤ k → ¬ (D (c[k]'(by omega)) ∨ IDF G D (c[k]'(by omega)))) →
      ∀ v ∈ c.tail, v = b ∨ ¬ (D v ∨ IDF G D v) := by
    intro w c hc hic v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi' : i + 1 < c.length := by simp at hi; omega
    rw [List.getElem_tail]
    by_cases hl : i + 1 + 1 < c.length
    · exact Or.inr (hic (i + 1) hl (by omega))
    · left
      have : i + 1 = c.length - 1 := by omega
      simp only [this]
      exact hc.getElem_last _
  constructor
  · intro hu
    refine ⟨hu.1, hsdom u hu, fun d' hd' hsd' => ?_⟩
    apply Classical.byContradiction
    intro hnd
    have hex : ∃ q, Walk G G.entry u q ∧ d' ∉ q := by
      apply Classical.byContradiction
      intro hno
      apply hnd
      intro q hq
      apply Classical.byContradiction
      intro hdq
      exact hno ⟨q, hq, hdq⟩
    obtain ⟨q, hq, hnq⟩ := hex
    obtain ⟨c, hc, _, hic⟩ := hu.exists_walk
    have hmem := hsd'.1 _ (hq.append hc)
    rcases List.mem_append.mp hmem with h | h
    · exact hnq h
    · rcases htail u c hc hic d' h with h' | h'
      · exact hsd'.2 h'
      · exact h' hd'
  · rintro ⟨hdD, hdS, hdN⟩
    obtain ⟨p, hp⟩ := hreach b
    obtain ⟨s, hs⟩ := hp.suffix_from (hdS.1 p hp)
    have ls : 2 ≤ s.length := by
      cases hs with
      | single => exact absurd rfl hdS.2
      | cons _ hw' => simp; exact hw'.length_pos
    obtain ⟨i, _, hrt⟩ := reachesTop_mem_of_walk (Defs := fun w => D w ∨ IDF G D w) hdD hs ls
    by_cases hwd : s[i] = u
    · rw [← hwd]; exact hrt
    · exfalso
      have hsw := hsdom _ hrt
      have hwdom : Dom G s[i] u := hdN _ hrt.1 hsw
      obtain ⟨q, hq, hnq⟩ := exists_walk_avoid_of_dom hwdom hwd
        (Reachable.of_dom hsw.1 (hreach b))
      obtain ⟨c, hc, _, hic⟩ := hrt.exists_walk
      have hmem := hdS.1 _ (hq.append hc)
      rcases List.mem_append.mp hmem with h | h
      · exact hnq h
      · rcases htail _ c hc hic u h with h' | h'
        · exact hdS.2 h'
        · exact h' hdD

/-! ### Consequences: join sets inside `DF⁺`, and placement at `DF⁺` -/

/-- **`J(S) ⊆ DF⁺(S)`** when every node is reachable from the entry (Cytron et al., Lemma 6).
No condition on `S`. Proof: if `z ∉ DF⁺(S)`, the last definition points of `S ∪ DF⁺(S)` on the two
converging walks both reach `z` and are therefore both the nearest strictly dominating
definition point of `z`, i.e. the same node, at a non-final index of both walks. -/
theorem join_subset_iteratedDF_of_allReachable (G : Cfg n) (S : Fin n → Prop)
    (hreach : AllReachable G) : ∀ z, InJoin G S z → IDF G S z := by
  intro z ⟨x, y, p, q, hx, hy, _, hwp, hwq, lp, lq, hdis⟩
  apply Classical.byContradiction
  intro hz
  obtain ⟨i, hi, hpi⟩ := reachesTop_mem_of_walk (Defs := fun w => S w ∨ IDF G S w) (Or.inl hx) hwp lp
  obtain ⟨j, hj, hqj⟩ := reachesTop_mem_of_walk (Defs := fun w => S w ∨ IDF G S w) (Or.inl hy) hwq lq
  have h1 := (reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf G S hreach hz _).mp hpi
  have h2 := (reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf G S hreach hz _).mp hqj
  have heq : p[i] = q[j] := dom_antisymm (h2.2.2 _ h1.1 h1.2.1) (h1.2.2 _ h2.1 h2.2.1)
    (Reachable.of_dom h1.2.1.1 (hreach z))
  rcases hdis i j heq with h | h <;> omega

/-- **`J(S) = DF⁺(S)`** under the hypotheses of both inclusions (Cytron et al., Theorem 2 with
Weiss's `J⁺ = J`). Derived from the two inclusions. -/
theorem join_eq_iteratedDF_of_allReachable_of_entryNoPreds_of_entry_mem (G : Cfg n) (S : Fin n → Prop)
    (hreach : AllReachable G) (hnp : EntryNoPreds G) (hS : S G.entry) :
    ∀ z, InJoin G S z ↔ IDF G S z := fun z =>
  ⟨join_subset_iteratedDF_of_allReachable G S hreach z,
   iteratedDF_subset_join_of_allReachable_of_entryNoPreds_of_entry_mem G S hreach hnp hS z⟩

/-- **Placing φs at `DF⁺(D)` gives single reaching definitions** when every node is reachable.
Derived from `J ⊆ DF⁺` (reachability), `DF⁺(D ∪ DF⁺(D)) ⊆ DF⁺(D)`, and
`singleReachingDef_of_joinClosed`. -/
theorem singleReachingDef_at_iteratedDF_of_allReachable (G : Cfg n) (D : Fin n → Prop)
    (hreach : AllReachable G) : SingleReachingDef G D (IDF G D) :=
  singleReachingDef_of_joinClosed G D (IDF G D) fun z hz =>
    idf_union_idf_subset (join_subset_iteratedDF_of_allReachable G _ hreach z hz)

/-- **Exactly one reaching definition with φs at `DF⁺(D)`**: every node reachable and the entry a
definition point; then every non-entry block without a φ is reached by exactly one definition
point. Derived from the two previous results. -/
theorem existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry (G : Cfg n) (D : Fin n → Prop)
    (hreach : AllReachable G) (hD : D G.entry) {b : Fin n} (hb : ¬ IDF G D b)
    (hbe : b ≠ G.entry) : ∃ u, ReachesTop G (fun w => D w ∨ IDF G D w) u b ∧
      ∀ v, ReachesTop G (fun w => D w ∨ IDF G D w) v b → v = u := by
  obtain ⟨u, hu⟩ := exists_reachesTop_of_entry_mem G D (IDF G D) hD (hreach b) hbe
  exact ⟨u, hu, fun v hv =>
    singleReachingDef_at_iteratedDF_of_allReachable G D hreach b hb hbe v u hv hu⟩

/-- **Minimality: every placement with single reaching definitions contains `J(D)`** when no edge
enters the entry. Hence a strict subset of `J(D)` always leaves a block whose top is reached by
two definitions. Derived from `joinClosed_of_entryNoPreds_of_singleReachingDef` (`J` is monotone). -/
theorem join_subset_of_entryNoPreds_of_singleReachingDef (G : Cfg n) (D P : Fin n → Prop)
    (hnp : EntryNoPreds G) (h : SingleReachingDef G D P) : ∀ z, InJoin G D z → P z := by
  intro z ⟨x, y, p, q, hx, hy, hc⟩
  exact joinClosed_of_entryNoPreds_of_singleReachingDef G D P hnp h z ⟨x, y, p, q, Or.inl hx, Or.inl hy, hc⟩

/-! ### Counterexamples and witnesses for the placement results -/

/-- Non-vacuity of `singleReachingDef_of_joinClosed`: in the diamond, `D = {0, 1}` and `P = {3}`
is join-closed (every join node has two predecessors, and only `3` does). -/
theorem joinClosed_diamond_example :
    ∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ w = 3) z → z = 3 := by
  intro z hz
  obtain ⟨a, b, hab, ha, hb⟩ := inJoin_two_preds hz
  clear hz
  revert z a b; decide

/-- Non-vacuity of `joinClosed_of_entryNoPreds_of_singleReachingDef` and `join_subset_of_entryNoPreds_of_singleReachingDef`: the
diamond with `D = {0, 1}`, `P = {3}`. -/
theorem srd_hyps_nonvacuous :
    EntryNoPreds diamond ∧
    SingleReachingDef diamond (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => decide (w = 3) = true) :=
  ⟨entryNoPreds_diamond, srd_example⟩

/-- Non-vacuity of `joinClosed_of_singleReachingDefAll`: the diamond with `D = {0, 1}` and
`P = {3}` satisfies `SingleReachingDefAll`. -/
theorem srdAll_hyps_nonvacuous :
    SingleReachingDefAll diamond (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => decide (w = 3) = true) :=
  (srdAll_iff_srd_of_entryNoPreds srd_hyps_nonvacuous.1 _ _).mpr srd_hyps_nonvacuous.2

/-- Entry `0` with a self-loop, `0 → 1`, `1 → 0`. -/
def entryCycle2 : Cfg 2 := Cfg.ofEdges 2 [(0, 0), (0, 1), (1, 0)] 0

/-- `EntryNoPreds` is necessary for `joinClosed_of_entryNoPreds_of_singleReachingDef` and for
`join_subset_of_entryNoPreds_of_singleReachingDef`: with `D = {0, 1}` and no φ, single reaching definitions hold
(the only constrained block is `1`), but `0 ∈ J(D)` carries no φ. -/
theorem srd_join_needs_entryNoPreds :
    ¬ EntryNoPreds entryCycle2 ∧
    SingleReachingDef entryCycle2 (fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w => (fun _ => false : Fin 2 → Bool) w = true) ∧
    InJoin entryCycle2 (fun w => (decide (w = 0) || decide (w = 1)) = true ∨
      (fun _ => false : Fin 2 → Bool) w = true) 0 ∧
    InJoin entryCycle2 (fun w => (decide (w = 0) || decide (w = 1)) = true) 0 ∧
    ¬ (fun _ => false : Fin 2 → Bool) 0 = true := by
  refine ⟨fun h => absurd (h 0) (by decide), srd_of_check (by decide), ?_, ?_, by decide⟩
  · exact ⟨0, 1, [0, 0], [1, 0], Or.inl rfl, Or.inl rfl, by decide,
      walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩
  · exact ⟨0, 1, [0, 0], [1, 0], rfl, rfl, by decide,
      walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩

/-- Extra φs can satisfy `SingleReachingDef` without join closure when an edge enters the entry:
on `entryCycle2` with `D = {0}`, `J(D)` is empty and the extra φ placement `P = {1}` satisfies
`SingleReachingDef entryCycle2 D P` (the entry `0` is exempt and `1 ∈ P`), yet `P` is not
join-closed: `0 ∈ J(D ∪ P)` and `0 ∉ P`. -/
theorem extra_phi_srd_without_joinClosed_when_entryPred :
    ¬ EntryNoPreds entryCycle2 ∧
    (∀ z, ¬ InJoin entryCycle2 (fun w => w = 0) z) ∧
    SingleReachingDef entryCycle2 (fun w => w = 0) (fun w => w = 1) ∧
    InJoin entryCycle2 (fun w => w = 0 ∨ w = 1) 0 ∧
    ¬ (fun w : Fin 2 => w = 1) 0 := by
  refine ⟨fun h => absurd (h 0) (by decide), ?_, ?_, ?_, by decide⟩
  · rintro z ⟨x, y, _, _, hx, hy, hne, _⟩
    exact hne (hx.trans hy.symm)
  · intro b hb hbe
    have : b = 0 ∨ b = 1 := by revert b; decide
    rcases this with rfl | rfl
    · exact absurd rfl hbe
    · exact absurd rfl hb
  · exact ⟨0, 1, [0, 0], [1, 0], Or.inl rfl, Or.inr rfl, by decide,
      walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩

/-- Witness for `singleReachingDef_at_join`: in the diamond with `D = {0, 1}`, `J(D)` is
nonempty (`3 ∈ J(D)` via `0 → 2 → 3` and `1 → 3`), so the placement is not trivial. -/
theorem join_placement_nonempty_example : InJoin diamond (fun w => w = 0 ∨ w = 1) 3 :=
  ⟨0, 1, [0, 2, 3], [1, 3], Or.inl rfl, Or.inr rfl, by decide,
    walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩

/-- Reachability is necessary for `singleReachingDef_at_iteratedDF_of_allReachable`: with `1, 2,
3` unreachable and `D = {0, 1, 2}`, `DF⁺(D) = ∅` and the top of `3` is reached from both `1` and
`2`. -/
theorem srd_iteratedDF_needs_allReachable :
    ¬ AllReachable unreachJoin4 ∧
    ¬ SingleReachingDef unreachJoin4
      (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true)
      (IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true)) := by
  refine ⟨join_subset_iteratedDF_needs_allReachable.1, fun h => ?_⟩
  have hnot : ∀ y, ¬ IDF unreachJoin4
      (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) y := by
    intro y hy
    have := idf_subset_of_check (G := unreachJoin4)
      (S := fun w => decide (w = 0) || decide (w = 1) || decide (w = 2))
      (T := fun _ => false) (by decide) hy
    exact absurd this (by decide)
  have := h 3 (hnot 3) (by decide) 1 2
    ⟨Or.inl (by decide), 3, by decide, Clear.here _⟩
    ⟨Or.inl (by decide), 3, by decide, Clear.here _⟩
  exact absurd this (by decide)

/-- Non-vacuity of the reachability-only results: the diamond is fully reachable. -/
theorem allReachable_nonvacuous : AllReachable diamond := allReachable_diamond

/-- The entry must be a definition point for `exists_reachesTop_of_entry_mem`: in the chain with
`D = P = ∅`, nothing reaches the reachable block `1`. -/
theorem exists_reachesTop_needs_entry_mem :
    ¬ (fun _ => False : Fin 3 → Prop) chain3.entry ∧ Reachable chain3 1 ∧ (1 : Fin 3) ≠ chain3.entry ∧
    ¬ ∃ u, ReachesTop chain3 (fun w => (fun _ => False : Fin 3 → Prop) w ∨
      (fun _ => False : Fin 3 → Prop) w) u 1 := by
  refine ⟨id, ⟨[0, 1], walk_of_isWalkB (by decide)⟩, by decide, ?_⟩
  rintro ⟨u, hu, _⟩
  simp at hu

/-- Reachability of the block is necessary for `exists_reachesTop_of_entry_mem`. -/
theorem exists_reachesTop_needs_reachable :
    (fun w => w = (0 : Fin 2)) isolated2.entry ∧ ¬ Reachable isolated2 1 ∧
    (1 : Fin 2) ≠ isolated2.entry ∧
    ¬ ∃ u, ReachesTop isolated2 (fun w => w = 0 ∨ (fun _ => False : Fin 2 → Prop) w) u 1 := by
  refine ⟨rfl, fun ⟨p, hp⟩ => absurd
      (not_walk_of_closed isolated2 (fun v => decide (v = 0)) (by decide) hp (by decide))
      (by decide), by decide, ?_⟩
  rintro ⟨u, -, v, he, -⟩
  have : ∀ u v : Fin 2, isolated2.edge u v = false := by decide
  simp [this] at he

/-- `b ≠ entry` is necessary for `exists_reachesTop_of_entry_mem`: nothing reaches the top of the
entry of the diamond (no edge enters it). -/
theorem exists_reachesTop_needs_ne_entry :
    (fun w : Fin 4 => w = 0) diamond.entry ∧ Reachable diamond 0 ∧
    ¬ ((0 : Fin 4) ≠ diamond.entry) ∧
    ¬ ∃ u, ReachesTop diamond (fun w => w = 0 ∨ (fun _ => False : Fin 4 → Prop) w) u 0 := by
  refine ⟨rfl, ⟨[0], Walk.single _⟩, fun h => h rfl, ?_⟩
  rintro ⟨u, hu⟩
  exact not_reachesTop_entry_of_entryNoPreds entryNoPreds_diamond _ u hu

/-- `b ∉ DF⁺(D)` is necessary for the uniqueness corollary and for the renaming result: at the
diamond's join `3` (with `D = {0, 1}`), both `1` and `0` (via `2`) reach, and `1` does not
strictly dominate `3`. -/
theorem reachesTop_at_phi_block_example :
    AllReachable diamond ∧ IDF diamond (fun w => w = 0 ∨ w = 1) 3 ∧
    ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w) 1 3 ∧
    ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w) 0 3 ∧
    ¬ NearestSDomDef diamond
      (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w) 3 1 := by
  have h2 : ¬ IDF diamond (fun w => w = 0 ∨ w = 1) 2 := by
    intro h
    have h' := IDF.mono (S' := fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w hw => by rcases hw with rfl | rfl <;> decide) h
    have := idf_subset_of_check (G := diamond) (S := fun w => decide (w = 0) || decide (w = 1))
      (T := fun w => decide (w = 3)) (by decide) h'
    exact absurd this (by decide)
  refine ⟨allReachable_diamond, IDF.base (x := 1) (Or.inr rfl) df_example,
    ⟨Or.inl (Or.inr rfl), 3, by decide, Clear.here _⟩,
    ⟨Or.inl (Or.inl rfl), 2, by decide, Clear.step ?_ (by decide) (Clear.here _)⟩, ?_⟩
  · rintro (h | h)
    · rcases h with h | h <;> exact absurd h (by decide)
    · exact h2 h
  · rintro ⟨_, hsd, _⟩
    exact not_dom_example hsd.1

/-- Reachability is necessary for `reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf`: in `isolated2`
with `D = {0}`, the unreachable `1` is vacuously strictly dominated by `0`, so `0` is its nearest
strictly dominating definition point, yet nothing reaches it. -/
theorem reachesTop_iff_needs_allReachable :
    ¬ AllReachable isolated2 ∧ ¬ IDF isolated2 (fun w => w = 0) 1 ∧
    NearestSDomDef isolated2 (fun w => w = 0 ∨ IDF isolated2 (fun w => w = 0) w) 1 0 ∧
    ¬ ReachesTop isolated2 (fun w => w = 0 ∨ IDF isolated2 (fun w => w = 0) w) 0 1 := by
  have hnot : ∀ y, ¬ IDF isolated2 (fun w => w = 0) y := by
    intro y hy
    have h' := IDF.mono (S' := fun w => decide (w = 0) = true) (fun w hw => by simp [hw]) hy
    have := idf_subset_of_check (G := isolated2) (S := fun w => decide (w = 0))
      (T := fun _ => false) (by decide) h'
    exact absurd this (by decide)
  refine ⟨not_allReachable_isolated2, hnot 1, ⟨Or.inl rfl, ⟨dom_of_domCheck (by decide), by decide⟩, ?_⟩, ?_⟩
  · intro d' hd' _
    rcases hd' with rfl | h
    · exact dom_refl _ _
    · exact absurd h (hnot d')
  · rintro ⟨-, v, he, -⟩
    have : ∀ u v : Fin 2, isolated2.edge u v = false := by decide
    simp [this] at he

/-! ### Minimality on the diamond and on a loop -/

/-- **Diamond**: `D = {0, 1}`, no φ (a strict subset of `J(D) = {3}`): two definitions reach the
top of `3`. -/
theorem strict_subset_of_join_two_defs_diamond :
    (∀ z, (fun _ => False : Fin 4 → Prop) z → InJoin diamond (fun w => w = 0 ∨ w = 1) z) ∧
    InJoin diamond (fun w => w = 0 ∨ w = 1) 3 ∧ ¬ (fun _ => False : Fin 4 → Prop) 3 ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) :=
  ⟨fun _ h => h.elim, join_placement_nonempty_example, id, not_srd_example⟩

/-- **Loop**: `D = {0, 2}` (initial value and an assignment in the loop body of `loop4`), no φ (a
strict subset of `J(D) ∋ 1`): the header `1` is reached from the entry and from the body. -/
theorem strict_subset_of_join_two_defs_loop :
    (∀ z, (fun _ => False : Fin 4 → Prop) z → InJoin loop4 (fun w => w = 0 ∨ w = 2) z) ∧
    InJoin loop4 (fun w => w = 0 ∨ w = 2) 1 ∧ ¬ (fun _ => False : Fin 4 → Prop) 1 ∧
    ¬ SingleReachingDef loop4 (fun w => w = 0 ∨ w = 2) (fun _ => False) := by
  refine ⟨fun _ h => h.elim, ⟨0, 2, [0, 1], [2, 1], Or.inl rfl, Or.inr rfl, by decide,
    walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩,
    id, fun h => ?_⟩
  have := h 1 id (by decide) 0 2
    ⟨Or.inl (Or.inl rfl), 1, by decide, Clear.here _⟩
    ⟨Or.inl (Or.inr rfl), 1, by decide, Clear.here _⟩
  exact absurd this (by decide)

/-! ### Counterexamples for the exactly-one corollary -/

theorem allReachable_chain3 : AllReachable chain3 := by
  intro b
  have : b = 0 ∨ b = 1 ∨ b = 2 := by revert b; decide
  rcases this with rfl | rfl | rfl
  · exact ⟨[0], walk_of_isWalkB (by decide)⟩
  · exact ⟨[0, 1], walk_of_isWalkB (by decide)⟩
  · exact ⟨[0, 1, 2], walk_of_isWalkB (by decide)⟩

/-- `D ∋ entry` is necessary for `existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry`: with `D = ∅` nothing
reaches block `1` of the chain. -/
theorem existsUnique_needs_entry_mem :
    AllReachable chain3 ∧ ¬ (fun _ => False : Fin 3 → Prop) chain3.entry ∧
    ¬ IDF chain3 (fun _ => False) 1 ∧ (1 : Fin 3) ≠ chain3.entry ∧
    ¬ ∃ u, ReachesTop chain3 (fun w => (fun _ => False : Fin 3 → Prop) w ∨
      IDF chain3 (fun _ => False) w) u 1 := by
  have hnot : ∀ y, ¬ IDF chain3 (fun _ => False) y := by
    intro y hy
    induction hy with
    | base hx _ => exact hx
    | step _ _ ih => exact ih
  refine ⟨allReachable_chain3, id, hnot 1, by decide, ?_⟩
  rintro ⟨u, hu, _⟩
  rcases hu with h | h
  · exact h
  · exact hnot u h

/-- Reachability is necessary for `existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry` (two definitions reach
the unreachable `3` in `unreachJoin4` with `D = {0, 1, 2}`). -/
theorem existsUnique_needs_allReachable :
    ¬ AllReachable unreachJoin4 ∧
    (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) unreachJoin4.entry ∧
    ¬ IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) 3 ∧
    (3 : Fin 4) ≠ unreachJoin4.entry ∧
    ¬ ∃ u, ReachesTop unreachJoin4
        (fun w => (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w ∨
          IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w)
        u 3 ∧
      ∀ v, ReachesTop unreachJoin4
        (fun w => (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w ∨
          IDF unreachJoin4 (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) w)
        v 3 → v = u := by
  have hnot : ∀ y, ¬ IDF unreachJoin4
      (fun w => (decide (w = 0) || decide (w = 1) || decide (w = 2)) = true) y := by
    intro y hy
    have := idf_subset_of_check (G := unreachJoin4)
      (S := fun w => decide (w = 0) || decide (w = 1) || decide (w = 2))
      (T := fun _ => false) (by decide) hy
    exact absurd this (by decide)
  refine ⟨join_subset_iteratedDF_needs_allReachable.1, by decide, hnot 3, by decide, ?_⟩
  rintro ⟨u, _, hu⟩
  have h1 := hu 1 ⟨Or.inl (by decide), 3, by decide, Clear.here _⟩
  have h2 := hu 2 ⟨Or.inl (by decide), 3, by decide, Clear.here _⟩
  exact absurd (h1.trans h2.symm) (by decide)

/-- `b ∉ DF⁺(D)` is necessary for `existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry`: at the diamond's join
`3` with `D = {0, 1}`, two definitions reach. -/
theorem existsUnique_needs_not_idf :
    AllReachable diamond ∧ (fun w => w = (0 : Fin 4) ∨ w = 1) diamond.entry ∧
    IDF diamond (fun w => w = 0 ∨ w = 1) 3 ∧ (3 : Fin 4) ≠ diamond.entry ∧
    ¬ ∃ u, ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w)
        u 3 ∧
      ∀ v, ReachesTop diamond (fun w => (w = 0 ∨ w = 1) ∨ IDF diamond (fun w => w = 0 ∨ w = 1) w)
        v 3 → v = u := by
  obtain ⟨_, hidf, h1, h0, _⟩ := reachesTop_at_phi_block_example
  refine ⟨allReachable_diamond, Or.inl rfl, hidf, by decide, ?_⟩
  rintro ⟨u, _, hu⟩
  exact absurd ((hu 1 h1).trans (hu 0 h0).symm) (by decide)

/-- `b ≠ entry` is necessary for `existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry`: nothing reaches the top
of the diamond's entry. -/
theorem existsUnique_needs_ne_entry :
    AllReachable diamond ∧ (fun w => w = (0 : Fin 4)) diamond.entry ∧
    ¬ IDF diamond (fun w => w = 0) 0 ∧ ¬ ((0 : Fin 4) ≠ diamond.entry) ∧
    ¬ ∃ u, ReachesTop diamond (fun w => w = 0 ∨ IDF diamond (fun w => w = 0) w) u 0 ∧
      ∀ v, ReachesTop diamond (fun w => w = 0 ∨ IDF diamond (fun w => w = 0) w) v 0 → v = u := by
  have hnot : ∀ y, ¬ IDF diamond (fun w => w = 0) y := fun y => not_idf_entry entryNoPreds_diamond y
  refine ⟨allReachable_diamond, rfl, hnot 0, fun h => h rfl, ?_⟩
  rintro ⟨u, hu, -⟩
  have hDefs : (fun w : Fin 4 => w = 0 ∨ IDF diamond (fun w => w = 0) w) =
      (fun w => (decide (w = 0) || false) = true) := by
    funext w
    apply propext
    constructor
    · rintro (h | h)
      · simp [h]
      · exact absurd h (hnot w)
    · intro h; left; simpa using h
  rw [hDefs] at hu
  have : ∀ u, notRTCheck diamond (fun w => decide (w = 0) || false) u 0 = true := by decide
  exact not_reachesTop_of_check (this u) hu

/-! ### Non-vacuity witnesses for the existence, uniqueness, and renaming results -/

theorem not_idf_diamond_01_at_1 : ¬ IDF diamond (fun w => w = 0 ∨ w = 1) 1 := by
  intro h
  have h' := IDF.mono (S' := fun w => (decide (w = 0) || decide (w = 1)) = true)
    (fun w hw => by rcases hw with rfl | rfl <;> decide) h
  have := idf_subset_of_check (G := diamond) (S := fun w => decide (w = 0) || decide (w = 1))
    (T := fun w => decide (w = 3)) (by decide) h'
  exact absurd this (by decide)

/-- Non-vacuity of `exists_reachesTop_of_entry_mem`: diamond, `D = {0, 1}`, `b = 3`. -/
theorem exists_reachesTop_hyps_nonvacuous :
    (fun w => w = (0 : Fin 4) ∨ w = 1) diamond.entry ∧ Reachable diamond 3 ∧
    (3 : Fin 4) ≠ diamond.entry :=
  ⟨Or.inl rfl, allReachable_diamond 3, by decide⟩

/-- Non-vacuity of `existsUnique_reachesTop_of_allReachable_of_entry_mem_of_not_idf_of_ne_entry`: diamond, `D = {0, 1}`, `b = 1`. -/
theorem existsUnique_hyps_nonvacuous :
    AllReachable diamond ∧ (fun w => w = (0 : Fin 4) ∨ w = 1) diamond.entry ∧
    ¬ IDF diamond (fun w => w = 0 ∨ w = 1) 1 ∧ (1 : Fin 4) ≠ diamond.entry :=
  ⟨allReachable_diamond, Or.inl rfl, not_idf_diamond_01_at_1, by decide⟩

/-- Non-vacuity of `reachesTop_iff_nearestSDomDef_of_allReachable_of_not_idf`: diamond, `D = {0, 1}`,
`b = 1`. -/
theorem reachesTop_iff_hyps_nonvacuous :
    AllReachable diamond ∧ ¬ IDF diamond (fun w => w = 0 ∨ w = 1) 1 :=
  ⟨allReachable_diamond, not_idf_diamond_01_at_1⟩

/-! ### Tightness of the characterization hypotheses, entry exemption, and non-monotonicity -/

/-- `hclosed` is tight in `singleReachingDef_of_joinClosed`: on the diamond with `D = {0, 1}` and
`P = ∅`, `3 ∈ J(D ∪ P)` carries no φ and two definitions reach `3`. -/
theorem singleReachingDef_needs_joinClosed :
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) := by
  refine ⟨fun h => ?_, not_srd_example⟩
  exact h 3 ⟨0, 1, [0, 2, 3], [1, 3], Or.inl (Or.inl rfl), Or.inl (Or.inr rfl), by decide,
    walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩

/-- `hclosed` is tight in `singleReachingDefAll_of_joinClosed`: on the diamond with `D = {0, 1}`
and no φ, the placement is not join-closed and `SingleReachingDefAll` fails. -/
theorem singleReachingDefAll_needs_joinClosed :
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) ∧
    ¬ SingleReachingDefAll diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) :=
  ⟨singleReachingDef_needs_joinClosed.1, fun h =>
    singleReachingDef_needs_joinClosed.2 fun b hb _ u v hu hv => h b hb u v hu hv⟩

/-- The premise `h : SingleReachingDefAll G D P` is tight in `joinClosed_of_singleReachingDefAll`:
on the diamond with `D = {0, 1}` and no φ, `SingleReachingDefAll` fails and the placement is not
join-closed. -/
theorem joinClosed_needs_singleReachingDefAll :
    ¬ SingleReachingDefAll diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) :=
  ⟨singleReachingDefAll_needs_joinClosed.2, singleReachingDefAll_needs_joinClosed.1⟩

/-- `h : SingleReachingDef G D P` is tight in `joinClosed_of_entryNoPreds_of_singleReachingDef`. -/
theorem joinClosed_needs_singleReachingDef :
    EntryNoPreds diamond ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ (∀ z, InJoin diamond (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 4 → Prop) w) z →
        (fun _ => False : Fin 4 → Prop) z) :=
  ⟨entryNoPreds_diamond, singleReachingDef_needs_joinClosed.2, singleReachingDef_needs_joinClosed.1⟩

/-- `h : SingleReachingDef G D P` is tight in `join_subset_of_entryNoPreds_of_singleReachingDef`. -/
theorem join_subset_needs_singleReachingDef :
    EntryNoPreds diamond ∧
    ¬ SingleReachingDef diamond (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ (∀ z, InJoin diamond (fun w => w = 0 ∨ w = 1) z → (fun _ => False : Fin 4 → Prop) z) :=
  ⟨entryNoPreds_diamond, not_srd_example, fun h => h 3 join_placement_nonempty_example⟩

/-- `SingleReachingDef` exempts the entry: on `entryCycle2` with `D = {0, 1}` and no φ, both `0`
and `1` reach the top of the entry, `SingleReachingDef` holds, and `SingleReachingDefAll` fails. -/
theorem srd_entry_exemption_example :
    ReachesTop entryCycle2 (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 2 → Prop) w) 0 0 ∧
    ReachesTop entryCycle2 (fun w => (w = 0 ∨ w = 1) ∨ (fun _ => False : Fin 2 → Prop) w) 1 0 ∧
    SingleReachingDef entryCycle2 (fun w => w = 0 ∨ w = 1) (fun _ => False) ∧
    ¬ SingleReachingDefAll entryCycle2 (fun w => w = 0 ∨ w = 1) (fun _ => False) := by
  refine ⟨⟨Or.inl (Or.inl rfl), 0, by decide, Clear.here _⟩,
    ⟨Or.inl (Or.inr rfl), 0, by decide, Clear.here _⟩, ?_, ?_⟩
  · have hsrd := srd_of_check (G := entryCycle2)
      (D := fun w => decide (w = 0) || decide (w = 1)) (P := fun _ => false) (by decide)
    have hD : (fun w : Fin 2 => (decide (w = 0) || decide (w = 1)) = true) =
        (fun w => w = 0 ∨ w = 1) := by
      funext w; apply propext; revert w; decide
    have hP : (fun w : Fin 2 => (fun _ => false : Fin 2 → Bool) w = true) = (fun _ => False) := by
      funext w; apply propext; revert w; decide
    rwa [hD, hP] at hsrd
  · intro h
    have heq := h 0 id 0 1
      ⟨Or.inl (Or.inl rfl), 0, by decide, Clear.here _⟩
      ⟨Or.inl (Or.inr rfl), 0, by decide, Clear.here _⟩
    exact absurd heq (by decide)

/-- `SingleReachingDef` means *at most one*: with `D = P = ∅` it holds although no definition
reaches block `1` of the chain. -/
theorem srd_at_most_one_example :
    SingleReachingDef chain3 (fun _ => False) (fun _ => False) ∧
    ¬ ∃ u, ReachesTop chain3 (fun w => (fun _ => False : Fin 3 → Prop) w ∨ False) u 1 := by
  refine ⟨?_, ?_⟩
  · intro b _ _ u _ hu
    rcases hu with ⟨h | h, _⟩ <;> exact h.elim
  · rintro ⟨u, h | h, _⟩ <;> exact h

/-- **`SingleReachingDef` is not monotone in the placement**: on the diamond with `D = {0}`,
`J(D) = ∅ ⊆ {1}`, yet the extra φ at `1` creates a second definition reaching `3` (from `1`, and
from `0` via `2`). -/
theorem srd_not_monotone_diamond :
    (∀ z, InJoin diamond (fun w => w = 0) z → (fun w : Fin 4 => w = 1) z) ∧
    ¬ SingleReachingDef diamond (fun w => w = 0) (fun w => w = 1) := by
  refine ⟨fun z ⟨x, y, _, _, hx, hy, hxy, _⟩ => absurd (hx.trans hy.symm) hxy, fun h => ?_⟩
  have := h 3 (by decide) (by decide) 0 1
    ⟨Or.inl rfl, 2, by decide, Clear.step (by rintro (h | h) <;> exact absurd h (by decide))
      (by decide) (Clear.here _)⟩
    ⟨Or.inr rfl, 3, by decide, Clear.here _⟩
  exact absurd this (by decide)

/-- Non-vacuity of `join_union_join_subset_join` exercising a join node as a start node: in
`ladder5` with `S = {0, 2}`, `3 ∈ J(S) \ S` and `4 ∈ J(S ∪ J(S))` via `[0, 4]` and `[3, 4]`. -/
theorem join_union_join_genuine_nonvacuous :
    InJoin ladder5 (fun x => x = 0 ∨ x = 2) 3 ∧ ¬ (fun x : Fin 5 => x = 0 ∨ x = 2) 3 ∧
    InJoin ladder5 (fun x => (x = 0 ∨ x = 2) ∨ InJoin ladder5 (fun x => x = 0 ∨ x = 2) x) 4 := by
  have h3 : InJoin ladder5 (fun x => x = 0 ∨ x = 2) 3 :=
    ⟨0, 2, [0, 1, 3], [2, 3], Or.inl rfl, Or.inr rfl, by decide,
      walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩
  refine ⟨h3, by decide, 0, 3, [0, 4], [3, 4], Or.inl (Or.inl rfl), Or.inr h3, by decide,
    walk_of_isWalkB (by decide), walk_of_isWalkB (by decide), by decide, by decide, by decide⟩

/-- Full non-vacuity of the join/frontier inclusions: all hypotheses hold and both premises
`InJoin` and `IDF` are met at `3` (diamond, `S = {0, 1}`). -/
theorem join_iteratedDF_full_nonvacuous :
    AllReachable diamond ∧ EntryNoPreds diamond ∧ (fun x : Fin 4 => x = 0 ∨ x = 1) diamond.entry ∧
    InJoin diamond (fun x => x = 0 ∨ x = 1) 3 ∧ IDF diamond (fun x => x = 0 ∨ x = 1) 3 :=
  ⟨allReachable_diamond, entryNoPreds_diamond, Or.inl rfl,
    join_placement_nonempty_example, IDF.base (x := 1) (Or.inr rfl) df_example⟩

end Toy.Ssa
