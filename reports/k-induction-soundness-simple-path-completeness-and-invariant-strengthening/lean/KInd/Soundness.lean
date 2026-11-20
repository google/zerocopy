import KInd.Basic

/-!
# Soundness of k-induction (plain and simple-path) and loop removal

* `kind_sound`: `Base k ∧ Step k ⇒ □ P`, for every transition system (finite or not).
* `exists_simple_reachIn`: every state reachable in `m` transitions is reachable along a
  simple path with at most `m` transitions (loop removal).
* `kind_simple_sound`: `Base k ∧ SimpleStep k ⇒ □ P`, again for every transition system.
  Because `SimpleStep` is weaker than `Step`, this implies `kind_sound`; its proof needs loop
  removal.
-/

namespace Toy.KInd

universe u

variable {σ : Type u} {I : σ → Prop} {T : σ → σ → Prop} {P : σ → Prop}

/-- **k-induction is sound.** For every transition system and every depth `k`, if every path
from an initial state with at most `k` states stays in `P` (`Base`) and every path of `k + 1`
states whose first `k` states satisfy `P` ends in `P` (`Step`), then every reachable state
satisfies `P`. -/
theorem kind_sound {k : Nat} (hbase : Base I T P k) (hstep : Step T P k) :
    Invariant I T P := by
  rw [base_iff_reachIn] at hbase
  -- every state reachable in exactly `m` transitions satisfies `P`, by strong induction
  have key : ∀ m s, ReachIn I T m s → P s := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro s hs
      by_cases hmk : m < k
      · exact hbase m hmk s hs
      · obtain ⟨π, h0, hp, rfl⟩ := hs
        have hsplit : m = (m - k) + k := by omega
        have hp' : IsPath T ((m - k) + k) π := hsplit ▸ hp
        have h := hstep (fun t => π ((m - k) + t)) hp'.shift (by
          intro i hi
          exact ih ((m - k) + i) (by omega) _ (reachIn_of_path h0 hp (by omega)))
        simpa [← hsplit] using h
  intro s ⟨m, hm⟩
  exact key m s hm

/-- **Loop removal.** If `s` is reachable in `m` transitions, then `s` is reachable along a
simple path (pairwise distinct states) with at most `m` transitions. -/
theorem exists_simple_reachIn {m : Nat} {s : σ} (h : ReachIn I T m s) :
    ∃ m', m' ≤ m ∧ ∃ π : Nat → σ, I (π 0) ∧ IsPath T m' π ∧ IsSimple m' π ∧ π m' = s := by
  induction m using Nat.strongRecOn generalizing s with
  | _ m ih =>
    obtain ⟨π, h0, hp, hs⟩ := h
    by_cases hrep : ∃ i j, i < j ∧ j ≤ m ∧ π i = π j
    · obtain ⟨i, j, hij, hjm, heq⟩ := hrep
      -- cut out the loop `π i, …, π j`
      let π' : Nat → σ := fun t => if t ≤ i then π t else π (t + (j - i))
      have hπ'0 : π' 0 = π 0 := by simp [π']
      have hpath : IsPath T (m - (j - i)) π' := by
        intro t ht
        by_cases hti : t < i
        · have h1 : t ≤ i := Nat.le_of_lt hti
          have h2 : t + 1 ≤ i := hti
          simp only [π', h1, h2, ite_true]
          exact hp t (by omega)
        · by_cases hte : t = i
          · subst hte
            have h2 : ¬ (t + 1 ≤ t) := Nat.not_succ_le_self t
            simp only [π', Nat.le_refl, ite_true, h2, ite_false]
            have e : t + 1 + (j - t) = j + 1 := by omega
            rw [e, heq]
            exact hp j (by omega)
          · have h1 : ¬ (t ≤ i) := by omega
            have h2 : ¬ (t + 1 ≤ i) := by omega
            simp only [π', h1, h2, ite_false]
            have e : t + 1 + (j - i) = t + (j - i) + 1 := by omega
            rw [e]
            exact hp (t + (j - i)) (by omega)
      have hend : π' (m - (j - i)) = s := by
        by_cases hle : m - (j - i) ≤ i
        · have hji : j = m := by omega
          have e : m - (j - i) = i := by omega
          simp only [π', hle, ite_true]
          rw [e, heq, hji, hs]
        · simp only [π', hle, ite_false]
          have e : m - (j - i) + (j - i) = m := by omega
          rw [e, hs]
      obtain ⟨m', hm', ρ, hρ⟩ :=
        ih (m - (j - i)) (by omega) ⟨π', hπ'0 ▸ h0, hpath, hend⟩
      exact ⟨m', by omega, ρ, hρ⟩
    · refine ⟨m, Nat.le_refl m, π, h0, hp, ?_, hs⟩
      intro i j hi hj hij
      rcases Nat.lt_trichotomy i j with hlt | heq | hgt
      · exact absurd ⟨i, j, hlt, hj, hij⟩ hrep
      · exact heq
      · exact absurd ⟨j, i, hgt, hi, hij.symm⟩ hrep

/-- **k-induction with the simple-path constraint is sound.** For every transition system and
every depth `k`, `Base I T P k` together with the step restricted to simple paths implies that
every reachable state satisfies `P`. -/
theorem kind_simple_sound {k : Nat} (hbase : Base I T P k) (hstep : SimpleStep T P k) :
    Invariant I T P := by
  rw [base_iff_reachIn] at hbase
  have key : ∀ m s, ReachIn I T m s → P s := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro s hs
      obtain ⟨m', hm', π, h0, hp, hsimp, rfl⟩ := exists_simple_reachIn hs
      by_cases hmk : m' < k
      · exact hbase m' hmk _ (reachIn_of_path h0 hp (Nat.le_refl _))
      · have hsplit : m' = (m' - k) + k := by omega
        have hp' : IsPath T ((m' - k) + k) π := hsplit ▸ hp
        have hs' : IsSimple ((m' - k) + k) π := hsplit ▸ hsimp
        have h := hstep (fun t => π ((m' - k) + t)) hp'.shift hs'.shift (by
          intro i hi
          exact ih ((m' - k) + i) (by omega) _ (reachIn_of_path h0 hp (by omega)))
        simpa [← hsplit] using h
  intro s ⟨m, hm⟩
  exact key m s hm

/-- **Exact-length base checks agree with `Base` when every state has a successor.** If the
transition relation is total, then checking every path from an initial state with exactly `k`
transitions is equivalent to `Base I T P (k + 1)` (every path with at most `k` transitions):
shorter paths extend to length `k`. Without totality the exact-length check can be weaker and
k-induction built on it unsound, as shown at `k = 2` (`exact_length_base_unsound_without_totality`). -/
theorem base_iff_exactBase_of_total {k : Nat} (htot : ∀ s, ∃ t, T s t) :
    Base I T P (k + 1) ↔
      ∀ π : Nat → σ, I (π 0) → IsPath T k π → ∀ i, i ≤ k → P (π i) := by
  constructor
  · intro h π h0 hp i hi
    exact h k (Nat.lt_succ_self k) π h0 hp i hi
  · intro h j hj π h0 hp i hi
    let f : σ → σ := fun s => Classical.choose (htot s)
    have hf : ∀ s, T s (f s) := fun s => Classical.choose_spec (htot s)
    -- `g n` is the end of an `n`-step `f`-extension of `π j`
    let g : Nat → σ := fun n => Nat.rec (π j) (fun _ x => f x) n
    have hg0 : g 0 = π j := rfl
    have hgs : ∀ n, g (n + 1) = f (g n) := fun _ => rfl
    let ρ : Nat → σ := fun t => if t ≤ j then π t else g (t - j)
    have hρ : ∀ t, j ≤ t → ρ t = g (t - j) := by
      intro t ht
      by_cases htj : t ≤ j
      · have e : t = j := by omega
        subst e
        simp only [ρ, htj, ite_true, Nat.sub_self, hg0]
      · simp only [ρ, htj, ite_false]
    have hpath : IsPath T k ρ := by
      intro t ht
      by_cases htj : t < j
      · have h1 : t ≤ j := Nat.le_of_lt htj
        have h2 : t + 1 ≤ j := htj
        simp only [ρ, h1, h2, ite_true]
        exact hp t htj
      · rw [hρ t (by omega), hρ (t + 1) (by omega)]
        have e : t + 1 - j = (t - j) + 1 := by omega
        rw [e, hgs]
        exact hf _
    have := h ρ (by simpa [ρ] using h0) hpath i (by omega)
    have hi' : i ≤ j := hi
    simpa [ρ, hi'] using this

/-- Plain k-induction soundness is also a corollary of the simple-path version. -/
theorem kind_sound_of_simple {k : Nat} (hbase : Base I T P k) (hstep : Step T P k) :
    Invariant I T P :=
  kind_simple_sound hbase hstep.simpleStep

/-- Ordinary induction (initiation plus consecution of a strengthening `Q ⇒ P`) is sound. -/
theorem invariant_of_inductive {Q : σ → Prop} (hinit : Initiation I Q)
    (hcons : Consecution T Q) (hQP : ∀ s, Q s → P s) : Invariant I T P := by
  have hQ : Invariant I T Q := by
    refine kind_sound (k := 1) ?_ (step_one_iff.mpr hcons)
    rw [base_iff_reachIn]
    intro j hj s hs
    have : j = 0 := by omega
    subst this
    exact hinit s (reachIn_zero_iff.mp hs)
  exact fun s hs => hQP s (hQ s hs)

end Toy.KInd
