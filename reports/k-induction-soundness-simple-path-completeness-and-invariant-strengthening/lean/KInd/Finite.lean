import KInd.Basic

/-!
# Finite state spaces: the pigeonhole principle for simple paths

A finite system has state type `Fin n`. A simple path visits pairwise distinct states, so in
`Fin n` it has at most `n` states, i.e. at most `n - 1` transitions.
-/

namespace Toy.KInd

universe u

/-- Pigeonhole: a duplicate-free list of elements of `Fin n` has length at most `n`. -/
theorem nodup_length_le_fin {n : Nat} {l : List (Fin n)} (h : l.Nodup) : l.length ≤ n := by
  have := h.length_le_of_subset (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  simpa [List.length_finRange] using this

/-- The first `j + 1` states of a simple path form a duplicate-free list. -/
theorem IsSimple.nodup_map_range {σ : Type u} {j : Nat} {π : Nat → σ} (h : IsSimple j π) :
    ((List.range (j + 1)).map π).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
  intro a b ha hb hab heq
  rw [List.mem_range] at ha hb
  exact hab (h a b (by omega) (by omega) heq)

/-- A simple path in a system with `n` states has fewer than `n` transitions. -/
theorem IsSimple.lt_card {n j : Nat} {π : Nat → Fin n} (h : IsSimple j π) : j < n := by
  have := nodup_length_le_fin h.nodup_map_range
  simp only [List.length_map, List.length_range] at this
  omega

/-- A simple path with `n - 1` transitions in a system with `n` states visits every state. -/
theorem IsSimple.surj_of_card {m : Nat} {π : Nat → Fin (m + 1)} (h : IsSimple m π)
    (s : Fin (m + 1)) : ∃ i, i ≤ m ∧ π i = s := by
  refine Classical.byContradiction fun hne => ?_
  have hnot : s ∉ (List.range (m + 1)).map π := by
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨i, hi, his⟩ := hm
    rw [List.mem_range] at hi
    exact hne ⟨i, by omega, his⟩
  have hnd : (s :: (List.range (m + 1)).map π).Nodup :=
    List.nodup_cons.mpr ⟨hnot, h.nodup_map_range⟩
  have := nodup_length_le_fin hnd
  simp only [List.length_cons, List.length_map, List.length_range] at this
  omega

/-- In a system with `n` states, `n - 1` bounds the recurrence diameter. -/
theorem reachRecurrenceBound_fin {n : Nat} (I : Fin n → Prop) (T : Fin n → Fin n → Prop) :
    ReachRecurrenceBound I T (n - 1) := by
  intro j π _ _ hs
  have := hs.lt_card
  omega

end Toy.KInd
