import KInd.Soundness

/-!
# k-induction versus 1-induction: monotonicity in the depth and strict separation

* `Step.mono`, `SimpleStep.mono`, `kind_success_mono`: the step checks (plain and simple-path)
  are monotone in the depth, and once plain k-induction succeeds at depth `k` it succeeds at
  every larger depth.
* `one_induction_fails_two_induction_succeeds`: a three-state system whose invariant is not
  1-inductive but is 2-inductive.
* `ladder_needs_depth_succ`: for every `k`, a finite system whose invariant is
  `(k+1)`-inductive but fails the step at every depth `j ≤ k`, even with the simple-path
  constraint; so k-induction (plain or simple-path) at any fixed depth is incomplete.
-/

namespace Toy.KInd

universe u

section Mono

variable {σ : Type u} {I : σ → Prop} {T : σ → σ → Prop} {P : σ → Prop}

/-- The step check is monotone in the depth. -/
theorem Step.succ {k : Nat} (h : Step T P k) : Step T P (k + 1) := by
  intro π hp hP
  have hp' : IsPath T (1 + k) π := by rw [Nat.add_comm]; exact hp
  have := h (fun t => π (1 + t)) hp'.shift (fun i hi => hP (1 + i) (by omega))
  simpa [Nat.add_comm] using this

/-- **The plain step check is monotone in the depth.** If `Step T P k` holds and `k ≤ k'`,
then `Step T P k'` holds. -/
theorem Step.mono {k k' : Nat} (h : Step T P k) (hk : k ≤ k') : Step T P k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- The simple-path step check is monotone in the depth (one step). -/
theorem SimpleStep.succ {k : Nat} (h : SimpleStep T P k) : SimpleStep T P (k + 1) := by
  intro π hp hs hP
  have hp' : IsPath T (1 + k) π := by rw [Nat.add_comm]; exact hp
  have hs' : IsSimple (1 + k) π := by rw [Nat.add_comm]; exact hs
  have := h (fun t => π (1 + t)) hp'.shift hs'.shift (fun i hi => hP (1 + i) (by omega))
  simpa [Nat.add_comm] using this

/-- **The simple-path step check is monotone in the depth.** If `SimpleStep T P k` holds and
`k ≤ k'`, then `SimpleStep T P k'` holds (a suffix of a simple path is simple). -/
theorem SimpleStep.mono {k k' : Nat} (h : SimpleStep T P k) (hk : k ≤ k') :
    SimpleStep T P k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- **Success of plain k-induction is monotone in the depth.** If `Base k ∧ Step k` holds and
`k ≤ k'`, then `Base k' ∧ Step k'` holds. -/
theorem kind_success_mono {k k' : Nat} (hb : Base I T P k) (hs : Step T P k) (hk : k ≤ k') :
    Base I T P k' ∧ Step T P k' :=
  ⟨base_of_invariant (kind_sound hb hs) k', hs.mono hk⟩

end Mono

/- `TwoInd`: states `Fin 3`; initial state `0` with a self-loop; an unreachable transition
`1 → 2`; `P` excludes `2`. -/
namespace TwoInd
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t => (s.val = 0 ∧ t.val = 0) ∨ (s.val = 1 ∧ t.val = 2)
abbrev P : Fin 3 → Prop := fun s => s.val ≠ 2
end TwoInd

/-- **k-induction succeeds where 1-induction fails.** In `TwoInd`, `P` is not preserved by
one transition (`1 → 2`), but `Base 2` and `Step 2` hold (state `1` has no predecessor), and
`P` is invariant. -/
theorem one_induction_fails_two_induction_succeeds :
    ¬ Step TwoInd.T TwoInd.P 1 ∧ Base TwoInd.I TwoInd.T TwoInd.P 2 ∧
      Step TwoInd.T TwoInd.P 2 ∧ Invariant TwoInd.I TwoInd.T TwoInd.P := by
  have hs2 : Step TwoInd.T TwoInd.P 2 := step_two_iff.mpr (by decide)
  have hb2 : Base TwoInd.I TwoInd.T TwoInd.P 2 := by
    rw [base_iff_reachIn]
    intro j hj s hs
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [reachIn_zero_iff] at hs
      simp only [TwoInd.P]
      omega
    · rw [reachIn_succ_iff] at hs
      obtain ⟨s', hs', hst⟩ := hs
      rw [reachIn_zero_iff] at hs'
      simp only [TwoInd.T] at hst
      simp only [TwoInd.P]
      omega
  refine ⟨?_, hb2, hs2, kind_sound hb2 hs2⟩
  rw [step_one_iff]
  unfold Consecution
  decide

/- `Ladder k`: states `Fin (k + 2)`; initial state `0` with a self-loop; an unreachable chain
`1 → 2 → ⋯ → k + 1`; `P` excludes `k + 1`. For `k = 1` this is `TwoInd`. -/
namespace Ladder
abbrev I (k : Nat) : Fin (k + 2) → Prop := fun s => s.val = 0
abbrev T (k : Nat) : Fin (k + 2) → Fin (k + 2) → Prop := fun s t =>
  (s.val = 0 ∧ t.val = 0) ∨ (1 ≤ s.val ∧ s.val ≤ k ∧ t.val = s.val + 1)
abbrev P (k : Nat) : Fin (k + 2) → Prop := fun s => s.val ≠ k + 1
end Ladder

/-- Along a `Ladder` path, state `0` stays at `0` and a nonzero state advances by one. -/
theorem ladder_path_val {k m : Nat} {π : Nat → Fin (k + 2)} (hp : IsPath (Ladder.T k) m π) :
    ∀ i, i ≤ m → ((π 0).val = 0 → (π i).val = 0) ∧ ((π 0).val ≠ 0 → (π i).val = (π 0).val + i) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨id, fun _ => rfl⟩
  | succ i ih =>
    intro hi
    have ⟨ih0, ih1⟩ := ih (by omega)
    have hstep := hp i (by omega)
    simp only [Ladder.T] at hstep
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have := ih0 h0; omega
    · have := ih1 h0; omega

/-- **For every depth `k` there is a finite system that needs depth `k + 1`.** In `Ladder k`
(`k + 2` states), `P` is invariant and `Base (k+1) ∧ Step (k+1)` holds, but the step fails at
every depth `j ≤ k`, even restricted to simple paths (the witness path `1 → 2 → ⋯ → k + 1` is
simple). So neither plain nor simple-path k-induction at any depth `j ≤ k` proves this
invariant. -/
theorem ladder_needs_depth_succ (k : Nat) :
    Invariant (Ladder.I k) (Ladder.T k) (Ladder.P k) ∧
      Base (Ladder.I k) (Ladder.T k) (Ladder.P k) (k + 1) ∧
      Step (Ladder.T k) (Ladder.P k) (k + 1) ∧
      ∀ j, j ≤ k → ¬ SimpleStep (Ladder.T k) (Ladder.P k) j := by
  have hinv : Invariant (Ladder.I k) (Ladder.T k) (Ladder.P k) := by
    refine invariant_of_inductive (Q := fun s => s.val = 0) (fun s hs => hs) ?_ ?_
    · intro s t hs hst
      simp only [Ladder.T] at hst
      omega
    · intro s hs
      simp only [Ladder.P]
      omega
  have hstep : Step (Ladder.T k) (Ladder.P k) (k + 1) := by
    intro π hp _
    have ⟨h0, h1⟩ := ladder_path_val hp (k + 1) (Nat.le_refl _)
    have hlt := (π (k + 1)).isLt
    simp only [Ladder.P]
    by_cases hz : (π 0).val = 0
    · have := h0 hz; omega
    · have := h1 hz; omega
  refine ⟨hinv, base_of_invariant hinv (k + 1), hstep, fun j hj hj' => ?_⟩
  have hk : SimpleStep (Ladder.T k) (Ladder.P k) k := hj'.mono hj
  have := hk (fun t => ⟨min (t + 1) (k + 1), by omega⟩)
    (by intro i hi; simp only [Ladder.T]; omega)
    (by intro a b ha hb hab
        have := congrArg Fin.val hab
        simp only at this
        omega)
    (by intro i hi; simp only [Ladder.P]; omega)
  simp only [Ladder.P] at this
  omega

/-- Positive control for `ladder_needs_depth_succ`: in `Ladder k`, k-induction succeeds at
depth `k + 1`. -/
theorem ladder_kind_succeeds_at_depth_succ (k : Nat) :
    Base (Ladder.I k) (Ladder.T k) (Ladder.P k) (k + 1) ∧
      Step (Ladder.T k) (Ladder.P k) (k + 1) :=
  ⟨(ladder_needs_depth_succ k).2.1, (ladder_needs_depth_succ k).2.2.1⟩

end Toy.KInd
