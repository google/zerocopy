import KInd.BMC
import KInd.Soundness

/-!
# Supplementary remarks backing non-claims

These theorems are not results of their own; they back specific non-claims in the report.

* `allInitChain_reachDiameter_zero_reachRecurrenceDiameter_pred`: when several states are
  initial, the gap between the reachability diameter and the reachability recurrence diameter
  of an `n`-state system can be `n - 1` (not only `n - 2`): on the chain `0 → 1 → ⋯ → m` with
  every state initial, `rd = 0` and `rrd = m`.
* `endpoint_only_exact_base_unsound_even_when_total`: an exact-length base check must assert
  `P` at every position of the path; checking only the last state is unsound even when every
  state has a successor.
* `base_one_iff_exactBase_zero`: at depth `1` the prefix-length base check and the
  exact-length check (of length `0`) agree without any totality assumption.
-/

namespace Toy.KInd

universe u

/-! The chain `0 → 1 → ⋯ → m` on `Fin (m + 1)` in which every state is initial. -/
namespace AllInitChain
abbrev I (m : Nat) : Fin (m + 1) → Prop := fun _ => True
abbrev T (m : Nat) : Fin (m + 1) → Fin (m + 1) → Prop := fun s t => t.val = s.val + 1
end AllInitChain

/-- With every state initial, the chain `0 → ⋯ → m` (`n = m + 1` states) has reachability
diameter `0` and reachability recurrence diameter `m = n - 1`. -/
theorem allInitChain_reachDiameter_zero_reachRecurrenceDiameter_pred (m : Nat) :
    IsReachDiameter (AllInitChain.I m) (AllInitChain.T m) 0 ∧
      IsReachRecurrenceDiameter (AllInitChain.I m) (AllInitChain.T m) m := by
  refine ⟨⟨fun _ _ => ⟨0, Nat.le_refl 0, reachIn_zero_iff.mpr trivial⟩,
           fun _ _ => Nat.zero_le _⟩,
          ⟨reachRecurrenceBound_fin _ _, fun r' hr' => ?_⟩⟩
  exact hr' m (countUpTo m (m + 1) (Nat.lt_succ_self m))
    trivial
    (by intro i hi; simp only [AllInitChain.T, countUpTo_val]; omega)
    (countUpTo_simple _)

/-! The two-state cycle `0 ↔ 1` with initial state `0` and property `P = {0}`. -/
namespace TwoCycle
abbrev I : Fin 2 → Prop := fun s => s.val = 0
abbrev T : Fin 2 → Fin 2 → Prop := fun s t => (s.val = 0 ∧ t.val = 1) ∨ (s.val = 1 ∧ t.val = 0)
abbrev P : Fin 2 → Prop := fun s => s.val = 0
end TwoCycle

/-- **Endpoint-only exact-length base checks are unsound even under totality.** On `TwoCycle`,
every state has a successor, every path from an initial state with exactly `2` transitions ends
in a `P`-state, and `Step 3` holds, yet `P` is not invariant (state `1` is reachable). -/
theorem endpoint_only_exact_base_unsound_even_when_total :
    (∀ s : Fin 2, ∃ t : Fin 2, TwoCycle.T s t) ∧
      (∀ π : Nat → Fin 2, TwoCycle.I (π 0) → IsPath TwoCycle.T 2 π → TwoCycle.P (π 2)) ∧
      Step TwoCycle.T TwoCycle.P 3 ∧
      ¬ Invariant TwoCycle.I TwoCycle.T TwoCycle.P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : s.val = 0
    · exact ⟨⟨1, by decide⟩, Or.inl ⟨hs, rfl⟩⟩
    · have hs1 : s.val = 1 := by omega
      exact ⟨⟨0, by decide⟩, Or.inr ⟨hs1, rfl⟩⟩
  · intro π h0 hp
    have h01 : TwoCycle.T (π 0) (π 1) := hp 0 (by decide)
    have h12 : TwoCycle.T (π 1) (π 2) := hp 1 (by decide)
    simp only [TwoCycle.I] at h0
    simp only [TwoCycle.T, TwoCycle.P] at h01 h12 ⊢
    omega
  · intro π hp hP
    have h01 : TwoCycle.T (π 0) (π 1) := hp 0 (by decide)
    have hp0 : TwoCycle.P (π 0) := hP 0 (by decide)
    have hp1 : TwoCycle.P (π 1) := hP 1 (by decide)
    simp only [TwoCycle.T, TwoCycle.P] at h01 hp0 hp1
    omega
  · intro hinv
    have hr1 : ReachIn TwoCycle.I TwoCycle.T 1 ⟨1, by decide⟩ := by
      simp only [reachIn_succ_iff, reachIn_zero_iff]
      decide
    exact absurd (hinv ⟨1, by decide⟩ ⟨1, hr1⟩) (by decide)

/-- **At depth `1` the prefix-length and exact-length base checks agree unconditionally.**
`Base I T P 1` is equivalent to checking `P` on every path from an initial state with exactly
`0` transitions, for every transition relation (total or not). -/
theorem base_one_iff_exactBase_zero {σ : Type u} {I : σ → Prop} {T : σ → σ → Prop}
    {P : σ → Prop} :
    Base I T P 1 ↔ ∀ π : Nat → σ, I (π 0) → IsPath T 0 π → ∀ i, i ≤ 0 → P (π i) := by
  constructor
  · intro h π h0 hp i hi
    exact h 0 (Nat.zero_lt_succ 0) π h0 hp i hi
  · intro h j hj π h0 hp i hi
    have hj0 : j = 0 := by omega
    subst hj0
    exact h π h0 hp i hi

end Toy.KInd
