import KInd.Soundness
import KInd.Finite

/-!
# Completeness of k-induction on finite systems: simple paths are what is needed

* `simpleStep_of_card_le`: in a system with `n` states the simple-path step holds at every
  depth `k ≥ n`, for every property, because no simple path has `n` transitions.
* `simple_kind_complete_fin`: hence, for an invariant `P` of an `n`-state system,
  `Base n ∧ SimpleStep n` holds: k-induction with the simple-path constraint is complete at
  depth `n`.
* `simple_kind_complete_fin_pred_of_init`: if some initial state exists, depth `n - 1` suffices.
* Optimality of both depths, the necessity of finiteness of the whole state type (finiteness
  of the reachable part does not suffice), and the failure of plain `Step` at every depth are
  shown by concrete counterexamples.
-/

namespace Toy.KInd

universe u

/-- **The simple-path step is vacuous at depth `≥ n`.** In a system with `n` states, for every
transition relation `T`, every property `P` and every `k ≥ n`, the simple-path step at depth
`k` holds (no simple path has `k ≥ n` transitions). -/
theorem simpleStep_of_card_le {n k : Nat} (T : Fin n → Fin n → Prop) (P : Fin n → Prop)
    (hk : n ≤ k) : SimpleStep T P k :=
  fun _ _ hs _ => absurd hs.lt_card (by omega)

/-- **k-induction with the simple-path constraint is complete for finite systems at depth
`n`.** For every system with state space `Fin n` and every invariant `P` of it,
`Base I T P n` and `SimpleStep T P n` both hold. -/
theorem simple_kind_complete_fin {n : Nat} {I : Fin n → Prop} {T : Fin n → Fin n → Prop}
    {P : Fin n → Prop} (h : Invariant I T P) : Base I T P n ∧ SimpleStep T P n :=
  ⟨base_of_invariant h n, simpleStep_of_card_le T P (Nat.le_refl n)⟩

/-- **Depth `n - 1` suffices when there is an initial state.** For every system with state
space `Fin (m + 1)` that has at least one initial state, and every invariant `P` of it,
`Base I T P m` and `SimpleStep T P m` both hold. (A simple path with `m` transitions visits
all `m + 1` states, in particular an initial one, so its last state is reachable.) -/
theorem simple_kind_complete_fin_pred_of_init {m : Nat} {I : Fin (m + 1) → Prop}
    {T : Fin (m + 1) → Fin (m + 1) → Prop} {P : Fin (m + 1) → Prop} (hI : ∃ s, I s)
    (h : Invariant I T P) : Base I T P m ∧ SimpleStep T P m := by
  refine ⟨base_of_invariant h m, ?_⟩
  intro π hp hs _
  obtain ⟨s0, hs0⟩ := hI
  obtain ⟨i, hi, hπi⟩ := hs.surj_of_card s0
  apply h
  have hsplit : m = i + (m - i) := by omega
  have hp' : IsPath T (i + (m - i)) π := hsplit ▸ hp
  refine ⟨m - i, ⟨fun t => π (i + t), ?_, hp'.shift, ?_⟩⟩
  · simpa [hπi] using hs0
  · show π (i + (m - i)) = π m
    exact congrArg π hsplit.symm

/-! ## Optimality and necessity counterexamples -/

/-- The path `0, 1, …, m` in `Fin n` (constant `m` afterwards), for `m < n`. -/
def countUpTo (m n : Nat) (h : m < n) : Nat → Fin n := fun t => ⟨min t m, by omega⟩

theorem countUpTo_val {m n : Nat} (h : m < n) (t : Nat) : (countUpTo m n h t).val = min t m :=
  rfl

theorem countUpTo_simple {m n : Nat} (h : m < n) : IsSimple m (countUpTo m n h) := by
  intro i j hi hj hij
  have := congrArg Fin.val hij
  simp only [countUpTo_val] at this
  omega

/- A chain `0 → 1 → ⋯ → m` on `Fin (m + 1)` with no initial states; `P` excludes `m`. -/
namespace NoInitChain
abbrev I (m : Nat) : Fin (m + 1) → Prop := fun _ => False
abbrev T (m : Nat) : Fin (m + 1) → Fin (m + 1) → Prop := fun s t => t.val = s.val + 1
abbrev P (m : Nat) : Fin (m + 1) → Prop := fun s => s.val ≠ m
end NoInitChain

/-- **Depth `n` is optimal in `simple_kind_complete_fin`.** For every `m`, the chain on
`Fin (m + 1)` without initial states has `P` invariant (vacuously) while the simple-path step
fails at depth `m = n - 1`. -/
theorem simple_kind_depth_card_optimal_without_init (m : Nat) :
    Invariant (NoInitChain.I m) (NoInitChain.T m) (NoInitChain.P m) ∧
      ¬ SimpleStep (NoInitChain.T m) (NoInitChain.P m) m := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨k, π, h0, -, -⟩
    exact h0.elim
  · intro h
    have := h (countUpTo m (m + 1) (Nat.lt_succ_self m))
      (by intro i hi; simp only [NoInitChain.T, countUpTo_val]; omega)
      (countUpTo_simple _)
      (by intro i hi; simp only [NoInitChain.P, countUpTo_val]; omega)
    simp [countUpTo_val] at this

/- A chain `0 → 1 → ⋯ → m` on `Fin (m + 2)` plus an isolated initial state `m + 1`; `P`
excludes `m`. -/
namespace IsolatedInitChain
abbrev I (m : Nat) : Fin (m + 2) → Prop := fun s => s.val = m + 1
abbrev T (m : Nat) : Fin (m + 2) → Fin (m + 2) → Prop :=
  fun s t => s.val < m ∧ t.val = s.val + 1
abbrev P (m : Nat) : Fin (m + 2) → Prop := fun s => s.val ≠ m
end IsolatedInitChain

/-- **Depth `n - 1` is optimal in `simple_kind_complete_fin_pred_of_init`.** For every `m`, the
system on `Fin (m + 2)` (so `n = m + 2`) has an initial state and `P` invariant, while the
simple-path step fails at depth `m = n - 2`. -/
theorem simple_kind_depth_pred_optimal_with_init (m : Nat) :
    (∃ s, IsolatedInitChain.I m s) ∧
      Invariant (IsolatedInitChain.I m) (IsolatedInitChain.T m) (IsolatedInitChain.P m) ∧
      ¬ SimpleStep (IsolatedInitChain.T m) (IsolatedInitChain.P m) m := by
  refine ⟨⟨⟨m + 1, by omega⟩, rfl⟩, ?_, ?_⟩
  · refine invariant_of_inductive (Q := fun s => s.val = m + 1) (fun s hs => hs) ?_ ?_
    · intro s t hs hst
      simp only [IsolatedInitChain.T] at hst
      omega
    · intro s hs
      simp only [IsolatedInitChain.P]
      omega
  · intro h
    have := h (countUpTo m (m + 2) (by omega))
      (by intro i hi; simp only [IsolatedInitChain.T, countUpTo_val]; omega)
      (countUpTo_simple _)
      (by intro i hi; simp only [IsolatedInitChain.P, countUpTo_val]; omega)
    simp [countUpTo_val] at this

/- An infinite system on `Nat`: initial state `0` with a self-loop, and an unreachable
descending chain `⋯ → 3 → 2 → 1`; `P` excludes `1`. -/
namespace NatDescent
abbrev I : Nat → Prop := fun s => s = 0
abbrev T : Nat → Nat → Prop := fun s t => (s = 0 ∧ t = 0) ∨ (2 ≤ s ∧ t + 1 = s)
abbrev P : Nat → Prop := fun s => s ≠ 1
end NatDescent

theorem natDescent_reachable_iff (s : Nat) : Reachable NatDescent.I NatDescent.T s ↔ s = 0 := by
  constructor
  · refine invariant_of_inductive (Q := fun s => s = 0) (fun s hs => hs) ?_ (fun _ h => h) s
    intro a b ha hab
    simp only [NatDescent.T] at hab
    omega
  · intro h
    exact reachable_of_init h

/-- **Finiteness of the state type is necessary for simple-path completeness; finiteness of the
reachable part is not enough.** The infinite system `NatDescent` has an initial state, exactly
one reachable state (`0`), reachability diameter bound `0` and reachability recurrence bound
`0`; `P` is invariant and every base check passes, yet the simple-path step fails at every
depth `k` (on the unreachable simple path `k + 1 → k → ⋯ → 1`), so k-induction with simple
paths never succeeds on it. -/
theorem simple_kind_incomplete_every_depth_infinite :
    (∃ s, NatDescent.I s) ∧
      (∀ s, Reachable NatDescent.I NatDescent.T s ↔ s = 0) ∧
      ReachDiameterBound NatDescent.I NatDescent.T 0 ∧
      ReachRecurrenceBound NatDescent.I NatDescent.T 0 ∧
      Invariant NatDescent.I NatDescent.T NatDescent.P ∧
      ∀ k, Base NatDescent.I NatDescent.T NatDescent.P k ∧
        ¬ SimpleStep NatDescent.T NatDescent.P k := by
  have hinv : Invariant NatDescent.I NatDescent.T NatDescent.P := by
    intro s hs
    have := (natDescent_reachable_iff s).mp hs
    simp only [NatDescent.P]
    omega
  have hd : ReachDiameterBound NatDescent.I NatDescent.T 0 := by
    intro s hs
    have h0 := (natDescent_reachable_iff s).mp hs
    exact ⟨0, Nat.le_refl 0, reachIn_zero_iff.mpr h0⟩
  have hr : ReachRecurrenceBound NatDescent.I NatDescent.T 0 := by
    intro j π h0 hp hs
    refine Classical.byContradiction fun hj => ?_
    have h01 : NatDescent.T (π 0) (π 1) := hp 0 (by omega)
    simp only [NatDescent.I] at h0
    simp only [NatDescent.T] at h01
    have := hs 0 1 (by omega) (by omega) (by omega)
    omega
  refine ⟨⟨0, rfl⟩, natDescent_reachable_iff, hd, hr, hinv,
    fun k => ⟨base_of_invariant hinv k, ?_⟩⟩
  intro h
  have := h (fun t => k + 1 - t)
    (by intro i hi; simp only [NatDescent.T]; omega)
    (by intro i j hi hj hij; simp only at hij; omega)
    (by intro i hi; simp only [NatDescent.P]; omega)
  simp only [NatDescent.P] at this
  omega

/- A finite system on `Fin 3`: initial state `0` with a self-loop, an unreachable state `1`
with a self-loop, and a transition `1 → 2` into the bad state `2`. -/
namespace SelfLoop
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t =>
  (s.val = 0 ∧ t.val = 0) ∨ (s.val = 1 ∧ t.val = 1) ∨ (s.val = 1 ∧ t.val = 2)
abbrev P : Fin 3 → Prop := fun s => s.val ≠ 2
end SelfLoop

theorem selfLoop_invariant : Invariant SelfLoop.I SelfLoop.T SelfLoop.P :=
  invariant_of_inductive (Q := fun s => s.val = 0) (fun s hs => hs)
    (by unfold Consecution; decide) (by decide)

/-- **Plain k-induction is incomplete at every depth, even for a finite system.** In
`SelfLoop`, `P` is invariant but `Step T P k` fails for every `k` (the unreachable path
`1, 1, …, 1, 2`). -/
theorem plain_kind_incomplete_every_depth :
    Invariant SelfLoop.I SelfLoop.T SelfLoop.P ∧ ∀ k, ¬ Step SelfLoop.T SelfLoop.P k := by
  refine ⟨selfLoop_invariant, fun k h => ?_⟩
  have := h (fun t => if t < k then (1 : Fin 3) else 2)
    (by
      intro i hi
      by_cases h1 : i + 1 < k
      · simp only [hi, h1, ite_true]; decide
      · simp only [hi, h1, ite_true, ite_false]; decide)
    (by intro i hi; simp only [hi, ite_true]; decide)
  simp at this

/-- Positive control for `plain_kind_incomplete_every_depth`: on the same system, k-induction
with the simple-path constraint succeeds at depth `2`. -/
theorem selfLoop_simple_kind_succeeds_at_two :
    Base SelfLoop.I SelfLoop.T SelfLoop.P 2 ∧ SimpleStep SelfLoop.T SelfLoop.P 2 :=
  ⟨base_of_invariant selfLoop_invariant 2, simpleStep_two_iff.mpr (by decide)⟩

/-- Escape hatch for `plain_kind_incomplete_every_depth` (unreachable states are essential): if
every state is reachable, every invariant passes the plain step already at depth `0` (hence, by
`Step.mono`, at every depth). -/
theorem step_zero_of_invariant_of_all_reachable {σ : Type u} {I : σ → Prop} {T : σ → σ → Prop}
    {P : σ → Prop} (hall : ∀ s, Reachable I T s) (h : Invariant I T P) : Step T P 0 :=
  step_zero_iff.mpr fun s => h s (hall s)

/-- Escape hatch for `plain_kind_incomplete_every_depth` (cycles are essential): if the
transition relation of an `n`-state system has no cycle (no path with at least one transition
returns to its start), then every path is simple, no path has `n` transitions, and the plain
step holds at depth `n` for every property. -/
theorem step_card_of_acyclic {n : Nat} (T : Fin n → Fin n → Prop) (P : Fin n → Prop)
    (hT : ∀ m (π : Nat → Fin n), IsPath T (m + 1) π → π 0 ≠ π (m + 1)) : Step T P n := by
  intro π hp _
  have hcyc : ∀ i j, i < j → j ≤ n → π i ≠ π j := by
    intro i j hij hj
    have e : i + ((j - i - 1) + 1) = j := by omega
    have hpj : IsPath T (i + ((j - i - 1) + 1)) π := by rw [e]; exact hp.mono hj
    have := hT (j - i - 1) (fun t => π (i + t)) hpj.shift
    simp only [Nat.add_zero] at this
    rw [e] at this
    exact this
  have hsimple : IsSimple n π := by
    intro i j hi hj hij
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hij (hcyc i j hlt hj)
    · exact heq
    · exact absurd hij.symm (hcyc j i hgt hi)
  exact absurd hsimple.lt_card (Nat.lt_irrefl n)

end Toy.KInd
