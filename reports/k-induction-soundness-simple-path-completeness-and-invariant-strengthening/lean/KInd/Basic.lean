/-!
# Transition systems, paths, and the checks of induction-based safety verification

A transition system is given by a state type `σ`, an initial-state predicate `I : σ → Prop`
and a transition relation `T : σ → σ → Prop`. A safety property is a state predicate
`P : σ → Prop`; the system is safe (`□ P`) when every reachable state satisfies `P`.

Paths are represented as functions `π : Nat → σ` together with an explicit number of
transitions `k`: the path visits `π 0, π 1, …, π k`, and the values of `π` above index `k` are
ignored. This is equivalent to using tuples `Fin (k+1) → σ` (any tuple extends to a function
`Nat → σ` because the tuple itself witnesses that `σ` is inhabited) and makes cutting and
splicing paths simple index arithmetic.

The state type `σ` is arbitrary (any universe, finite or infinite); the transition relation need
not be total (states without successors are allowed).

Depth conventions (these matter: if `BMC k` meant `Base k`, BMC at the reachability recurrence
diameter would be unsound, see `base_at_recurrence_diameter_unsound`):
* `Step T P k` assumes `P` on the first `k` states of a path with `k` transitions (`k+1`
  states) and demands `P` on the last state. `Step T P 1` is ordinary (1-)induction.
* `Base I T P k` checks every path from an initial state with at most `k` states, i.e. at most
  `k - 1` transitions. These are exactly the states the step at depth `k` relies on.
* `BMC I T P k` (bounded model checking to depth `k`) checks every path from an initial state
  with at most `k` transitions. It is `Base I T P (k + 1)` by definition.

Diameters (`ReachDiameterBound`, `IsReachDiameter`, `ReachRecurrenceBound`,
`IsReachRecurrenceDiameter`) are the *initialized* notions, measured along paths that start in an
initial state (the reachability diameter `rd` and reachability recurrence diameter `rrd` of
Kroening and Strichman). They are not the graph-theoretic (uninitialized) diameter and recurrence
diameter, which quantify over all start states and are never smaller.
-/

namespace Toy.KInd

universe u

variable {σ : Type u}

/-- `IsPath T k π`: the states `π 0, π 1, …, π k` form a `T`-path with `k` transitions,
i.e. `T (π i) (π (i+1))` for every `i < k`. Values of `π` above index `k` are ignored.
Captures a finite execution fragment of the transition system. -/
def IsPath (T : σ → σ → Prop) (k : Nat) (π : Nat → σ) : Prop :=
  ∀ i, i < k → T (π i) (π (i + 1))

/-- `IsSimple k π`: the states `π 0, …, π k` are pairwise distinct. Captures the
"loop-free" (simple-path) constraint of strengthened k-induction. -/
def IsSimple (k : Nat) (π : Nat → σ) : Prop :=
  ∀ i j, i ≤ k → j ≤ k → π i = π j → i = j

/-- `ReachIn I T k s`: some path with exactly `k` transitions starts in an initial state and
ends in `s`. -/
def ReachIn (I : σ → Prop) (T : σ → σ → Prop) (k : Nat) (s : σ) : Prop :=
  ∃ π : Nat → σ, I (π 0) ∧ IsPath T k π ∧ π k = s

/-- `Reachable I T s`: `s` is reachable from an initial state in finitely many transitions. -/
def Reachable (I : σ → Prop) (T : σ → σ → Prop) (s : σ) : Prop :=
  ∃ k, ReachIn I T k s

/-- `ReachWithin I T k s`: `s` is reachable in at most `k` transitions. -/
def ReachWithin (I : σ → Prop) (T : σ → σ → Prop) (k : Nat) (s : σ) : Prop :=
  ∃ j, j ≤ k ∧ ReachIn I T j s

/-- Safety `□ P`: every reachable state satisfies `P` (`P` is an invariant of the system). -/
def Invariant (I : σ → Prop) (T : σ → σ → Prop) (P : σ → Prop) : Prop :=
  ∀ s, Reachable I T s → P s

/-- Base case of k-induction at depth `k`: every path from an initial state with at most `k`
states (at most `k - 1` transitions) satisfies `P` at every position. `Base I T P 0` is
vacuous.

All prefix lengths `j < k` are checked, not only paths with exactly `k - 1` transitions. The two
agree when every state has a successor (`base_iff_exactBase_of_total`); without that assumption a
check of exact length only can be unsound, because a bad state at a dead end reached in fewer than
`k - 1` transitions is never examined (`exact_length_base_unsound_without_totality`). -/
def Base (I : σ → Prop) (T : σ → σ → Prop) (P : σ → Prop) (k : Nat) : Prop :=
  ∀ j, j < k → ∀ π : Nat → σ, I (π 0) → IsPath T j π → ∀ i, i ≤ j → P (π i)

/-- Inductive step of (plain) k-induction at depth `k`: on every path with `k` transitions
(`k + 1` states), if the first `k` states satisfy `P` then so does the last one. Initial states
play no role; the path may start anywhere, including in unreachable states. `Step T P 1` says
that `P` is preserved by one transition (1-inductiveness of `P`, without initiation);
`Step T P 0` says that `P` holds everywhere. -/
def Step (T : σ → σ → Prop) (P : σ → Prop) (k : Nat) : Prop :=
  ∀ π : Nat → σ, IsPath T k π → (∀ i, i < k → P (π i)) → P (π k)

/-- Inductive step of k-induction strengthened by the simple-path constraint: `Step`
restricted to paths whose `k + 1` states are pairwise distinct. -/
def SimpleStep (T : σ → σ → Prop) (P : σ → Prop) (k : Nat) : Prop :=
  ∀ π : Nat → σ, IsPath T k π → IsSimple k π → (∀ i, i < k → P (π i)) → P (π k)

/-- Bounded model checking to depth `k`: every path from an initial state with at most `k`
transitions satisfies `P` (equivalently, no counterexample of length `≤ k` exists). Defined as
`Base I T P (k + 1)` so that the relation to the base case is definitional. -/
def BMC (I : σ → Prop) (T : σ → σ → Prop) (P : σ → Prop) (k : Nat) : Prop :=
  Base I T P (k + 1)

/-- `ReachDiameterBound I T d`: every reachable state is reachable from an initial state in at
most `d` transitions. The least such `d` (`IsReachDiameter`) is the reachability diameter: the
number of transitions of a longest shortest path from an initial state to a reachable state,
and `0` when nothing is reachable (for example when there is no initial state). On an infinite
state type no finite bound need exist. -/
def ReachDiameterBound (I : σ → Prop) (T : σ → σ → Prop) (d : Nat) : Prop :=
  ∀ s, Reachable I T s → ReachWithin I T d s

/-- `IsReachDiameter I T d`: `d` is the least `ReachDiameterBound` (the reachability diameter).
With no initial state, `IsReachDiameter I T 0` holds. -/
def IsReachDiameter (I : σ → Prop) (T : σ → σ → Prop) (d : Nat) : Prop :=
  ReachDiameterBound I T d ∧ ∀ d', ReachDiameterBound I T d' → d ≤ d'

/-- `ReachRecurrenceBound I T r`: every simple path that starts in an initial state has at most
`r` transitions. The least such `r` (`IsReachRecurrenceDiameter`) is the reachability recurrence
diameter: the number of transitions of a longest simple path from an initial state, and `0` when
there is no initial state. On an infinite state type no finite bound need exist, even when a
finite `ReachDiameterBound` does. -/
def ReachRecurrenceBound (I : σ → Prop) (T : σ → σ → Prop) (r : Nat) : Prop :=
  ∀ j (π : Nat → σ), I (π 0) → IsPath T j π → IsSimple j π → j ≤ r

/-- `IsReachRecurrenceDiameter I T r`: `r` is the least `ReachRecurrenceBound` (the reachability
recurrence diameter). With no initial state, `IsReachRecurrenceDiameter I T 0` holds. -/
def IsReachRecurrenceDiameter (I : σ → Prop) (T : σ → σ → Prop) (r : Nat) : Prop :=
  ReachRecurrenceBound I T r ∧ ∀ r', ReachRecurrenceBound I T r' → r ≤ r'

/-- Initiation: every initial state satisfies `Q`. -/
def Initiation (I : σ → Prop) (Q : σ → Prop) : Prop :=
  ∀ s, I s → Q s

/-- Consecution: `Q` is preserved by every transition (the step of 1-induction for `Q`). -/
def Consecution (T : σ → σ → Prop) (Q : σ → Prop) : Prop :=
  ∀ s t, Q s → T s t → Q t

/-- `FutureSafe T P m s`: every path from `s` with at most `m` transitions ends in a
`P`-state, i.e. `P` holds now and for the next `m` steps along every execution from `s`. -/
def FutureSafe (T : σ → σ → Prop) (P : σ → Prop) (m : Nat) (s : σ) : Prop :=
  ∀ j, j ≤ m → ∀ π : Nat → σ, π 0 = s → IsPath T j π → P (π j)

/-! ## Basic path lemmas -/

section Lemmas

variable {I : σ → Prop} {T : σ → σ → Prop} {P : σ → Prop}

theorem IsPath.mono {k j : Nat} {π : Nat → σ} (h : IsPath T k π) (hj : j ≤ k) :
    IsPath T j π :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hj)

theorem IsSimple.mono {k j : Nat} {π : Nat → σ} (h : IsSimple k π) (hj : j ≤ k) :
    IsSimple j π :=
  fun a b ha hb hab => h a b (Nat.le_trans ha hj) (Nat.le_trans hb hj) hab

/-- The suffix of a path starting at index `a` is a path. -/
theorem IsPath.shift {a b : Nat} {π : Nat → σ} (h : IsPath T (a + b) π) :
    IsPath T b (fun t => π (a + t)) := by
  intro i hi
  have := h (a + i) (by omega)
  simpa [Nat.add_assoc] using this

theorem IsSimple.shift {a b : Nat} {π : Nat → σ} (h : IsSimple (a + b) π) :
    IsSimple b (fun t => π (a + t)) := by
  intro i j hi hj hij
  have := h (a + i) (a + j) (by omega) (by omega) hij
  omega

theorem reachIn_zero_iff {s : σ} : ReachIn I T 0 s ↔ I s := by
  constructor
  · rintro ⟨π, h0, -, hs⟩
    exact hs ▸ h0
  · intro h
    exact ⟨fun _ => s, h, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩

/-- Extending a path by one transition. -/
theorem ReachIn.succ {k : Nat} {s t : σ} (h : ReachIn I T k s) (ht : T s t) :
    ReachIn I T (k + 1) t := by
  obtain ⟨π, h0, hp, hs⟩ := h
  refine ⟨fun i => if i ≤ k then π i else t, ?_, ?_, ?_⟩
  · simpa using h0
  · intro i hi
    by_cases hik : i < k
    · have h1 : i ≤ k := Nat.le_of_lt hik
      have h2 : i + 1 ≤ k := hik
      simp only [h1, h2, ite_true]
      exact hp i hik
    · have hi' : i = k := by omega
      subst hi'
      simp only [Nat.le_refl, ite_true, Nat.not_succ_le_self, ite_false]
      exact hs ▸ ht
  · simp only [Nat.not_succ_le_self, ite_false]

theorem reachIn_succ_iff {k : Nat} {t : σ} :
    ReachIn I T (k + 1) t ↔ ∃ s, ReachIn I T k s ∧ T s t := by
  constructor
  · rintro ⟨π, h0, hp, ht⟩
    exact ⟨π k, ⟨π, h0, hp.mono (Nat.le_succ k), rfl⟩, ht ▸ hp k (Nat.lt_succ_self k)⟩
  · rintro ⟨s, hs, hst⟩
    exact hs.succ hst

/-- Every state on a path from an initial state is reachable (in as many steps as its index). -/
theorem reachIn_of_path {k i : Nat} {π : Nat → σ} (h0 : I (π 0)) (hp : IsPath T k π)
    (hi : i ≤ k) : ReachIn I T i (π i) :=
  ⟨π, h0, hp.mono hi, rfl⟩

theorem base_iff_reachIn {k : Nat} :
    Base I T P k ↔ ∀ j, j < k → ∀ s, ReachIn I T j s → P s := by
  constructor
  · rintro h j hj s ⟨π, h0, hp, rfl⟩
    exact h j hj π h0 hp j (Nat.le_refl j)
  · intro h j hj π h0 hp i hi
    exact h i (by omega) (π i) (reachIn_of_path h0 hp hi)

theorem bmc_iff_reachIn {k : Nat} :
    BMC I T P k ↔ ∀ j, j ≤ k → ∀ s, ReachIn I T j s → P s := by
  unfold BMC
  rw [base_iff_reachIn]
  exact ⟨fun h j hj => h j (Nat.lt_succ_of_le hj), fun h j hj => h j (Nat.le_of_lt_succ hj)⟩

theorem reachable_of_init {s : σ} (h : I s) : Reachable I T s :=
  ⟨0, reachIn_zero_iff.mpr h⟩

theorem Reachable.step {s t : σ} (h : Reachable I T s) (ht : T s t) : Reachable I T t := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, hk.succ ht⟩

/-- An invariant passes every base check. -/
theorem base_of_invariant (h : Invariant I T P) (k : Nat) : Base I T P k := by
  rw [base_iff_reachIn]
  intro j _ s hs
  exact h s ⟨j, hs⟩

theorem bmc_of_invariant (h : Invariant I T P) (k : Nat) : BMC I T P k :=
  base_of_invariant h (k + 1)

/-- Plain steps imply simple steps (the simple-path constraint only removes paths). -/
theorem Step.simpleStep {k : Nat} (h : Step T P k) : SimpleStep T P k :=
  fun π hp _ hP => h π hp hP

theorem step_zero_iff : Step T P 0 ↔ ∀ s, P s := by
  constructor
  · intro h s
    exact h (fun _ => s) (fun i hi => absurd hi (Nat.not_lt_zero _))
      (fun i hi => absurd hi (Nat.not_lt_zero _))
  · intro h π _ _
    exact h _

theorem step_one_iff : Step T P 1 ↔ Consecution T P := by
  constructor
  · intro h s t hs hst
    have := h (fun i => if i = 0 then s else t)
      (by intro i hi; have : i = 0 := by omega
          subst this; simpa using hst)
      (by intro i hi; have : i = 0 := by omega
          subst this; simpa using hs)
    simpa using this
  · intro h π hp hP
    exact h (π 0) (π 1) (hP 0 (by decide)) (hp 0 (by decide))

/-- Two-transition paths, spelled out on three explicit states (used to decide small
examples). -/
theorem step_two_iff :
    Step T P 2 ↔ ∀ a b c, T a b → T b c → P a → P b → P c := by
  constructor
  · intro h a b c hab hbc ha hb
    have := h (fun i => if i = 0 then a else if i = 1 then b else c)
      (by intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl <;> simpa)
      (by intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl <;> simpa)
    simpa using this
  · intro h π hp hP
    exact h (π 0) (π 1) (π 2) (hp 0 (by decide)) (hp 1 (by decide)) (hP 0 (by decide))
      (hP 1 (by decide))

theorem simpleStep_one_iff :
    SimpleStep T P 1 ↔ ∀ a b, T a b → a ≠ b → P a → P b := by
  constructor
  · intro h a b hab hne ha
    have := h (fun i => if i = 0 then a else b)
      (by intro i hi; have : i = 0 := by omega
          subst this; simpa using hab)
      (by intro i j hi hj hij
          have hi' : i = 0 ∨ i = 1 := by omega
          have hj' : j = 0 ∨ j = 1 := by omega
          rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp_all [eq_comm])
      (by intro i hi; have : i = 0 := by omega
          subst this; simpa using ha)
    simpa using this
  · intro h π hp hs hP
    exact h (π 0) (π 1) (hp 0 (by decide))
      (fun he => absurd (hs 0 1 (by decide) (by decide) he) (by decide)) (hP 0 (by decide))

theorem simpleStep_two_iff :
    SimpleStep T P 2 ↔
      ∀ a b c, T a b → T b c → a ≠ b → a ≠ c → b ≠ c → P a → P b → P c := by
  constructor
  · intro h a b c hab hbc h1 h2 h3 ha hb
    have := h (fun i => if i = 0 then a else if i = 1 then b else c)
      (by intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl <;> simpa)
      (by intro i j hi hj hij
          have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
            simp_all [eq_comm])
      (by intro i hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl <;> simpa)
    simpa using this
  · intro h π hp hs hP
    have hne : ∀ i j, i ≤ 2 → j ≤ 2 → i ≠ j → π i ≠ π j :=
      fun i j hi hj hij he => hij (hs i j hi hj he)
    exact h (π 0) (π 1) (π 2) (hp 0 (by decide)) (hp 1 (by decide))
      (hne 0 1 (by decide) (by decide) (by decide)) (hne 0 2 (by decide) (by decide) (by decide))
      (hne 1 2 (by decide) (by decide) (by decide)) (hP 0 (by decide)) (hP 1 (by decide))

end Lemmas

end Toy.KInd
