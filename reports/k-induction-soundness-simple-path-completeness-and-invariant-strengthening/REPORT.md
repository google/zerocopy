# k-induction: soundness, simple-path completeness, BMC thresholds, and invariant strengthening (Lean 4 formalization)

## Summary

This package formalizes, in Lean 4 without Mathlib, the core theory of k-induction for safety properties of transition systems: soundness of plain and simple-path k-induction, completeness of simple-path k-induction on finite state types and its failure on infinite ones, incompleteness of plain and fixed-depth k-induction, completeness thresholds of bounded model checking (BMC) via the reachability diameter and reachability recurrence diameter, and the relation between k-induction and 1-inductive strengthenings. All 22 results are re-derivations of known or folklore results (tiers T0 and T1); none is claimed to be new. Every statement is kernel-checked; the model is a toy model (see Applicability).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Depth conventions used throughout: `Base k` checks every path from an initial state with at most `k` states, i.e. at most `k - 1` transitions, of every length (not only the longest); `Step k` assumes `P` on the first `k` of `k + 1` path states; `SimpleStep k` is `Step k` restricted to pairwise distinct states; `BMC k` is `Base (k + 1)` (at most `k` transitions). Diameters are measured from initial states.

Results (numbering is used throughout this report):

1. **`kind-sound`** (theorem, T0). For every transition system (finite or infinite, total or not) and every depth k, if Base k holds (every path from an initial state with at most k states, of every length, stays in P) and Step k holds (every path of k+1 states whose first k states satisfy P ends in P), then P holds in every reachable state.
2. **`kind-simple-sound`** (theorem, T0). The same soundness holds when the step is restricted to simple paths (k+1 pairwise distinct full states, SimpleStep k), together with the unchanged Base k.
3. **`loop-removal`** (theorem, T0). Every state reachable from an initial state in m transitions is reachable from some initial state along a simple path with at most m transitions.
4. **`depth-monotonicity`** (theorem, T0). For depths k <= k', Base k with Step k implies Base k' with Step k', Step k alone implies Step k', and SimpleStep k alone implies SimpleStep k'.
5. **`one-induction-fails-two-induction-succeeds`** (counterexample, T0). In the concrete 3-state system TwoInd, the invariant P passes Base 2 and Step 2 but fails Step 1 (a reference point; it is the case k = 1 of the next result).
6. **`fixed-depth-kind-incomplete`** (impossibility, T0). For every k there is a finite (k+2)-state system, Ladder k, whose invariant passes Base (k+1) and Step (k+1) while SimpleStep j, and hence Step j, fails at every depth j <= k.
7. **`plain-kind-incomplete-every-depth`** (impossibility, T0). In the concrete 3-state system SelfLoop, P is invariant but plain Step k fails for every k, so plain k-induction proves it at no depth.
8. **`simple-step-vacuous-at-card`** (theorem, T0). When the state type is Fin n, SimpleStep T P k holds for every transition relation T, every property P and every depth k >= n, because no simple path has k transitions.
9. **`simple-kind-complete-fin`** (theorem, T0). When the state type is Fin n, every property P that holds in all reachable states passes Base n and SimpleStep n.
10. **`simple-kind-complete-fin-pred-of-init`** (theorem, T1). When the state type is Fin (m+1) and at least one initial state exists, every property P that holds in all reachable states passes Base m and SimpleStep m (depth n-1 for n states).
11. **`simple-kind-incomplete-infinite`** (impossibility, T0). In the concrete infinite system NatDescent (state type Nat), which has an initial state, exactly one reachable state, and reachability-diameter and reachability-recurrence bounds 0, the invariant P passes Base k but fails SimpleStep k for every k.
12. **`bmc-complete-of-diameter-bound`** (theorem, T0). If d bounds the reachability diameter (every reachable state is reachable within d transitions), d <= k, and BMC to depth k (every path from an initial state with at most k transitions stays in P) holds, then P is invariant.
13. **`recurrence-bound-is-diameter-bound`** (theorem, T0). If every simple path from an initial state has at most r transitions, then r bounds the reachability diameter, and hence BMC to any depth k >= r proves that P is invariant.
14. **`reach-diameter-le-reach-recurrence-bound`** (theorem, T0). If d is the reachability diameter (the least reachability-diameter bound) and every simple path from an initial state has at most r transitions, then d <= r.
15. **`bmc-complete-fin`** (theorem, T0). When the state type is Fin n, BMC to depth n-1 (truncated subtraction, so depth 0 when n = 0) proves that P is invariant.
16. **`bmc-threshold-characterization`** (characterization, T1). BMC to depth k implies invariance for every property P if and only if k bounds the reachability diameter; when it does not, the property 'reachable within k transitions' passes BMC k but is not invariant.
17. **`base-at-recurrence-diameter-off-by-one`** (counterexample, T0). In the concrete 2-state system OneEdge, whose reachability recurrence diameter is 1, Base 1 holds although P is not invariant, while BMC 1 (= Base 2) correctly fails (a reference point on depth conventions).
18. **`diameter-below-recurrence-diameter`** (counterexample, T0). For every n >= 2 the n-state complete DAG TriangleN (single initial state) has reachability diameter 1 and reachability recurrence diameter n-1, a gap of n-2 that is positive only for n >= 3.
19. **`inductive-strengthening`** (theorem, T0). If every initial state satisfies P and Q, and every transition from a state satisfying P and Q leads to a state satisfying P and Q, then P is invariant.
20. **`reachable-strongest-inductive-invariant`** (characterization, T0). The reachable set is the strongest predicate that satisfies initiation and consecution, so P is invariant iff P together with Reachable satisfies initiation and consecution iff some such predicate implies P; dually, 'every path from the state ends in P' is the weakest consecution-closed predicate implying P, and it holds initially exactly when P is invariant.
21. **`k-inductive-has-explicit-1-inductive-strengthening`** (theorem, T0). If P passes Base (k+1) and SimpleStep (k+1) (in particular, if it passes plain (k+1)-induction), then FutureSafe T P k, 'every path with at most k transitions from the state ends in P', satisfies initiation and consecution and implies P.
22. **`exact-length-base-needs-totality`** (theorem, T0). If every state has a successor, checking P at every position of every path from an initial state with exactly k transitions is equivalent to Base (k+1); without totality, the exact-length check can be weaker and unsound as a k-induction base, as proved at k = 2 (at k = 0 the two checks coincide for every transition relation).

Each result has non-claims that limit how it may be read; they are listed per result at the start of **Boundaries**, together with escape hatches for the impossibility results. Read them before relying on a result.

## Applicability

**Model fidelity.** This is a toy model. A transition system is a state type `σ` (any universe,
finite or infinite), an initial-state predicate `I : σ → Prop` and a transition relation
`T : σ → σ → Prop` that need not be total; a safety property is a state predicate `P`. Paths are
explicit finite state sequences (`π : Nat → σ` together with a transition count `k`; only
`π 0, …, π k` matter). The definitions are meant to capture the checks performed by SAT/SMT-based
k-induction engines (the base and step queries of Sheeran, Singh and Stålmarck 2000 and of Eén and
Sörensson 2003, including the simple-path ("loop-free", "uniqueness") constraint), the completeness
thresholds of bounded model checking (the reachability diameter and reachability recurrence
diameter of Kroening and Strichman 2003, the initialized counterparts of the diameter and
recurrence diameter of Biere et al. 1999), and the inductive-strengthening vocabulary of IC3/PDR (initiation and
consecution, Bradley 2011).

Known gaps between the model and real systems:

* No symbolic encoding, SAT/SMT solving, incremental solving, input variables, fairness, liveness
  or LTL: only safety (`□ P`) is modelled.
* Distinctness in `SimpleStep` is over full states. Distinctness over a projection of the state is
  not covered by the soundness theorem and is unsound in general (`projected_simple_step_unsound`).
* Variants of the step with "no initial state after position 0" constraints, Sheeran et al.'s
  forward termination check, relative inductiveness with frames, and property-directed variants
  are not modelled.
* Diameters are the initialized notions (measured along paths from initial states), stated as
  bound predicates plus least-bound predicates; no function computes them. With no initial state
  both least bounds are `0`.
* Finiteness results are stated for state type `Fin n`; for real models `n` is the size of the full
  state space.

Every theorem is a kernel-checked statement about this model (`Basis: execution (Lean kernel
check)`). Each finding below also carries a separate `Basis: derived (modeling bridge)` line that
states, with its reasoning, what the theorem suggests about real engines; those lines are not
proved.

**Depth conventions.** `Base I T P k` checks every path from an initial state with at most `k`
states (at most `k - 1` transitions, every length, not only the longest); `Step T P k` assumes `P`
on the first `k` states of a path with `k` transitions and demands it on the last;
`BMC I T P k` is by definition `Base I T P (k + 1)` (at most `k` transitions). Literature indices
differ: Jovanović and Dutertre 2016 (Definition II.2) use the same convention as `Base k` and
`Step k` here; Sheeran et al.'s "induction with depth i" is `Step (i + 1)` here; Gurfinkel and
Ivrii 2017 (eq. 5) assume `k + 1` consecutive states, which is depth `k + 1` here. Translate before
comparing.

**Subjects.** The Lean 4 toolchain release in `REPORT.json` is the checker for every theorem. The
papers in `REPORT.json` are the primary sources whose known results are restated (tiers T0 and T1);
the report does not claim that their proofs were checked, only that the restated statements are
proved here, and each finding states how its statement relates to the source.

**Lean.** `leanprover/lean4:v4.34.1`, core Lean and `Std` only, no Mathlib, no Lake dependencies.
All general statements are universe-polymorphic (`σ : Type u`). Namespace `Toy.KInd`; library
`KInd` in `lean/`.

## Findings

All Lean names below are in namespace `Toy.KInd` (prefix omitted in prose). Statements quoted from the source use the section variables `{σ : Type u} {I : σ → Prop} {T : σ → σ → Prop} {P : σ → Prop}` where these are not bound explicitly.

### Definitions

The core definitions, quoted from `lean/KInd/Basic.lean` (each definition's docstring states what it is meant to capture):

```lean
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
check of exact length only is unsound, because a bad state at a dead end reached in fewer than
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
```

Intended positive and negative examples for every definition are proved in `lean/KInd/Examples.lean`: `isPath_pos`/`isPath_neg`, `isSimple_pos`/`isSimple_neg`, `reachIn_pos`/`reachIn_neg`, `reachable_pos`/`reachable_neg`, `reachWithin_pos`/`reachWithin_neg`, `invariant_pos`/`invariant_neg`, `base_pos`/`base_neg` (and `base_zero_vacuous`), `bmc_pos`/`bmc_neg`, `step_pos`/`step_neg`, `simpleStep_pos`/`simpleStep_neg` (and `simpleStep_not_step`), `reachDiameterBound_pos`/`reachDiameterBound_neg`, `isReachDiameter_pos`/`isReachDiameter_neg`, `reachRecurrenceBound_pos`/`reachRecurrenceBound_neg`, `isReachRecurrenceDiameter_pos`/`isReachRecurrenceDiameter_neg`, `initiation_pos`/`initiation_neg`, `consecution_pos`/`consecution_neg`, `futureSafe_pos`/`futureSafe_neg`. The empty-initial-set convention is proved by `isReachDiameter_no_init` and `isReachRecurrenceDiameter_no_init`, and the contrast between initialized and graph-theoretic diameters by `selfLoop_reach_diameters_zero`.

Concrete systems used by the results (each is `I`, `T`, and where relevant `P`):

```lean
-- lean/KInd/Systems.lean
namespace Chain
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t => t.val = s.val + 1
abbrev P : Fin 3 → Prop := fun s => s.val ≠ 2
end Chain
```
```lean
-- lean/KInd/Systems.lean
namespace OneEdge
abbrev I : Fin 2 → Prop := fun s => s.val = 0
abbrev T : Fin 2 → Fin 2 → Prop := fun s t => s.val = 0 ∧ t.val = 1
abbrev P : Fin 2 → Prop := fun s => s.val = 0
end OneEdge
```
```lean
-- lean/KInd/Systems.lean
namespace Triangle
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t => s.val < t.val
end Triangle
```
```lean
-- lean/KInd/Systems.lean
namespace Stuck
abbrev I : Fin 1 → Prop := fun _ => True
abbrev T : Fin 1 → Fin 1 → Prop := fun _ _ => False
abbrev P : Fin 1 → Prop := fun _ => False
end Stuck
```
```lean
-- lean/KInd/Systems.lean
namespace TriangleN
abbrev I (m : Nat) : Fin (m + 2) → Prop := fun s => s.val = 0
abbrev T (m : Nat) : Fin (m + 2) → Fin (m + 2) → Prop := fun s t => s.val < t.val
end TriangleN
```
```lean
-- lean/KInd/Systems.lean
namespace FinChain
abbrev I (m : Nat) : Fin (m + 2) → Prop := fun s => s.val = 0
abbrev T (m : Nat) : Fin (m + 2) → Fin (m + 2) → Prop := fun s t => t.val = s.val + 1
abbrev P (m : Nat) : Fin (m + 2) → Prop := fun s => s.val ≠ m + 1
end FinChain
```
```lean
-- lean/KInd/Systems.lean
namespace NatSucc
abbrev I : Nat → Prop := fun s => s = 0
abbrev T : Nat → Nat → Prop := fun s t => t = s + 1
end NatSucc
```
```lean
-- lean/KInd/Systems.lean
namespace StarChain
abbrev I : Nat → Prop := fun s => s = 0
abbrev T : Nat → Nat → Prop := fun s t => (s = 0 ∧ 1 ≤ t) ∨ (1 ≤ s ∧ t = s + 1)
end StarChain
```
```lean
-- lean/KInd/Systems.lean
namespace Branch4
abbrev I : Fin 4 → Prop := fun s => s.val = 0
abbrev T : Fin 4 → Fin 4 → Prop := fun s t =>
  (s.val = 0 ∧ t.val = 0) ∨ (s.val = 1 ∧ t.val = 2) ∨ (s.val = 2 ∧ t.val = 3) ∨
    (s.val = 1 ∧ t.val = 3)
abbrev P : Fin 4 → Prop := fun s => s.val ≠ 3
end Branch4
```
```lean
-- lean/KInd/Completeness.lean
namespace NoInitChain
abbrev I (m : Nat) : Fin (m + 1) → Prop := fun _ => False
abbrev T (m : Nat) : Fin (m + 1) → Fin (m + 1) → Prop := fun s t => t.val = s.val + 1
abbrev P (m : Nat) : Fin (m + 1) → Prop := fun s => s.val ≠ m
end NoInitChain
```
```lean
-- lean/KInd/Completeness.lean
namespace IsolatedInitChain
abbrev I (m : Nat) : Fin (m + 2) → Prop := fun s => s.val = m + 1
abbrev T (m : Nat) : Fin (m + 2) → Fin (m + 2) → Prop :=
  fun s t => s.val < m ∧ t.val = s.val + 1
abbrev P (m : Nat) : Fin (m + 2) → Prop := fun s => s.val ≠ m
end IsolatedInitChain
```
```lean
-- lean/KInd/Completeness.lean
namespace NatDescent
abbrev I : Nat → Prop := fun s => s = 0
abbrev T : Nat → Nat → Prop := fun s t => (s = 0 ∧ t = 0) ∨ (2 ≤ s ∧ t + 1 = s)
abbrev P : Nat → Prop := fun s => s ≠ 1
end NatDescent
```
```lean
-- lean/KInd/Completeness.lean
namespace SelfLoop
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t =>
  (s.val = 0 ∧ t.val = 0) ∨ (s.val = 1 ∧ t.val = 1) ∨ (s.val = 1 ∧ t.val = 2)
abbrev P : Fin 3 → Prop := fun s => s.val ≠ 2
end SelfLoop
```
```lean
-- lean/KInd/Separation.lean
namespace TwoInd
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t => (s.val = 0 ∧ t.val = 0) ∨ (s.val = 1 ∧ t.val = 2)
abbrev P : Fin 3 → Prop := fun s => s.val ≠ 2
end TwoInd
```
```lean
-- lean/KInd/Separation.lean
namespace Ladder
abbrev I (k : Nat) : Fin (k + 2) → Prop := fun s => s.val = 0
abbrev T (k : Nat) : Fin (k + 2) → Fin (k + 2) → Prop := fun s t =>
  (s.val = 0 ∧ t.val = 0) ∨ (1 ≤ s.val ∧ s.val ≤ k ∧ t.val = s.val + 1)
abbrev P (k : Nat) : Fin (k + 2) → Prop := fun s => s.val ≠ k + 1
end Ladder
```
```lean
-- lean/KInd/Remarks.lean
namespace AllInitChain
abbrev I (m : Nat) : Fin (m + 1) → Prop := fun _ => True
abbrev T (m : Nat) : Fin (m + 1) → Fin (m + 1) → Prop := fun s t => t.val = s.val + 1
end AllInitChain
```
```lean
-- lean/KInd/Remarks.lean
namespace TwoCycle
abbrev I : Fin 2 → Prop := fun s => s.val = 0
abbrev T : Fin 2 → Fin 2 → Prop := fun s t => (s.val = 0 ∧ t.val = 1) ∨ (s.val = 1 ∧ t.val = 0)
abbrev P : Fin 2 → Prop := fun s => s.val = 0
end TwoCycle
```

`AllInitChain` and `TwoCycle` are used only by supporting theorems that back non-claims (see Evidence).

### 1. `kind-sound`

- **Kind:** theorem. **Tier:** T0. Standard soundness of k-induction (Sheeran, Singh and Stålmarck 2000), restated in this package's depth convention, which is that of Jovanović and Dutertre 2016 (Definition II.2). Soundness of k-induction encodings was mechanized earlier in Coq (Ishii and Fujii 2020).
- **Depth:** `shallow`.
- **Plain claim:** For every transition system (finite or infinite, with or without dead-end states) and every depth k: if every path from an initial state with at most k states stays in P (Base k: all path lengths below k are checked, not only the longest) and every path of k+1 states whose first k states satisfy P ends in P (Step k), then every reachable state satisfies P.
- **Lean statement** (`Toy.KInd.kind_sound`):

  ```lean
  -- lean/KInd/Soundness.lean:24
  theorem kind_sound {k : Nat} (hbase : Base I T P k) (hstep : Step T P k) :
      Invariant I T P
  ```

  With the key definitions unfolded:

  ```text
  (∀ j < k, ∀ π, I (π 0) → (∀ i < j, T (π i) (π (i+1))) → ∀ i ≤ j, P (π i)) → (∀ π, (∀ i < k, T (π i) (π (i+1))) → (∀ i < k, P (π i)) → P (π k)) → ∀ s, (∃ m π, I (π 0) ∧ (∀ i < m, T (π i) (π (i+1))) ∧ π m = s) → P s
  ```

- **Hypothesis ledger:**
  - `hbase : Base I T P k` (tight: counterexample `Toy.KInd.kind_sound_needs_base`, `Toy.KInd.kind_sound_base_depth_tight`). Establishes P on every state reachable in fewer than k transitions, which the step assumes without proof (vacuous at k = 0, where Step 0 alone says P holds everywhere).
  - `hstep : Step T P k` (tight: counterexample `Toy.KInd.kind_sound_needs_step`). Propagates P beyond the depth covered by the base.
- **Non-vacuity witness:** TwoInd (states Fin 3, 0 initial with a self-loop, unreachable edge 1 -> 2, P excludes 2) at depth k = 2. Lean: `Toy.KInd.nonvacuity_kind_sound`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. Definition II.2 (k-induction: the base checks paths from initial states of each length l < k, the step assumes k consecutive P-states; the same depth convention as Base k and Step k here). Footnote 3 (Section II): 'If P is k-inductive then P ∧ ◦P ∧ ◦◦P ∧ ... ∧ ◦◦···◦P [k-1 operators] is inductive, where ◦ stands for "next state"'; reading ◦ as 'in every successor state', this conjunction is FutureSafe T P (k-1). The footnote has no proof and concerns plain (not simple-path) k-induction. Lemma III.1: there are N-inductive properties whose shortest inductive strengthening has size larger than N; Lemma III.2: there is a property that is k-inductive for some k > 1 but has no inductive strengthening (its example lives in the quantifier-free fragment of a theory of arrays).
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
  - D. Ishii, S. Fujii, 'Formalizing the Soundness of the Encoding Methods of SAT-based Model Checking', TASE 2020, pp. 105-112, doi:10.1109/TASE49443.2020.00023 (arXiv:2006.13613; Coq development at https://github.com/dsksh/coq-smc). Earlier mechanization, in Coq, of the soundness of BMC and k-induction encodings (its k-induction step uses plain paths), of Sheeran et al.'s loop-free forward and backward encodings, of a reduction of safety to loop-free paths (its Lemma 1), and of a simplified PDR. The paper states that completeness is not formalized.
  - K. Batz, B. L. Kaminski, L. Kehrer, G. Klein, H. Urbat, T. Schmid, 'The Algebra of Iterative Constructions', Archive of Formal Proofs, April 29, 2026, https://www.isa-afp.org/entries/Iteration_Algebra.html. Isabelle/HOL mechanization; its abstract lists 'a fixed point-theoretic generalization of k-induction' among its results. Lattice-level, not the path-based statements here.
  - A. Gurfinkel, A. Ivrii, 'K-Induction without Unrolling', FMCAD 2017, pp. 148-155, doi:10.23919/FMCAD.2017.8102253. Defines k-invariants (eq. 4: all states reachable in at most k steps satisfy the formula) and k-inductive invariants (eq. 5: the step assumes k+1 consecutive states, i.e. depth k+1 here). States that neither induction nor k-induction is complete and that k-induction restricted to loop-free paths is complete (citing Sheeran et al.). Its Lemma 2: if the K-Ind procedure returns BLOCKED, the returned G is an inductive strengthening of the clause relative to a 0-invariant F0; its Theorem 1, under the stated assumption that Generalize(¬s) always returns ¬s, characterizes when K-Ind returns BLOCKED (the clause is k-inductive relative to F0).
  - P. Bjesse, K. Claessen, 'SAT-Based Verification without State Space Traversal', FMCAD 2000, LNCS 1954, pp. 372-389, doi:10.1007/3-540-40922-X_23. SAT-based induction contemporaneous with Sheeran et al.; bibliographic data verified on dblp, text not consulted here.
  - L. de Moura, H. Rueß, M. Sorea, 'Bounded Model Checking and Induction: From Refutation to Verification', CAV 2003, LNCS 2725, pp. 14-26, doi:10.1007/978-3-540-45069-6_2. k-induction with decision procedures for infinite-state systems (per its abstract); bibliographic data verified on dblp, full text not consulted here.
  - A. F. Donaldson, L. Haller, D. Kroening, P. Rümmer, 'Software Verification Using k-Induction', SAS 2011, LNCS 6887, pp. 351-368, doi:10.1007/978-3-642-23702-7_26. k-induction applied to software verification; bibliographic data verified on dblp, text not consulted here.
- **Design question:** When is a k-induction proof sound? Answer: always, for every transition system, provided the base covers every path from an initial state with at most k states (every length, not one fixed length, unless the transition relation is total).
- **Non-claims:** see Boundaries, result 1.
- Basis: execution (Lean kernel check) — `Toy.KInd.kind_sound` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — a k-induction engine is sound for a model when its base query fails to find a counterexample exactly when Base k holds and its step query exactly when Step k holds over the model's full state, because the theorem holds for every state type, initial predicate and transition relation. Whether a given engine's queries encode Base and Step literally (same depth index; every base length, or a total transition relation) must be checked separately; it is not checked here.

### 2. `kind-simple-sound`

- **Kind:** theorem. **Tier:** T0. Soundness of strengthened (loop-free) induction with depth (Sheeran, Singh and Stålmarck 2000; unique-state induction of Eén and Sörensson 2003), restated.
- **Depth:** `shallow`.
- **Plain claim:** For every transition system (finite or infinite) and every depth k: if Base k holds and the step holds on every path of k+1 pairwise distinct states (a simple path) whose first k states satisfy P, then every reachable state satisfies P. Distinctness is required of the full states.
- **Lean statement** (`Toy.KInd.kind_simple_sound`):

  ```lean
  -- lean/KInd/Soundness.lean:99
  theorem kind_simple_sound {k : Nat} (hbase : Base I T P k) (hstep : SimpleStep T P k) :
      Invariant I T P
  ```

  With the key definitions unfolded:

  ```text
  Base I T P k → (∀ π, IsPath T k π → (∀ i j, i ≤ k → j ≤ k → π i = π j → i = j) → (∀ i < k, P (π i)) → P (π k)) → ∀ s, Reachable I T s → P s
  ```

- **Hypothesis ledger:**
  - `hbase : Base I T P k` (tight: counterexample `Toy.KInd.kind_simple_sound_needs_base`, `Toy.KInd.kind_simple_sound_needs_base_k2`, `Toy.KInd.kind_simple_sound_base_depth_tight`). Establishes P on every state reachable in fewer than k transitions (vacuous at k = 0).
  - `hstep : SimpleStep T P k` (tight: counterexample `Toy.KInd.kind_sound_needs_step`, `Toy.KInd.kind_simple_sound_needs_step_k2`). Step restricted to simple paths; strictly weaker than Step from depth 2 on (at depth 1 the two coincide), so soundness is not inherited from kind-sound.
- **Non-vacuity witness:** SelfLoop (states Fin 3, 0 initial with a self-loop, unreachable 1 with a self-loop and edge 1 -> 2, P excludes 2) at depth 2, where plain Step 2 fails. Lean: `Toy.KInd.nonvacuity_kind_simple_sound`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
  - D. Ishii, S. Fujii, 'Formalizing the Soundness of the Encoding Methods of SAT-based Model Checking', TASE 2020, pp. 105-112, doi:10.1109/TASE49443.2020.00023 (arXiv:2006.13613; Coq development at https://github.com/dsksh/coq-smc). Earlier mechanization, in Coq, of the soundness of BMC and k-induction encodings (its k-induction step uses plain paths), of Sheeran et al.'s loop-free forward and backward encodings, of a reduction of safety to loop-free paths (its Lemma 1), and of a simplified PDR. The paper states that completeness is not formalized.
  - A. Gurfinkel, A. Ivrii, 'K-Induction without Unrolling', FMCAD 2017, pp. 148-155, doi:10.23919/FMCAD.2017.8102253. Defines k-invariants (eq. 4: all states reachable in at most k steps satisfy the formula) and k-inductive invariants (eq. 5: the step assumes k+1 consecutive states, i.e. depth k+1 here). States that neither induction nor k-induction is complete and that k-induction restricted to loop-free paths is complete (citing Sheeran et al.). Its Lemma 2: if the K-Ind procedure returns BLOCKED, the returned G is an inductive strengthening of the clause relative to a 0-invariant F0; its Theorem 1, under the stated assumption that Generalize(¬s) always returns ¬s, characterizes when K-Ind returns BLOCKED (the clause is k-inductive relative to F0).
- **Design question:** Is it safe to add the simple-path (all-different) constraint to the k-induction step? Answer: yes, soundness is preserved for every system, provided distinctness is imposed on full states.
- **Non-claims:** see Boundaries, result 2.
- Basis: execution (Lean kernel check) — `Toy.KInd.kind_simple_sound` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — engines that add pairwise-distinctness constraints over all state variables to the step keep soundness, because the theorem allows any state type and requires distinctness only of the states the engine's model uses. Distinctness over a projection of the state is outside the theorem and is unsound in general (projected_simple_step_unsound).

### 3. `loop-removal`

- **Kind:** theorem. **Tier:** T0. Standard graph fact: every state reachable from an initial state is reachable from an initial state along a simple path that is no longer. A reduction of safety to loop-free paths was mechanized in Coq by Ishii and Fujii 2020 (their Lemma 1).
- **Depth:** `substantive`.
- **Plain claim:** For every transition system, if a state s is reachable from an initial state in m transitions, then s is reachable from an initial state along a simple path (pairwise distinct states) with at most m transitions.
- **Lean statement** (`Toy.KInd.exists_simple_reachIn`):

  ```lean
  -- lean/KInd/Soundness.lean:47
  theorem exists_simple_reachIn {m : Nat} {s : σ} (h : ReachIn I T m s) :
      ∃ m', m' ≤ m ∧ ∃ π : Nat → σ, I (π 0) ∧ IsPath T m' π ∧ IsSimple m' π ∧ π m' = s
  ```

  With the key definitions unfolded:

  ```text
  ReachIn I T m s → ∃ m' ≤ m, ∃ π, I (π 0) ∧ IsPath T m' π ∧ IsSimple m' π ∧ π m' = s
  ```

- **Hypothesis ledger:**
  - `h : ReachIn I T m s` (tight: counterexample `Toy.KInd.loop_removal_needs_reachIn`). The state must be reachable at all.
- **Non-vacuity witness:** In SelfLoop, the initial state 0 is reached in 3 transitions around its self-loop (a non-simple path). Lean: `Toy.KInd.nonvacuity_exists_simple_reachIn`.
- **Prior art:**
  - A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. Statement numbers follow the technical-report version (CMU-CS-99-101) and may differ in the published version. Definition 19 (diameter: the least d such that whenever a state v is reachable from a state u, it is reachable via a path of length at most d); Definition 22 (recurrence diameter: the least d such that every sequence of states s0, ..., s_{d+1} along transitions has s_{d+1} = s_j for some j <= d); Theorem 18 (for ECTL, a bound equal to the number of states suffices), Theorems 20 and 23 (the diameter suffices for EF p, the recurrence diameter for ECTL). These diameters range over all start states, so they are never smaller than the initialized notions used here.
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
  - D. Ishii, S. Fujii, 'Formalizing the Soundness of the Encoding Methods of SAT-based Model Checking', TASE 2020, pp. 105-112, doi:10.1109/TASE49443.2020.00023 (arXiv:2006.13613; Coq development at https://github.com/dsksh/coq-smc). Earlier mechanization, in Coq, of the soundness of BMC and k-induction encodings (its k-induction step uses plain paths), of Sheeran et al.'s loop-free forward and backward encodings, of a reduction of safety to loop-free paths (its Lemma 1), and of a simplified PDR. The paper states that completeness is not formalized.
- **Design question:** Why are simple-path bounds (reachability recurrence diameters) valid completeness thresholds? Because every reachable state is reachable along a simple path.
- **Non-claims:** see Boundaries, result 3.
- Basis: execution (Lean kernel check) — `Toy.KInd.exists_simple_reachIn` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — simple-path (recurrence-diameter) bounds are valid completeness thresholds for any model whose executions are sequences of states related by a transition relation, because shortest witnesses can always be taken loop-free.

### 4. `depth-monotonicity`

- **Kind:** theorem. **Tier:** T0. Folklore property of k-induction (success persists at larger depths), made explicit for both the plain and the simple-path step.
- **Depth:** `shallow`.
- **Plain claim:** For every transition system and depths k <= k': if Base k and Step k hold then Base k' and Step k' hold; Step k alone implies Step k'; and SimpleStep k alone implies SimpleStep k'.
- **Lean statement** (`Toy.KInd.kind_success_mono`, `Toy.KInd.Step.mono`, `Toy.KInd.SimpleStep.mono`):

  ```lean
  -- lean/KInd/Separation.lean:56
  theorem kind_success_mono {k k' : Nat} (hb : Base I T P k) (hs : Step T P k) (hk : k ≤ k') :
      Base I T P k' ∧ Step T P k'

  -- lean/KInd/Separation.lean:33
  theorem Step.mono {k k' : Nat} (h : Step T P k) (hk : k ≤ k') : Step T P k'

  -- lean/KInd/Separation.lean:48
  theorem SimpleStep.mono {k k' : Nat} (h : SimpleStep T P k) (hk : k ≤ k') :
      SimpleStep T P k'
  ```

  With the key definitions unfolded:

  ```text
  Base I T P k → Step T P k → k ≤ k' → Base I T P k' ∧ Step T P k';   Step T P k → k ≤ k' → Step T P k';   SimpleStep T P k → k ≤ k' → SimpleStep T P k'
  ```

- **Hypothesis ledger:**
  - `hb : Base I T P k (kind_success_mono)` (tight: counterexample `Toy.KInd.kind_success_mono_needs_base`). Needed for Base k' (soundness turns Base k ∧ Step k into invariance, which gives every base check).
  - `hs : Step T P k (kind_success_mono)` (tight: counterexample `Toy.KInd.kind_success_mono_needs_step`, `Toy.KInd.kind_success_mono_needs_step_invariant`). Needed for each conjunct separately: without it Base k' can fail (OneEdge), and even for an invariant P, Step k' can fail (SelfLoop).
  - `hk : k ≤ k' (kind_success_mono)` (tight: counterexample `Toy.KInd.kind_success_mono_needs_le`). Monotonicity is upward only.
  - `h : Step T P k (Step.mono)` (tight: counterexample `Toy.KInd.step_mono_needs_step`). The step must hold at the smaller depth.
  - `hk : k ≤ k' (Step.mono)` (tight: counterexample `Toy.KInd.step_mono_needs_le`). Step is not antitone: TwoInd passes Step 2 but not Step 1.
  - `h : SimpleStep T P k (SimpleStep.mono)` (tight: counterexample `Toy.KInd.simpleStep_mono_needs_step`). The simple-path step must hold at the smaller depth.
  - `hk : k ≤ k' (SimpleStep.mono)` (tight: counterexample `Toy.KInd.simpleStep_mono_needs_le`). SimpleStep is not antitone: SelfLoop passes SimpleStep 2 but not SimpleStep 1.
- **Non-vacuity witness:** TwoInd with k = 2, k' = 3 (Base 2, Step 2); SelfLoop with k = 2, k' = 3 for SimpleStep (where Step 2 fails). Lean: `Toy.KInd.nonvacuity_kind_success_mono`, `Toy.KInd.nonvacuity_step_mono`, `Toy.KInd.nonvacuity_simpleStep_mono`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. Definition II.2 (k-induction: the base checks paths from initial states of each length l < k, the step assumes k consecutive P-states; the same depth convention as Base k and Step k here). Footnote 3 (Section II): 'If P is k-inductive then P ∧ ◦P ∧ ◦◦P ∧ ... ∧ ◦◦···◦P [k-1 operators] is inductive, where ◦ stands for "next state"'; reading ◦ as 'in every successor state', this conjunction is FutureSafe T P (k-1). The footnote has no proof and concerns plain (not simple-path) k-induction. Lemma III.1: there are N-inductive properties whose shortest inductive strengthening has size larger than N; Lemma III.2: there is a property that is k-inductive for some k > 1 but has no inductive strengthening (its example lives in the quantifier-free fragment of a theory of arrays).
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
- **Design question:** Can a k-induction loop that increases k skip depths or restart? Yes: success at depth k persists at all larger depths, for the plain and for the simple-path step.
- **Non-claims:** see Boundaries, result 4.
- Basis: execution (Lean kernel check) — `Toy.KInd.kind_success_mono`, `Toy.KInd.Step.mono`, `Toy.KInd.SimpleStep.mono` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — an engine that increases k after a failed attempt never loses a proof available at a smaller depth, because each check at k' is implied by the check at k <= k'; this presumes a base that covers every length below the depth, as here, and does not cover relative or frame-based variants.

### 5. `one-induction-fails-two-induction-succeeds`

- **Kind:** counterexample. **Tier:** T0. The standard motivating example for k-induction (an unreachable predecessor of a bad state), checked by decide. Reference point: it is the case k = 1 of fixed-depth-kind-incomplete (TwoInd is Ladder 1), kept as the smallest instance.
- **Depth:** `definitional`.
- **Plain claim:** In the system TwoInd (states Fin 3; initial state 0 with a self-loop; an unreachable transition 1 -> 2; P excludes 2), P is invariant and passes Base 2 and Step 2, but is not preserved by one transition (Step 1 fails).
- **Lean statement** (`Toy.KInd.one_induction_fails_two_induction_succeeds`):

  ```lean
  -- lean/KInd/Separation.lean:73
  theorem one_induction_fails_two_induction_succeeds :
      ¬ Step TwoInd.T TwoInd.P 1 ∧ Base TwoInd.I TwoInd.T TwoInd.P 2 ∧
        Step TwoInd.T TwoInd.P 2 ∧ Invariant TwoInd.I TwoInd.T TwoInd.P
  ```

  With the key definitions unfolded:

  ```text
  ¬ Step TwoInd.T TwoInd.P 1 ∧ Base TwoInd.I TwoInd.T TwoInd.P 2 ∧ Step TwoInd.T TwoInd.P 2 ∧ Invariant TwoInd.I TwoInd.T TwoInd.P
  ```

- **Hypothesis ledger:** no hypotheses (a closed statement about concrete systems).
- **Non-vacuity witness:** The statement is itself a concrete instance. Lean: `Toy.KInd.one_induction_fails_two_induction_succeeds`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. Definition II.2 (k-induction: the base checks paths from initial states of each length l < k, the step assumes k consecutive P-states; the same depth convention as Base k and Step k here). Footnote 3 (Section II): 'If P is k-inductive then P ∧ ◦P ∧ ◦◦P ∧ ... ∧ ◦◦···◦P [k-1 operators] is inductive, where ◦ stands for "next state"'; reading ◦ as 'in every successor state', this conjunction is FutureSafe T P (k-1). The footnote has no proof and concerns plain (not simple-path) k-induction. Lemma III.1: there are N-inductive properties whose shortest inductive strengthening has size larger than N; Lemma III.2: there is a property that is k-inductive for some k > 1 but has no inductive strengthening (its example lives in the quantifier-free fragment of a theory of arrays).
- **Design question:** Reference point: what does k-induction buy over 1-induction? Here the bad state's only P-predecessor (state 1) has no predecessor, so any path of two transitions into the bad state already violates the step's assumption.
- **Non-claims:** see Boundaries, result 5.
- Basis: execution (Lean kernel check) — `Toy.KInd.one_induction_fails_two_induction_succeeds` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — reference point only; it explains why engines try depths above 1 and makes no further claim about real systems.

### 6. `fixed-depth-kind-incomplete`

- **Kind:** impossibility. **Tier:** T0. Incompleteness of induction at a fixed depth (Sheeran et al. 2000; Gurfinkel and Ivrii 2017), made precise with an explicit family that defeats the plain and the simple-path step.
- **Depth:** `shallow`.
- **Plain claim:** For every k there is a finite system, Ladder k (states Fin (k+2); initial state 0 with a self-loop; an unreachable chain 1 -> 2 -> ... -> k+1; P excludes k+1), whose property P is invariant and passes Base (k+1) and Step (k+1), while the step fails at every depth j <= k even when restricted to simple paths (SimpleStep j fails, hence Step j fails).
- **Lean statement** (`Toy.KInd.ladder_needs_depth_succ`):

  ```lean
  -- lean/KInd/Separation.lean:125
  theorem ladder_needs_depth_succ (k : Nat) :
      Invariant (Ladder.I k) (Ladder.T k) (Ladder.P k) ∧
        Base (Ladder.I k) (Ladder.T k) (Ladder.P k) (k + 1) ∧
        Step (Ladder.T k) (Ladder.P k) (k + 1) ∧
        ∀ j, j ≤ k → ¬ SimpleStep (Ladder.T k) (Ladder.P k) j
  ```

  With the key definitions unfolded:

  ```text
  ∀ k, Invariant (Ladder.I k) (Ladder.T k) (Ladder.P k) ∧ Base … (k+1) ∧ Step … (k+1) ∧ ∀ j ≤ k, ¬ SimpleStep (Ladder.T k) (Ladder.P k) j
  ```

- **Hypothesis ledger:** no hypotheses (a closed statement about concrete systems).
- **Non-vacuity witness:** The statement is a parametric family of concrete systems. Lean: `Toy.KInd.ladder_needs_depth_succ`.
- **Positive controls** (nearby settings where the impossibility disappears): `Toy.KInd.ladder_kind_succeeds_at_depth_succ`, `Toy.KInd.ladder_inductive_strengthening`, `Toy.KInd.ladder_reachDiameterBound_zero_bmc_zero`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - A. Gurfinkel, A. Ivrii, 'K-Induction without Unrolling', FMCAD 2017, pp. 148-155, doi:10.23919/FMCAD.2017.8102253. Defines k-invariants (eq. 4: all states reachable in at most k steps satisfy the formula) and k-inductive invariants (eq. 5: the step assumes k+1 consecutive states, i.e. depth k+1 here). States that neither induction nor k-induction is complete and that k-induction restricted to loop-free paths is complete (citing Sheeran et al.). Its Lemma 2: if the K-Ind procedure returns BLOCKED, the returned G is an inductive strengthening of the clause relative to a 0-invariant F0; its Theorem 1, under the stated assumption that Generalize(¬s) always returns ¬s, characterizes when K-Ind returns BLOCKED (the clause is k-inductive relative to F0).
  - D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. Definition II.2 (k-induction: the base checks paths from initial states of each length l < k, the step assumes k consecutive P-states; the same depth convention as Base k and Step k here). Footnote 3 (Section II): 'If P is k-inductive then P ∧ ◦P ∧ ◦◦P ∧ ... ∧ ◦◦···◦P [k-1 operators] is inductive, where ◦ stands for "next state"'; reading ◦ as 'in every successor state', this conjunction is FutureSafe T P (k-1). The footnote has no proof and concerns plain (not simple-path) k-induction. Lemma III.1: there are N-inductive properties whose shortest inductive strengthening has size larger than N; Lemma III.2: there is a property that is k-inductive for some k > 1 but has no inductive strengthening (its example lives in the quantifier-free fragment of a theory of arrays).
- **Design question:** Is any fixed depth k enough for k-induction, plain or simple-path? No: for every k some finite system needs depth k+1.
- **Non-claims:** see Boundaries, result 6.
- Basis: execution (Lean kernel check) — `Toy.KInd.ladder_needs_depth_succ` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — a tool that fixes its induction depth in advance, with or without distinctness constraints, is incomplete on some finite models, because Ladder k is finite and defeats every depth up to k; completeness needs a depth that grows with the model or a strengthening.

### 7. `plain-kind-incomplete-every-depth`

- **Kind:** impossibility. **Tier:** T0. Sheeran et al. 2000 state that induction with depth without the loop-free restriction is incomplete; this is an explicit finite witness.
- **Depth:** `shallow`.
- **Plain claim:** In the finite system SelfLoop (states Fin 3; initial state 0 with a self-loop; an unreachable state 1 with a self-loop and an edge 1 -> 2; P excludes 2), P is invariant but plain Step k fails for every k, so plain k-induction cannot prove it at any depth.
- **Lean statement** (`Toy.KInd.plain_kind_incomplete_every_depth`):

  ```lean
  -- lean/KInd/Completeness.lean:197
  theorem plain_kind_incomplete_every_depth :
      Invariant SelfLoop.I SelfLoop.T SelfLoop.P ∧ ∀ k, ¬ Step SelfLoop.T SelfLoop.P k
  ```

  With the key definitions unfolded:

  ```text
  Invariant SelfLoop.I SelfLoop.T SelfLoop.P ∧ ∀ k, ¬ Step SelfLoop.T SelfLoop.P k
  ```

- **Hypothesis ledger:** no hypotheses (a closed statement about concrete systems).
- **Non-vacuity witness:** The statement is itself a concrete instance. Lean: `Toy.KInd.plain_kind_incomplete_every_depth`.
- **Positive controls** (nearby settings where the impossibility disappears): `Toy.KInd.selfLoop_simple_kind_succeeds_at_two`, `Toy.KInd.step_zero_of_invariant_of_all_reachable`, `Toy.KInd.step_card_of_acyclic`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - A. Gurfinkel, A. Ivrii, 'K-Induction without Unrolling', FMCAD 2017, pp. 148-155, doi:10.23919/FMCAD.2017.8102253. Defines k-invariants (eq. 4: all states reachable in at most k steps satisfy the formula) and k-inductive invariants (eq. 5: the step assumes k+1 consecutive states, i.e. depth k+1 here). States that neither induction nor k-induction is complete and that k-induction restricted to loop-free paths is complete (citing Sheeran et al.). Its Lemma 2: if the K-Ind procedure returns BLOCKED, the returned G is an inductive strengthening of the clause relative to a 0-invariant F0; its Theorem 1, under the stated assumption that Generalize(¬s) always returns ¬s, characterizes when K-Ind returns BLOCKED (the clause is k-inductive relative to F0).
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
- **Design question:** Why do k-induction engines add all-different (simple-path) constraints? Without them, a cycle through unreachable P-states that can reach a bad state defeats every depth.
- **Non-claims:** see Boundaries, result 7.
- Basis: execution (Lean kernel check) — `Toy.KInd.plain_kind_incomplete_every_depth` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — a plain k-induction engine without distinctness constraints or strengthening can fail at every depth on a finite model that has an unreachable cycle of P-states from which a bad state is reachable, because SelfLoop is such a model.

### 8. `simple-step-vacuous-at-card`

- **Kind:** theorem. **Tier:** T0. Pigeonhole: a simple path in an n-state system has at most n-1 transitions.
- **Depth:** `shallow`.
- **Plain claim:** In every system with n states (state type Fin n), for every transition relation T, every property P and every depth k >= n, the simple-path step SimpleStep T P k holds, because no simple path has k transitions.
- **Lean statement** (`Toy.KInd.simpleStep_of_card_le`):

  ```lean
  -- lean/KInd/Completeness.lean:25
  theorem simpleStep_of_card_le {n k : Nat} (T : Fin n → Fin n → Prop) (P : Fin n → Prop)
      (hk : n ≤ k) : SimpleStep T P k
  ```

  With the key definitions unfolded:

  ```text
  n ≤ k → ∀ π : Nat → Fin n, IsPath T k π → IsSimple k π → (∀ i < k, P (π i)) → P (π k)
  ```

- **Hypothesis ledger:**
  - `hk : n ≤ k` (tight: counterexample `Toy.KInd.simple_kind_depth_card_optimal_without_init`). Depth at least the number of states makes simple paths of that length impossible.
  - `state type Fin n (parameter)` (tight: counterexample `Toy.KInd.simple_kind_incomplete_every_depth_infinite`). Finiteness gives the pigeonhole bound; the counterexample is the infinite analogue (no finite n exists for state type Nat).
- **Non-vacuity witness:** SelfLoop with n = k = 3. Lean: `Toy.KInd.nonvacuity_simpleStep_of_card_le`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
- **Design question:** Why is simple-path k-induction complete for finite systems, and what does that completeness cost? At depth n the step is vacuous, so completeness reduces to exhaustive bounded checking.
- **Non-claims:** see Boundaries, result 8.
- Basis: execution (Lean kernel check) — `Toy.KInd.simpleStep_of_card_le` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — on a finite model with n full states, simple-path k-induction succeeds by depth n at the latest, but at that depth the step check is trivially satisfied and the remaining work is BMC to depth n-1; for bit-level models n is the size of the full state space, so this is a termination argument, not a cost estimate.

### 9. `simple-kind-complete-fin`

- **Kind:** theorem. **Tier:** T0. Completeness of strengthened induction with depth for finite systems (Sheeran et al. 2000; Eén and Sörensson 2003), restated at depth n.
- **Depth:** `shallow`.
- **Plain claim:** For every system whose state type is finite with n states (Fin n) and every property P that holds in all reachable states, Base n and SimpleStep n both hold: k-induction with the simple-path constraint succeeds at depth n.
- **Lean statement** (`Toy.KInd.simple_kind_complete_fin`):

  ```lean
  -- lean/KInd/Completeness.lean:32
  theorem simple_kind_complete_fin {n : Nat} {I : Fin n → Prop} {T : Fin n → Fin n → Prop}
      {P : Fin n → Prop} (h : Invariant I T P) : Base I T P n ∧ SimpleStep T P n
  ```

  With the key definitions unfolded:

  ```text
  Invariant I T P → Base I T P n ∧ SimpleStep T P n   (I T P over Fin n)
  ```

- **Hypothesis ledger:**
  - `h : Invariant I T P` (tight: counterexample `Toy.KInd.simple_kind_complete_fin_needs_invariant`). Completeness only for true invariants (soundness gives the converse).
  - `state type Fin n (parameter)` (tight: counterexample `Toy.KInd.simple_kind_incomplete_every_depth_infinite`). The whole state type must be finite, not just the reachable part; the counterexample is the infinite analogue, with one reachable state.
  - `depth k = n, not n-1 (parameter)` (tight: counterexample `Toy.KInd.simple_kind_depth_card_optimal_without_init`). Without initial states depth n-1 can fail; with an initial state see simple-kind-complete-fin-pred-of-init.
- **Non-vacuity witness:** SelfLoop (an invariant on which plain k-induction fails at every depth). Lean: `Toy.KInd.nonvacuity_simple_kind_complete_fin`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
  - A. Gurfinkel, A. Ivrii, 'K-Induction without Unrolling', FMCAD 2017, pp. 148-155, doi:10.23919/FMCAD.2017.8102253. Defines k-invariants (eq. 4: all states reachable in at most k steps satisfy the formula) and k-inductive invariants (eq. 5: the step assumes k+1 consecutive states, i.e. depth k+1 here). States that neither induction nor k-induction is complete and that k-induction restricted to loop-free paths is complete (citing Sheeran et al.). Its Lemma 2: if the K-Ind procedure returns BLOCKED, the returned G is an inductive strengthening of the clause relative to a 0-invariant F0; its Theorem 1, under the stated assumption that Generalize(¬s) always returns ¬s, characterizes when K-Ind returns BLOCKED (the clause is k-inductive relative to F0).
- **Design question:** Which constraint makes k-induction complete for finite systems? The simple-path constraint; with it, depth n always suffices when the state type has n elements.
- **Non-claims:** see Boundaries, result 9.
- Basis: execution (Lean kernel check) — `Toy.KInd.simple_kind_complete_fin` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — a simple-path k-induction engine that increases k without bound proves every true safety property of a finite model by depth n, where n counts the full state space of the model, because the theorem quantifies over every system on Fin n.

### 10. `simple-kind-complete-fin-pred-of-init`

- **Kind:** theorem. **Tier:** T1. An easy sharpening of finite-state completeness, closely related to the loop-free termination check of Sheeran et al. 2000; the n-1 bound with matching optimality families was not found stated in the sources checked. Not claimed novel.
- **Depth:** `shallow`.
- **Plain claim:** For every system whose state type is finite with m+1 states (Fin (m+1)) and that has at least one initial state, and every property P holding in all reachable states, Base m and SimpleStep m both hold: depth n-1 suffices when an initial state exists.
- **Lean statement** (`Toy.KInd.simple_kind_complete_fin_pred_of_init`):

  ```lean
  -- lean/KInd/Completeness.lean:40
  theorem simple_kind_complete_fin_pred_of_init {m : Nat} {I : Fin (m + 1) → Prop}
      {T : Fin (m + 1) → Fin (m + 1) → Prop} {P : Fin (m + 1) → Prop} (hI : ∃ s, I s)
      (h : Invariant I T P) : Base I T P m ∧ SimpleStep T P m
  ```

  With the key definitions unfolded:

  ```text
  (∃ s, I s) → Invariant I T P → Base I T P m ∧ SimpleStep T P m   (I T P over Fin (m+1))
  ```

- **Hypothesis ledger:**
  - `hI : ∃ s, I s` (tight: counterexample `Toy.KInd.simple_kind_depth_card_optimal_without_init`). A simple path with m transitions visits every state, hence an initial one, so its end is reachable.
  - `h : Invariant I T P` (tight: counterexample `Toy.KInd.simple_kind_complete_fin_pred_of_init_needs_invariant`). Completeness only for true invariants.
  - `state type Fin (m+1) (parameter)` (tight: counterexample `Toy.KInd.simple_kind_incomplete_every_depth_infinite`). The whole state type must be finite; the counterexample is the infinite analogue and has an initial state.
  - `depth m = n-1, not n-2 (parameter, n >= 2)` (tight: counterexample `Toy.KInd.simple_kind_depth_pred_optimal_with_init`). Optimal: with an isolated initial state, depth n-2 can fail; the counterexample family has n = m+2 >= 2 states.
- **Non-vacuity witness:** SelfLoop (Fin (2+1), initial state 0). Lean: `Toy.KInd.nonvacuity_simple_kind_complete_fin`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
- **Design question:** What is the worst-case depth for simple-path k-induction on n-state systems? n-1 if some initial state exists, n otherwise; both bounds are attained.
- **Non-claims:** see Boundaries, result 10.
- Basis: execution (Lean kernel check) — `Toy.KInd.simple_kind_complete_fin_pred_of_init` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — the same as for simple-kind-complete-fin, with depth n-1 when the model has an initial state; n counts the full state space, so this is a worst-case termination bound.

### 11. `simple-kind-incomplete-infinite`

- **Kind:** impossibility. **Tier:** T0. Simple-path k-induction is complete only for finite state spaces (Sheeran et al. 2000; Eén and Sörensson 2003 attribute completeness to finiteness); this is an explicit infinite witness with a single reachable state.
- **Depth:** `shallow`.
- **Plain claim:** In the infinite system NatDescent (states Nat; initial state 0 with a self-loop; unreachable transitions s -> s-1 for every s >= 2; P excludes 1), there is an initial state, exactly one state (0) is reachable, 0 bounds both the reachability diameter and the reachability recurrence diameter, P is invariant and passes Base k for every k, yet SimpleStep k fails for every k: simple-path k-induction never proves this invariant.
- **Lean statement** (`Toy.KInd.simple_kind_incomplete_every_depth_infinite`):

  ```lean
  -- lean/KInd/Completeness.lean:146
  theorem simple_kind_incomplete_every_depth_infinite :
      (∃ s, NatDescent.I s) ∧
        (∀ s, Reachable NatDescent.I NatDescent.T s ↔ s = 0) ∧
        ReachDiameterBound NatDescent.I NatDescent.T 0 ∧
        ReachRecurrenceBound NatDescent.I NatDescent.T 0 ∧
        Invariant NatDescent.I NatDescent.T NatDescent.P ∧
        ∀ k, Base NatDescent.I NatDescent.T NatDescent.P k ∧
          ¬ SimpleStep NatDescent.T NatDescent.P k
  ```

  With the key definitions unfolded:

  ```text
  (∃ s, NatDescent.I s) ∧ (∀ s, Reachable NatDescent.I NatDescent.T s ↔ s = 0) ∧ ReachDiameterBound … 0 ∧ ReachRecurrenceBound … 0 ∧ Invariant NatDescent.I NatDescent.T NatDescent.P ∧ ∀ k, Base NatDescent.I NatDescent.T NatDescent.P k ∧ ¬ SimpleStep NatDescent.T NatDescent.P k
  ```

- **Hypothesis ledger:** no hypotheses (a closed statement about concrete systems).
- **Non-vacuity witness:** The statement is itself a concrete instance. Lean: `Toy.KInd.simple_kind_incomplete_every_depth_infinite`.
- **Positive controls** (nearby settings where the impossibility disappears): `Toy.KInd.selfLoop_simple_kind_succeeds_at_two`, `Toy.KInd.natDescent_bmc_zero_proves_invariant`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
  - L. de Moura, H. Rueß, M. Sorea, 'Bounded Model Checking and Induction: From Refutation to Verification', CAV 2003, LNCS 2725, pp. 14-26, doi:10.1007/978-3-540-45069-6_2. k-induction with decision procedures for infinite-state systems (per its abstract); bibliographic data verified on dblp, full text not consulted here.
- **Design question:** When verifying a program whose state type is infinite but whose reachable states are few, can one rely on simple-path k-induction terminating? No: unreachable infinite simple paths can defeat every depth; use a strengthening or a reachability-diameter argument instead.
- **Non-claims:** see Boundaries, result 11.
- Basis: execution (Lean kernel check) — `Toy.KInd.simple_kind_incomplete_every_depth_infinite` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — for infinite-state models (for example software with unbounded integers), simple-path k-induction without strengthening has no guaranteed depth even when only finitely many states are reachable, because NatDescent is such a model; such tools need invariant strengthening or another argument.

### 12. `bmc-complete-of-diameter-bound`

- **Kind:** theorem. **Tier:** T0. The reachability diameter is a completeness threshold of BMC for invariants (Kroening and Strichman 2003; with the uninitialized diameter, Biere et al. 1999).
- **Depth:** `definitional`.
- **Plain claim:** For every transition system, if every reachable state is reachable from an initial state within d transitions (d bounds the reachability diameter, the initialized notion), d <= k, and BMC to depth k finds no path from an initial state with at most k transitions ending outside P, then every reachable state satisfies P.
- **Lean statement** (`Toy.KInd.bmc_complete_of_reachDiameterBound`):

  ```lean
  -- lean/KInd/BMC.lean:74
  theorem bmc_complete_of_reachDiameterBound {d k : Nat} (hd : ReachDiameterBound I T d)
      (hk : d ≤ k) (hb : BMC I T P k) : Invariant I T P
  ```

  With the key definitions unfolded:

  ```text
  (∀ s, Reachable I T s → ∃ j ≤ d, ReachIn I T j s) → d ≤ k → (∀ j ≤ k, ∀ s, ReachIn I T j s → P s) → Invariant I T P
  ```

- **Hypothesis ledger:**
  - `hd : ReachDiameterBound I T d` (tight: counterexample `Toy.KInd.bmc_reachDiameter_needs_hd`). Every reachable state appears within the explored depth.
  - `hk : d ≤ k` (tight: counterexample `Toy.KInd.bmc_reachDiameter_needs_hk`). The BMC depth must reach the bound. (d and hk together are equivalent to ReachDiameterBound I T k, by ReachDiameterBound.mono; the statement with d = k loses nothing.)
  - `hb : BMC I T P k` (tight: counterexample `Toy.KInd.bmc_reachDiameter_needs_hb`). No counterexample of length at most k.
- **Non-vacuity witness:** Triangle with d = 1, k = 2 and P := True; also SelfLoop with d = k = 0 and its non-trivial P (selfLoop_reachDiameterBound_zero_bmc_zero). Lean: `Toy.KInd.nonvacuity_bmc_complete_of_reachDiameterBound`, `Toy.KInd.selfLoop_reachDiameterBound_zero_bmc_zero`.
- **Prior art:**
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
  - A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. Statement numbers follow the technical-report version (CMU-CS-99-101) and may differ in the published version. Definition 19 (diameter: the least d such that whenever a state v is reachable from a state u, it is reachable via a path of length at most d); Definition 22 (recurrence diameter: the least d such that every sequence of states s0, ..., s_{d+1} along transitions has s_{d+1} = s_j for some j <= d); Theorem 18 (for ECTL, a bound equal to the number of states suffices), Theorems 20 and 23 (the diameter suffices for EF p, the recurrence diameter for ECTL). These diameters range over all start states, so they are never smaller than the initialized notions used here.
  - A. Biere, A. Cimatti, E. M. Clarke, O. Strichman, Y. Zhu, 'Bounded Model Checking', Advances in Computers 58, pp. 117-148, 2003, doi:10.1016/S0065-2458(03)58003-2. Survey of bounded model checking; bibliographic data verified on dblp, text not consulted here (cited as a general reference).
  - A. Biere, 'Bounded Model Checking', in Handbook of Satisfiability, 2nd ed., FAIA 336, pp. 739-764, IOS Press, 2021, doi:10.3233/FAIA201002 (1st ed. 2009, FAIA 185, pp. 457-481, doi:10.3233/978-1-58603-929-5-457). Handbook chapter on bounded model checking; bibliographic data verified on dblp, text not consulted here (cited as a general reference).
  - F. Kurz, M. Abdulaziz, 'Upper Bounding Diameters of State Spaces of Factored Transition Systems', Archive of Formal Proofs, October 12, 2018, https://www.isa-afp.org/entries/Factored_Transition_System_Bounding.html. Isabelle/HOL development (ported from HOL4) treating the diameter as a completeness threshold for bounded model checking of safety properties and for planning, with compositional upper bounds for factored systems. Its diameter is the uninitialized one (shortest paths between all pairs of states), not the reachability diameter used here.
- **Design question:** What does 'BMC found no counterexample up to depth k' establish? Safety of the invariant whenever k bounds the reachability diameter.
- **Non-claims:** see Boundaries, result 12.
- Basis: execution (Lean kernel check) — `Toy.KInd.bmc_complete_of_reachDiameterBound` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — a BMC run to depth k proves a safety property of any model whose reachability diameter is at most k, because the theorem holds for every system; obtaining a sound bound on the diameter is the hard part and is outside this package.

### 13. `recurrence-bound-is-diameter-bound`

- **Kind:** theorem. **Tier:** T0. The (reachability) recurrence diameter over-approximates the (reachability) diameter as a BMC threshold (Biere et al. 1999; Kroening and Strichman 2003).
- **Depth:** `shallow`.
- **Plain claim:** For every transition system, if every simple path from an initial state has at most r transitions (r bounds the reachability recurrence diameter), then every reachable state is reachable from an initial state within r transitions; hence BMC to any depth k >= r implies that every reachable state satisfies P.
- **Lean statement** (`Toy.KInd.bmc_complete_of_reachRecurrenceBound`, `Toy.KInd.reachDiameterBound_of_reachRecurrenceBound`):

  ```lean
  -- lean/KInd/BMC.lean:92
  theorem bmc_complete_of_reachRecurrenceBound {r k : Nat} (hr : ReachRecurrenceBound I T r)
      (hk : r ≤ k) (hb : BMC I T P k) : Invariant I T P

  -- lean/KInd/BMC.lean:83
  theorem reachDiameterBound_of_reachRecurrenceBound {r : Nat} (hr : ReachRecurrenceBound I T r) :
      ReachDiameterBound I T r
  ```

  With the key definitions unfolded:

  ```text
  (∀ j π, I (π 0) → IsPath T j π → IsSimple j π → j ≤ r) → r ≤ k → BMC I T P k → Invariant I T P;   ReachRecurrenceBound I T r → ReachDiameterBound I T r
  ```

- **Hypothesis ledger:**
  - `hr : ReachRecurrenceBound I T r (both theorems)` (tight: counterexample `Toy.KInd.bmc_reachRecurrence_needs_hr`, `Toy.KInd.reachDiameterBound_of_reachRecurrenceBound_needs_hr`). Bounds simple paths from initial states.
  - `hk : r ≤ k (bmc_complete_of_reachRecurrenceBound)` (tight: counterexample `Toy.KInd.bmc_reachRecurrence_needs_hk`). Depth must reach the bound.
  - `hb : BMC I T P k (bmc_complete_of_reachRecurrenceBound)` (tight: counterexample `Toy.KInd.bmc_reachRecurrence_needs_hb`). No counterexample up to depth k.
- **Non-vacuity witness:** Triangle with r = 2, k = 3 and P := True (also witnesses reachDiameterBound_of_reachRecurrenceBound with r = 2). Lean: `Toy.KInd.nonvacuity_bmc_complete_of_reachRecurrenceBound`.
- **Prior art:**
  - A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. Statement numbers follow the technical-report version (CMU-CS-99-101) and may differ in the published version. Definition 19 (diameter: the least d such that whenever a state v is reachable from a state u, it is reachable via a path of length at most d); Definition 22 (recurrence diameter: the least d such that every sequence of states s0, ..., s_{d+1} along transitions has s_{d+1} = s_j for some j <= d); Theorem 18 (for ECTL, a bound equal to the number of states suffices), Theorems 20 and 23 (the diameter suffices for EF p, the recurrence diameter for ECTL). These diameters range over all start states, so they are never smaller than the initialized notions used here.
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
  - D. Ishii, S. Fujii, 'Formalizing the Soundness of the Encoding Methods of SAT-based Model Checking', TASE 2020, pp. 105-112, doi:10.1109/TASE49443.2020.00023 (arXiv:2006.13613; Coq development at https://github.com/dsksh/coq-smc). Earlier mechanization, in Coq, of the soundness of BMC and k-induction encodings (its k-induction step uses plain paths), of Sheeran et al.'s loop-free forward and backward encodings, of a reduction of safety to loop-free paths (its Lemma 1), and of a simplified PDR. The paper states that completeness is not formalized.
- **Design question:** Can a BMC engine use the (propositionally checkable) reachability recurrence diameter as its threshold for invariants? Yes, soundly, at the price of possibly exploring deeper than needed.
- **Non-claims:** see Boundaries, result 13.
- Basis: execution (Lean kernel check) — `Toy.KInd.bmc_complete_of_reachRecurrenceBound`, `Toy.KInd.reachDiameterBound_of_reachRecurrenceBound` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — bounding the longest simple path from initial states, a check expressible with distinctness constraints, is a sound way to obtain a BMC completeness threshold for safety, because such a bound bounds the reachability diameter for every system.

### 14. `reach-diameter-le-reach-recurrence-bound`

- **Kind:** theorem. **Tier:** T0. Kroening and Strichman 2003 note that rrd(M) over-approximates rd(M); restated with any reachability recurrence bound in place of the least one.
- **Depth:** `shallow`.
- **Plain claim:** For every transition system, if d is the reachability diameter and every simple path from an initial state has at most r transitions, then d <= r. In particular the reachability diameter is at most the reachability recurrence diameter whenever both exist.
- **Lean statement** (`Toy.KInd.isReachDiameter_le_of_reachRecurrenceBound`):

  ```lean
  -- lean/KInd/BMC.lean:106
  theorem isReachDiameter_le_of_reachRecurrenceBound {d r : Nat} (hd : IsReachDiameter I T d)
      (hr : ReachRecurrenceBound I T r) : d ≤ r
  ```

  With the key definitions unfolded:

  ```text
  (ReachDiameterBound I T d ∧ ∀ d', ReachDiameterBound I T d' → d ≤ d') → (∀ j π, I (π 0) → IsPath T j π → IsSimple j π → j ≤ r) → d ≤ r
  ```

- **Hypothesis ledger:**
  - `hd : IsReachDiameter I T d` (tight: counterexample `Toy.KInd.isReachDiameter_le_needs_hd`). d must be the least reachability-diameter bound. Only the minimality half is used; the general form with just that half is le_of_reachDiameter_lower_bound_of_reachRecurrenceBound.
  - `hr : ReachRecurrenceBound I T r` (tight: counterexample `Toy.KInd.isReachDiameter_le_needs_hr`). r must bound simple paths from initial states (any such bound, not necessarily the least).
- **Non-vacuity witness:** Triangle: reachability diameter 1, reachability recurrence bound 2. Lean: `Toy.KInd.nonvacuity_isReachDiameter_le_of_reachRecurrenceBound`.
- **Prior art:**
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
  - A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. Statement numbers follow the technical-report version (CMU-CS-99-101) and may differ in the published version. Definition 19 (diameter: the least d such that whenever a state v is reachable from a state u, it is reachable via a path of length at most d); Definition 22 (recurrence diameter: the least d such that every sequence of states s0, ..., s_{d+1} along transitions has s_{d+1} = s_j for some j <= d); Theorem 18 (for ECTL, a bound equal to the number of states suffices), Theorems 20 and 23 (the diameter suffices for EF p, the recurrence diameter for ECTL). These diameters range over all start states, so they are never smaller than the initialized notions used here.
- **Design question:** Is the reachability diameter ever larger than a recurrence bound? No; the recurrence bound is always a safe (over-approximating) stand-in.
- **Non-claims:** see Boundaries, result 14.
- Basis: execution (Lean kernel check) — `Toy.KInd.isReachDiameter_le_of_reachRecurrenceBound` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — using a recurrence bound instead of the reachability diameter as a BMC threshold is never too small, because the inequality holds for every system; it can be much larger (diameter-below-recurrence-diameter).

### 15. `bmc-complete-fin`

- **Kind:** theorem. **Tier:** T0. Corollary: the reachability recurrence diameter of an n-state system is at most n-1 (cf. Biere et al. 1999, Theorem 18 in the report numbering, a bound by the number of states).
- **Depth:** `shallow`.
- **Plain claim:** For every system whose state type is finite with n states (Fin n), if no path from an initial state with at most n-1 transitions reaches a state outside P, then every reachable state satisfies P.
- **Lean statement** (`Toy.KInd.bmc_complete_fin`):

  ```lean
  -- lean/KInd/BMC.lean:148
  theorem bmc_complete_fin {n : Nat} {I : Fin n → Prop} {T : Fin n → Fin n → Prop}
      {P : Fin n → Prop} (hb : BMC I T P (n - 1)) : Invariant I T P
  ```

  With the key definitions unfolded:

  ```text
  BMC I T P (n - 1) → Invariant I T P   (I T P over Fin n; n - 1 is truncated subtraction, so n = 0 gives depth 0, where the claim holds vacuously)
  ```

- **Hypothesis ledger:**
  - `hb : BMC I T P (n - 1)` (tight: counterexample `Toy.KInd.bmc_complete_fin_depth_tight_all`, `Toy.KInd.bmc_complete_fin_depth_tight`). Exhaustive bounded check up to n-1 transitions; depth n-2 is not enough, for every n >= 2.
  - `state type Fin n (parameter)` (tight: counterexample `Toy.KInd.bmc_incomplete_every_depth_infinite`). Finiteness bounds simple paths; on the infinite counter NatSucc no BMC depth k is complete (the property s <= k passes BMC k and is not invariant). This is the infinite analogue; the finite statement cannot be instantiated there.
- **Non-vacuity witness:** SelfLoop (n = 3) passes BMC 2. Lean: `Toy.KInd.nonvacuity_bmc_complete_fin`.
- **Prior art:**
  - A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. Statement numbers follow the technical-report version (CMU-CS-99-101) and may differ in the published version. Definition 19 (diameter: the least d such that whenever a state v is reachable from a state u, it is reachable via a path of length at most d); Definition 22 (recurrence diameter: the least d such that every sequence of states s0, ..., s_{d+1} along transitions has s_{d+1} = s_j for some j <= d); Theorem 18 (for ECTL, a bound equal to the number of states suffices), Theorems 20 and 23 (the diameter suffices for EF p, the recurrence diameter for ECTL). These diameters range over all start states, so they are never smaller than the initialized notions used here.
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
- **Design question:** What is the trivial completeness threshold for BMC on finite systems? n-1 transitions, and no smaller depth works for all n-state systems.
- **Non-claims:** see Boundaries, result 15.
- Basis: execution (Lean kernel check) — `Toy.KInd.bmc_complete_fin` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — BMC to depth n-1 is a complete safety check for a model with n full states, because the theorem holds for every system on Fin n; for bit-level models n is usually far too large for this to be a practical threshold.

### 16. `bmc-threshold-characterization`

- **Kind:** characterization. **Tier:** T1. Kroening and Strichman 2003 state that the reachability diameter is the completeness threshold for Gp; this makes precise in which sense (the least depth that works uniformly for every state predicate) and exposes the witness property.
- **Depth:** `definitional`.
- **Plain claim:** For every transition system and depth k, BMC to depth k implies safety for every state predicate P if and only if every reachable state is reachable within k transitions (k bounds the reachability diameter); when k fails this, the property 'reachable within k transitions' passes BMC k but is not invariant.
- **Lean statement** (`Toy.KInd.bmc_complete_all_props_iff_reachDiameterBound`, `Toy.KInd.bmc_incomplete_of_not_reachDiameterBound`):

  ```lean
  -- lean/KInd/BMC.lean:140
  theorem bmc_complete_all_props_iff_reachDiameterBound {k : Nat} :
      (∀ P : σ → Prop, BMC I T P k → Invariant I T P) ↔ ReachDiameterBound I T k

  -- lean/KInd/BMC.lean:121
  theorem bmc_incomplete_of_not_reachDiameterBound {k : Nat} (h : ¬ ReachDiameterBound I T k) :
      BMC I T (ReachWithin I T k) k ∧ ¬ Invariant I T (ReachWithin I T k)
  ```

  With the key definitions unfolded:

  ```text
  (∀ P, BMC I T P k → Invariant I T P) ↔ ReachDiameterBound I T k;   ¬ ReachDiameterBound I T k → BMC I T (ReachWithin I T k) k ∧ ¬ Invariant I T (ReachWithin I T k)
  ```

- **Hypothesis ledger:**
  - `h : ¬ ReachDiameterBound I T k (bmc_incomplete_of_not_reachDiameterBound)` (tight: counterexample `Toy.KInd.bmc_incomplete_needs_not_reachDiameterBound`). Below a reachability-diameter bound some property fools BMC.
- **Non-vacuity witness:** Chain: k = 1 is below its reachability diameter 2 (¬ ReachDiameterBound 1); at k = 2 the iff's right side holds. Lean: `Toy.KInd.chain_not_reachDiameterBound_one`, `Toy.KInd.chain_reachDiameterBound_two`.
- **Positive controls** (nearby settings where the impossibility disappears): `Toy.KInd.chain_reachWithin_two_invariant`.
- **Prior art:**
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
  - A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. Statement numbers follow the technical-report version (CMU-CS-99-101) and may differ in the published version. Definition 19 (diameter: the least d such that whenever a state v is reachable from a state u, it is reachable via a path of length at most d); Definition 22 (recurrence diameter: the least d such that every sequence of states s0, ..., s_{d+1} along transitions has s_{d+1} = s_j for some j <= d); Theorem 18 (for ECTL, a bound equal to the number of states suffices), Theorems 20 and 23 (the diameter suffices for EF p, the recurrence diameter for ECTL). These diameters range over all start states, so they are never smaller than the initialized notions used here.
  - E. M. Clarke, D. Kroening, J. Ouaknine, O. Strichman, 'Completeness and Complexity of Bounded Model Checking', VMCAI 2004, LNCS 2937, pp. 85-96, doi:10.1007/978-3-540-24622-0_9. Per its abstract, computes an over-approximation of the completeness threshold for general LTL properties via Büchi automata and analyses the complexity of SAT-based BMC; only safety invariants are treated here.
  - A. Biere, 'Bounded Model Checking', in Handbook of Satisfiability, 2nd ed., FAIA 336, pp. 739-764, IOS Press, 2021, doi:10.3233/FAIA201002 (1st ed. 2009, FAIA 185, pp. 457-481, doi:10.3233/978-1-58603-929-5-457). Handbook chapter on bounded model checking; bibliographic data verified on dblp, text not consulted here (cited as a general reference).
- **Design question:** Is the reachability diameter the right property-independent BMC threshold for invariants? Yes, exactly: no smaller depth works for all state predicates.
- **Non-claims:** see Boundaries, result 16.
- Basis: execution (Lean kernel check) — `Toy.KInd.bmc_complete_all_props_iff_reachDiameterBound`, `Toy.KInd.bmc_incomplete_of_not_reachDiameterBound` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — for safety properties, a depth is a property-independent BMC completeness threshold exactly when it bounds the reachability diameter, because the characterization quantifies over all state predicates; property classes restricted in advance may have smaller thresholds, which this package does not treat.

### 17. `base-at-recurrence-diameter-off-by-one`

- **Kind:** counterexample. **Tier:** T0. Reference point: a concrete check of a depth convention, by decide. It records a pitfall (counting states instead of transitions at the threshold) rather than a new result.
- **Depth:** `definitional`.
- **Plain claim:** In OneEdge (states Fin 2; initial state 0; one transition 0 -> 1; P = {0}), the reachability recurrence diameter is 1 and Base 1 (paths with at most one state) holds, yet P is not invariant; BMC 1 (paths with at most one transition) correctly fails.
- **Lean statement** (`Toy.KInd.base_at_recurrence_diameter_unsound`):

  ```lean
  -- lean/KInd/BMC.lean:219
  theorem base_at_recurrence_diameter_unsound :
      IsReachRecurrenceDiameter OneEdge.I OneEdge.T 1 ∧ Base OneEdge.I OneEdge.T OneEdge.P 1 ∧
        ¬ Invariant OneEdge.I OneEdge.T OneEdge.P ∧ ¬ BMC OneEdge.I OneEdge.T OneEdge.P 1
  ```

  With the key definitions unfolded:

  ```text
  IsReachRecurrenceDiameter OneEdge.I OneEdge.T 1 ∧ Base OneEdge.I OneEdge.T OneEdge.P 1 ∧ ¬ Invariant … ∧ ¬ BMC OneEdge.I OneEdge.T OneEdge.P 1
  ```

- **Hypothesis ledger:** no hypotheses (a closed statement about concrete systems).
- **Non-vacuity witness:** The statement is itself a concrete instance. Lean: `Toy.KInd.base_at_recurrence_diameter_unsound`.
- **Prior art:**
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
- **Design question:** Reference point: which off-by-one is safe when wiring a completeness threshold into a BMC loop? Depth counts transitions; checking only paths of r states at threshold r is unsound.
- **Non-claims:** see Boundaries, result 17.
- Basis: execution (Lean kernel check) — `Toy.KInd.base_at_recurrence_diameter_unsound` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — reference point only: depth indices differ by one across tools and papers, and using the base check at the recurrence diameter instead of BMC to it is unsound.

### 18. `diameter-below-recurrence-diameter`

- **Kind:** counterexample. **Tier:** T0. Kroening and Strichman 2003 give a system with rd(M) < rrd(M); Biere et al. 1999 note that in a fully connected structure the diameter is 1 while the recurrence diameter equals the number of states (uninitialized notions, their counting). This is a parametric family for the initialized notions on transitive tournaments (complete DAGs).
- **Depth:** `shallow`.
- **Plain claim:** For every n >= 2 there is an n-state system, TriangleN m with n = m+2 (states Fin (m+2); initial state 0; transitions s -> t for every s < t), whose reachability diameter is 1 while its reachability recurrence diameter is n-1; so the gap can be n-2.
- **Lean statement** (`Toy.KInd.reachDiameter_lt_reachRecurrenceDiameter_family`):

  ```lean
  -- lean/KInd/BMC.lean:453
  theorem reachDiameter_lt_reachRecurrenceDiameter_family (m : Nat) :
      IsReachDiameter (TriangleN.I m) (TriangleN.T m) 1 ∧
        IsReachRecurrenceDiameter (TriangleN.I m) (TriangleN.T m) (m + 1)
  ```

  With the key definitions unfolded:

  ```text
  ∀ m, IsReachDiameter (TriangleN.I m) (TriangleN.T m) 1 ∧ IsReachRecurrenceDiameter (TriangleN.I m) (TriangleN.T m) (m + 1)
  ```

- **Hypothesis ledger:** no hypotheses (a closed statement about concrete systems).
- **Non-vacuity witness:** The statement is a parametric family of concrete systems; Triangle (triangle_reachDiameter_one_reachRecurrenceDiameter_two) is the 3-state instance. Lean: `Toy.KInd.reachDiameter_lt_reachRecurrenceDiameter_family`, `Toy.KInd.triangle_reachDiameter_one_reachRecurrenceDiameter_two`.
- **Prior art:**
  - D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. Definition 1 (completeness threshold CT(M, phi) = min{i | M |=_i phi -> M |= phi}), Definition 2 (reachability diameter rd(M): least i such that every reachable state is reachable within i steps), Definition 3 (reachability recurrence diameter rrd(M): longest loop-free path from an initial state). States (p. 300) that the completeness threshold for Gp formulas is the reachability diameter, and shows (Fig. 1) that rd(M) does not suffice for Fp formulas, for which rrd(M) is used. ReachDiameterBound/IsReachDiameter and ReachRecurrenceBound/IsReachRecurrenceDiameter here correspond to rd(M) and rrd(M).
  - A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. Statement numbers follow the technical-report version (CMU-CS-99-101) and may differ in the published version. Definition 19 (diameter: the least d such that whenever a state v is reachable from a state u, it is reachable via a path of length at most d); Definition 22 (recurrence diameter: the least d such that every sequence of states s0, ..., s_{d+1} along transitions has s_{d+1} = s_j for some j <= d); Theorem 18 (for ECTL, a bound equal to the number of states suffices), Theorems 20 and 23 (the diameter suffices for EF p, the recurrence diameter for ECTL). These diameters range over all start states, so they are never smaller than the initialized notions used here.
- **Design question:** How much can BMC save by using the reachability diameter instead of the reachability recurrence diameter as its threshold? Up to n-2 steps in an n-state system when the reachability diameter is at least 1 (strictly positive savings need n >= 3), and up to n-1 steps when several initial states make the reachability diameter 0 (as when every state of an n-state chain is initial).
- **Non-claims:** see Boundaries, result 18.
- Basis: execution (Lean kernel check) — `Toy.KInd.reachDiameter_lt_reachRecurrenceDiameter_family` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — the savings from using the reachability diameter instead of a recurrence bound as a BMC threshold can grow linearly with the number of states, because the family exists for every n; whether computing the diameter pays off is a cost question not addressed here.

### 19. `inductive-strengthening`

- **Kind:** theorem. **Tier:** T0. The invariance rule with a strengthening (Bradley 2011, Section 3; standard textbook material, Manna and Pnueli 1995).
- **Depth:** `shallow`.
- **Plain claim:** For every transition system, if every initial state satisfies P and Q, and every transition from a state satisfying P and Q leads to a state satisfying P and Q, then every reachable state satisfies P.
- **Lean statement** (`Toy.KInd.invariant_of_inductive_strengthening`):

  ```lean
  -- lean/KInd/Strengthening.lean:34
  theorem invariant_of_inductive_strengthening {Q : σ → Prop} (hIP : Initiation I P)
      (hIQ : Initiation I Q) (hcons : Consecution T (fun s => P s ∧ Q s)) :
      Invariant I T P
  ```

  With the key definitions unfolded:

  ```text
  (∀ s, I s → P s) → (∀ s, I s → Q s) → (∀ s t, P s ∧ Q s → T s t → P t ∧ Q t) → Invariant I T P
  ```

- **Hypothesis ledger:**
  - `hIP : Initiation I P` (tight: counterexample `Toy.KInd.strengthening_needs_init_P`). P must hold initially; initiation of Q and joint consecution do not imply it.
  - `hIQ : Initiation I Q` (tight: counterexample `Toy.KInd.strengthening_needs_init_Q`). The strengthening must hold initially.
  - `hcons : Consecution T (P ∧ Q)` (tight: counterexample `Toy.KInd.strengthening_needs_consecution`). Joint preservation by transitions.
- **Non-vacuity witness:** TwoInd with Q := (state ≠ 1): P alone is not preserved, P ∧ Q is. Lean: `Toy.KInd.nonvacuity_inductive_strengthening`.
- **Prior art:**
  - A. R. Bradley, 'SAT-Based Model Checking without Unrolling', VMCAI 2011, LNCS 6538, pp. 70-87, doi:10.1007/978-3-642-18275-4_7. Section 3 defines initiation (I => F) and consecution (F and T => F'), calls F an inductive strengthening of P when F and P together are inductive, notes that iterative post-image (respectively pre-image) computation yields the strongest (respectively weakest) inductive strengthening of P, and defines F to be inductive relative to G when I => F and G and F and T => F' (citing Manna and Pnueli 1995 for relative inductiveness). IC3 builds such relatively inductive clauses; IC3 itself is not modelled here.
  - Z. Manna, A. Pnueli, 'Temporal Verification of Reactive Systems: Safety', Springer, 1995, ISBN 978-0-387-94459-3, doi:10.1007/978-1-4612-4222-2. Standard textbook treatment of invariance proofs for transition systems (cited by Bradley 2011 for relative inductiveness). Bibliographic data verified on the publisher's page; the book's text was not consulted, so no specific rule or page is cited.
- **Design question:** What exactly does an inductive strengthening buy? Initiation of both conjuncts plus joint consecution suffice for P, and each is needed.
- **Non-claims:** see Boundaries, result 19.
- Basis: execution (Lean kernel check) — `Toy.KInd.invariant_of_inductive_strengthening` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — an invariant-inference tool that finds Q such that P and Q hold initially and P-and-Q is preserved by every transition has a valid safety proof, because the theorem holds for every system; relative inductiveness with respect to frames is a different rule, not covered here.

### 20. `reachable-strongest-inductive-invariant`

- **Kind:** characterization. **Tier:** T0. Completeness of the invariance rule: the reachable set is the least inductive set containing the initial states, and 'every path from here stays in P' is the weakest inductive strengthening (strongest and weakest inductive strengthenings, Bradley 2011, Section 3; textbook material, Manna and Pnueli 1995).
- **Depth:** `shallow`.
- **Plain claim:** For every transition system (finite or infinite): the reachable set contains the initial states, is preserved by transitions, and is contained in every such set; consequently P is invariant if and only if P ∧ Reachable satisfies initiation and consecution, if and only if some Q with initiation and consecution implies P. Dually, 'every path from s, of any length, ends in P' is preserved by transitions, implies P, contains every predicate that is preserved by transitions and implies P, and holds initially exactly when P is invariant.
- **Lean statement** (`Toy.KInd.reachable_strongest_inductive_invariant`, `Toy.KInd.invariant_iff_reachable_strengthening_inductive`, `Toy.KInd.invariant_iff_exists_inductive_strengthening`, `Toy.KInd.futureSafe_forever_weakest_inductive_strengthening`):

  ```lean
  -- lean/KInd/Strengthening.lean:43
  theorem reachable_strongest_inductive_invariant :
      Initiation I (Reachable I T) ∧ Consecution T (Reachable I T) ∧
        ∀ Q : σ → Prop, Initiation I Q → Consecution T Q → ∀ s, Reachable I T s → Q s

  -- lean/KInd/Strengthening.lean:51
  theorem invariant_iff_reachable_strengthening_inductive :
      Invariant I T P ↔
        Initiation I (fun s => P s ∧ Reachable I T s) ∧
          Consecution T (fun s => P s ∧ Reachable I T s)

  -- lean/KInd/Strengthening.lean:65
  theorem invariant_iff_exists_inductive_strengthening :
      Invariant I T P ↔ ∃ Q : σ → Prop, Initiation I Q ∧ Consecution T Q ∧ ∀ s, Q s → P s

  -- lean/KInd/Strengthening.lean:99
  theorem futureSafe_forever_weakest_inductive_strengthening :
      Consecution T (fun s => ∀ m, FutureSafe T P m s) ∧
        (∀ s, (∀ m, FutureSafe T P m s) → P s) ∧
        (∀ Q : σ → Prop, Consecution T Q → (∀ s, Q s → P s) →
          ∀ s, Q s → ∀ m, FutureSafe T P m s) ∧
        (Initiation I (fun s => ∀ m, FutureSafe T P m s) ↔ Invariant I T P)
  ```

  With the key definitions unfolded:

  ```text
  Initiation I R ∧ Consecution T R ∧ ∀ Q, Initiation I Q → Consecution T Q → ∀ s, R s → Q s  (R = Reachable I T);   Invariant I T P ↔ Initiation I (P ∧ R) ∧ Consecution T (P ∧ R);   Invariant I T P ↔ ∃ Q, Initiation I Q ∧ Consecution T Q ∧ ∀ s, Q s → P s;   with W s := ∀ m, FutureSafe T P m s: Consecution T W ∧ (∀ s, W s → P s) ∧ (∀ Q, Consecution T Q → (∀ s, Q s → P s) → ∀ s, Q s → W s) ∧ (Initiation I W ↔ Invariant I T P)
  ```

- **Hypothesis ledger:** no hypotheses (unconditional characterizations over arbitrary transition systems).
- **Non-vacuity witness:** SelfLoop, where the reachable set is exactly {0}. Lean: `Toy.KInd.selfLoop_reachable_iff`.
- **Prior art:**
  - A. R. Bradley, 'SAT-Based Model Checking without Unrolling', VMCAI 2011, LNCS 6538, pp. 70-87, doi:10.1007/978-3-642-18275-4_7. Section 3 defines initiation (I => F) and consecution (F and T => F'), calls F an inductive strengthening of P when F and P together are inductive, notes that iterative post-image (respectively pre-image) computation yields the strongest (respectively weakest) inductive strengthening of P, and defines F to be inductive relative to G when I => F and G and F and T => F' (citing Manna and Pnueli 1995 for relative inductiveness). IC3 builds such relatively inductive clauses; IC3 itself is not modelled here.
  - Z. Manna, A. Pnueli, 'Temporal Verification of Reactive Systems: Safety', Springer, 1995, ISBN 978-0-387-94459-3, doi:10.1007/978-1-4612-4222-2. Standard textbook treatment of invariance proofs for transition systems (cited by Bradley 2011 for relative inductiveness). Bibliographic data verified on the publisher's page; the book's text was not consulted, so no specific rule or page is cited.
  - D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. Definition II.2 (k-induction: the base checks paths from initial states of each length l < k, the step assumes k consecutive P-states; the same depth convention as Base k and Step k here). Footnote 3 (Section II): 'If P is k-inductive then P ∧ ◦P ∧ ◦◦P ∧ ... ∧ ◦◦···◦P [k-1 operators] is inductive, where ◦ stands for "next state"'; reading ◦ as 'in every successor state', this conjunction is FutureSafe T P (k-1). The footnote has no proof and concerns plain (not simple-path) k-induction. Lemma III.1: there are N-inductive properties whose shortest inductive strengthening has size larger than N; Lemma III.2: there is a property that is k-inductive for some k > 1 but has no inductive strengthening (its example lives in the quantifier-free fragment of a theory of arrays).
- **Design question:** Is every invariant provable by 1-induction with a suitable strengthening? Yes, semantically; the practical question is only expressibility and search.
- **Non-claims:** see Boundaries, result 20.
- Basis: execution (Lean kernel check) — `Toy.KInd.reachable_strongest_inductive_invariant`, `Toy.KInd.invariant_iff_reachable_strengthening_inductive`, `Toy.KInd.invariant_iff_exists_inductive_strengthening`, `Toy.KInd.futureSafe_forever_weakest_inductive_strengthening` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — every true safety property of a model has a 1-inductive strengthening (the reachable set), because the characterization holds for every system; failure to find one is a limitation of the search method or of the language strengthenings are written in, not of 1-induction as a proof rule.

### 21. `k-inductive-has-explicit-1-inductive-strengthening`

- **Kind:** theorem. **Tier:** T0. Re-derivation of Jovanović and Dutertre 2016, footnote 3 (if P is k-inductive then P ∧ ◦P ∧ ... ∧ ◦^(k-1) P is inductive), stated there without proof for plain k-induction. The version here assumes only the simple-path step, a small generalization (the plain-step form is the corollary kinductive_futureSafe_strengthening); not claimed novel. Batz et al. 2021 give a different explicit strengthening built from predecessors.
- **Depth:** `shallow`.
- **Plain claim:** For every transition system and every k: if P passes Base (k+1) and the simple-path step SimpleStep (k+1) (in particular, if P is (k+1)-inductive in the plain sense, Base (k+1) and Step (k+1)), then FutureSafe T P k, 'every path of at most k transitions from the state ends in P', holds in every initial state, is preserved by every transition, and implies P.
- **Lean statement** (`Toy.KInd.simple_kinductive_futureSafe_strengthening`):

  ```lean
  -- lean/KInd/Strengthening.lean:125
  theorem simple_kinductive_futureSafe_strengthening {k : Nat} (hb : Base I T P (k + 1))
      (hs : SimpleStep T P (k + 1)) :
      Initiation I (FutureSafe T P k) ∧ Consecution T (FutureSafe T P k) ∧
        ∀ s, FutureSafe T P k s → P s
  ```

  With the key definitions unfolded:

  ```text
  Base I T P (k+1) → SimpleStep T P (k+1) → Initiation I F ∧ Consecution T F ∧ ∀ s, F s → P s, where F s := ∀ j ≤ k, ∀ π, π 0 = s → IsPath T j π → P (π j)
  ```

- **Hypothesis ledger:**
  - `hb : Base I T P (k+1)` (tight: counterexample `Toy.KInd.futureSafe_strengthening_needs_base_k1`, `Toy.KInd.futureSafe_strengthening_needs_base`). Needed for initiation of the strengthening (Initiation I (FutureSafe T P k) is equivalent to Base (k+1)).
  - `hs : SimpleStep T P (k+1)` (tight: counterexample `Toy.KInd.futureSafe_strengthening_needs_step_k1`, `Toy.KInd.futureSafe_strengthening_needs_step`). Needed for consecution of the strengthening; strictly weaker than Step (k+1) for k >= 1, so the plain-step version follows.
- **Non-vacuity witness:** SelfLoop with k = 1: Base 2 and SimpleStep 2 hold while Step 2 fails; also TwoInd with k = 1, where FutureSafe T P 1 is exactly {0} (twoInd_futureSafe_one_iff). Lean: `Toy.KInd.nonvacuity_simple_kinductive_futureSafe_strengthening`, `Toy.KInd.nonvacuity_kind_sound`.
- **Prior art:**
  - D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. Definition II.2 (k-induction: the base checks paths from initial states of each length l < k, the step assumes k consecutive P-states; the same depth convention as Base k and Step k here). Footnote 3 (Section II): 'If P is k-inductive then P ∧ ◦P ∧ ◦◦P ∧ ... ∧ ◦◦···◦P [k-1 operators] is inductive, where ◦ stands for "next state"'; reading ◦ as 'in every successor state', this conjunction is FutureSafe T P (k-1). The footnote has no proof and concerns plain (not simple-path) k-induction. Lemma III.1: there are N-inductive properties whose shortest inductive strengthening has size larger than N; Lemma III.2: there is a property that is k-inductive for some k > 1 but has no inductive strengthening (its example lives in the quantifier-free fragment of a theory of arrays).
  - K. Batz, M. Chen, B. L. Kaminski, J.-P. Katoen, C. Matheja, P. Schröer, 'Latticed k-Induction with an Application to Probabilistic Programs', CAV 2021, LNCS 12760, pp. 524-549, doi:10.1007/978-3-030-81688-9_25. Lattice-theoretic k-induction. Lemma 2: Phi(Psi_f^k(f)) <= f iff Phi(Psi_f^k(f)) <= Psi_f^k(f), where Psi_f(g) = Phi(g) meet f, so the iterate Psi_f^k(f) is an inductive invariant stronger than f; Theorem 4 instantiates Phi(F) = I ∪ Succs(F) and recovers classical k-induction. For transition systems this gives another explicit 1-inductive strengthening of a k-inductive P, the (k-1)-fold iterate of G -> (I ∪ Succs(G)) ∩ P applied to P, built from predecessors rather than from successors as FutureSafe is. Section 4 requires a total transition relation and warns that without totality the classical SAT formulation of k-induction, whose base is a single fixed-length formula, is unsound.
  - K. Batz, B. L. Kaminski, L. Kehrer, G. Klein, H. Urbat, T. Schmid, 'The Algebra of Iterative Constructions', Archive of Formal Proofs, April 29, 2026, https://www.isa-afp.org/entries/Iteration_Algebra.html. Isabelle/HOL mechanization; its abstract lists 'a fixed point-theoretic generalization of k-induction' among its results. Lattice-level, not the path-based statements here.
  - A. Gurfinkel, A. Ivrii, 'K-Induction without Unrolling', FMCAD 2017, pp. 148-155, doi:10.23919/FMCAD.2017.8102253. Defines k-invariants (eq. 4: all states reachable in at most k steps satisfy the formula) and k-inductive invariants (eq. 5: the step assumes k+1 consecutive states, i.e. depth k+1 here). States that neither induction nor k-induction is complete and that k-induction restricted to loop-free paths is complete (citing Sheeran et al.). Its Lemma 2: if the K-Ind procedure returns BLOCKED, the returned G is an inductive strengthening of the clause relative to a 0-invariant F0; its Theorem 1, under the stated assumption that Generalize(¬s) always returns ¬s, characterizes when K-Ind returns BLOCKED (the clause is k-inductive relative to F0).
  - A. R. Bradley, 'SAT-Based Model Checking without Unrolling', VMCAI 2011, LNCS 6538, pp. 70-87, doi:10.1007/978-3-642-18275-4_7. Section 3 defines initiation (I => F) and consecution (F and T => F'), calls F an inductive strengthening of P when F and P together are inductive, notes that iterative post-image (respectively pre-image) computation yields the strongest (respectively weakest) inductive strengthening of P, and defines F to be inductive relative to G when I => F and G and F and T => F' (citing Manna and Pnueli 1995 for relative inductiveness). IC3 builds such relatively inductive clauses; IC3 itself is not modelled here.
- **Design question:** How do k-induction and inductive invariants relate? A property that passes (simple-path) k-induction at depth k+1 has the explicit 1-inductive strengthening 'P holds for the next k steps on every path', but not conversely.
- **Non-claims:** see Boundaries, result 21.
- Basis: execution (Lean kernel check) — `Toy.KInd.simple_kinductive_futureSafe_strengthening` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — a successful plain or simple-path k-induction proof can be turned into a 1-inductive certificate, FutureSafe T P k, because the theorem holds for every system; expressing that predicate in a tool's logic (it quantifies over paths) is a separate problem not addressed here.

### 22. `exact-length-base-needs-totality`

- **Kind:** theorem. **Tier:** T0. Folklore made explicit: SAT encodings of k-induction with a single fixed-length base formula assume a total transition relation (Sheeran et al. 2000, Section 2.2); Batz et al. 2021 (Section 4) warn that the classical formulation is unsound without totality.
- **Depth:** `shallow`.
- **Plain claim:** For every transition system in which every state has a successor and every k, checking that every path from an initial state with exactly k transitions satisfies P at every position is equivalent to Base (k+1) (every path with at most k transitions). Without totality, the exact-length check can be strictly weaker than Base (k+1) and unsound as a k-induction base, as proved at k = 2 on a concrete system with a dead end; at k = 0 the two checks coincide for every transition relation.
- **Lean statement** (`Toy.KInd.base_iff_exactBase_of_total`):

  ```lean
  -- lean/KInd/Soundness.lean:125
  theorem base_iff_exactBase_of_total {k : Nat} (htot : ∀ s, ∃ t, T s t) :
      Base I T P (k + 1) ↔
        ∀ π : Nat → σ, I (π 0) → IsPath T k π → ∀ i, i ≤ k → P (π i)
  ```

  With the key definitions unfolded:

  ```text
  (∀ s, ∃ t, T s t) → (Base I T P (k+1) ↔ ∀ π, I (π 0) → IsPath T k π → ∀ i ≤ k, P (π i))
  ```

- **Hypothesis ledger:**
  - `htot : ∀ s, ∃ t, T s t` (tight: counterexample `Toy.KInd.exact_length_base_unsound_without_totality`). Shorter paths extend to length k only if every state has a successor.
- **Non-vacuity witness:** NatSucc (the infinite counter, every state has a successor). Lean: `Toy.KInd.nonvacuity_base_iff_exactBase_of_total`.
- **Prior art:**
  - M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. Assumes that every state has a successor (Section 2.2). Defines a path of length n as n transitions and loopFree paths (pairwise distinct states). 'Induction with depth i' checks that after i+1 P-states in a row the next state satisfies P; 'strengthened induction with depth' restricts this step to loop-free paths, and the paper states that without this restriction induction with depth is incomplete. The constraint that no state after position 0 is initial (all.¬I(s[1..i])) appears only in its forward termination check (Algorithms 2-5), not in the induction step. Its depth index i corresponds to depth i+1 here.
  - K. Batz, M. Chen, B. L. Kaminski, J.-P. Katoen, C. Matheja, P. Schröer, 'Latticed k-Induction with an Application to Probabilistic Programs', CAV 2021, LNCS 12760, pp. 524-549, doi:10.1007/978-3-030-81688-9_25. Lattice-theoretic k-induction. Lemma 2: Phi(Psi_f^k(f)) <= f iff Phi(Psi_f^k(f)) <= Psi_f^k(f), where Psi_f(g) = Phi(g) meet f, so the iterate Psi_f^k(f) is an inductive invariant stronger than f; Theorem 4 instantiates Phi(F) = I ∪ Succs(F) and recovers classical k-induction. For transition systems this gives another explicit 1-inductive strengthening of a k-inductive P, the (k-1)-fold iterate of G -> (I ∪ Succs(G)) ∩ P applied to P, built from predecessors rather than from successors as FutureSafe is. Section 4 requires a total transition relation and warns that without totality the classical SAT formulation of k-induction, whose base is a single fixed-length formula, is unsound.
  - N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). Incremental SAT k-induction: the step assumes n+1 consecutive P-states and is strengthened with a uniqueness constraint (all states pairwise distinct), which makes the method complete for finite systems; the base is checked one exact length at a time as n increases, so all lengths up to n are covered. Notes that intermediate states of a shortest counterexample are neither initial nor bad, and that the step they use includes the uniqueness constraints but not 'not initial' constraints.
  - D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. Definition II.2 (k-induction: the base checks paths from initial states of each length l < k, the step assumes k consecutive P-states; the same depth convention as Base k and Step k here). Footnote 3 (Section II): 'If P is k-inductive then P ∧ ◦P ∧ ◦◦P ∧ ... ∧ ◦◦···◦P [k-1 operators] is inductive, where ◦ stands for "next state"'; reading ◦ as 'in every successor state', this conjunction is FutureSafe T P (k-1). The footnote has no proof and concerns plain (not simple-path) k-induction. Lemma III.1: there are N-inductive properties whose shortest inductive strengthening has size larger than N; Lemma III.2: there is a property that is k-inductive for some k > 1 but has no inductive strengthening (its example lives in the quantifier-free fragment of a theory of arrays).
- **Design question:** When implementing the k-induction base as one fixed-length unrolling, what must hold? The transition relation must be total; otherwise check every length below k.
- **Non-claims:** see Boundaries, result 22.
- Basis: execution (Lean kernel check) — `Toy.KInd.base_iff_exactBase_of_total` and every name above; axioms listed under Evidence.
- Basis: derived (modeling bridge) — an engine whose base check is a single unrolling of one exact length is sound only if the model's transition relation is total (or every length is checked), because the theorem needs totality and the OneEdge counterexample shows the failure otherwise.

## Boundaries

### Non-claims

**Applies to every result:** Toy model only: an abstract transition system (a state type in any universe, an initial-state predicate, and a transition relation that need not be total) and a state property; paths are explicit finite state sequences. No symbolic encoding, SAT/SMT solving, incremental algorithms, input variables, fairness, or liveness. Transfer to a real model checker is a separate modelling argument this package does not provide.

**1. `kind-sound`**

- Does not say Base k and Step k ever hold together for a given invariant: plain k-induction can fail at every depth even on a finite system (plain-kind-incomplete-every-depth).
- The base depth matters: Base (k-1) together with Step k is not sound (kind_sound_base_depth_tight, k = 2). Literature depth indices differ by one in various ways; translate before comparing.
- Base k checks every prefix length j < k, not only paths with exactly k-1 transitions. A base check over paths of exact length k-1 only (a single fixed-length unrolling, as in SAT encodings that assume a total transition relation) is unsound when some states have no successor (exact_length_base_unsound_without_totality); it is equivalent to Base k when every state has a successor (exact-length-base-needs-totality).
- At k = 0, Base 0 is vacuous (it covers no state, not even the initial ones) and Step 0 says that P holds in every state.
- Step quantifies over all paths, including paths through unreachable states and paths that revisit initial states. Of the variants that add constraints to the step, only the simple-path constraint is modelled (kind-simple-sound). A 'no initial state after position 0' constraint on the step (Eén and Sörensson note that intermediate states of a shortest counterexample are not initial) and the separate termination check of Sheeran et al. (which applies that constraint to loop-free paths from initial states) are not modelled.

**2. `kind-simple-sound`**

- The proof is shallow only given loop removal (loop-removal): a shortest path to a state is simple.
- Distinctness must be imposed on full states. Imposing it only on a projection of the state (for example on some of the state variables) is unsound in general (projected_simple_step_unsound: Base 2 and the projected step at depth 2 hold on Chain, P is not invariant); any such reduction needs its own argument.
- As for plain k-induction, the base depth cannot be lowered: Base (k-1) together with SimpleStep k is unsound (kind_simple_sound_base_depth_tight, k = 2), and a base check of exact length k-1 only is unsound without a total transition relation (exact_length_base_unsound_without_totality).
- Does not claim any depth at which SimpleStep holds for infinite systems; there it can fail at every depth even when only one state is reachable (simple-kind-incomplete-infinite).

**3. `loop-removal`**

- The statement takes only ReachIn I T m s, not a witness path, so it promises only some initial start state, not the start state of a given path, and it does not promise that the simple path uses only states or transitions of a given path or that it preserves a state predicate along the way (the construction in the proof cuts cycles out of a given path and does all of this, but that is not part of the statement).
- Says nothing about shortest paths being unique or computable.

**4. `depth-monotonicity`**

- Base alone is antitone, not monotone, in the depth: Base (k+1) implies Base k, not conversely.
- Monotonicity means iterating k upward never loses a success; it gives no bound on the first successful depth.
- Monotonicity of success is proved for plain k-induction (Base k ∧ Step k); for the simple-path variant only the step check is shown monotone (SimpleStep.mono), which together with soundness gives the same conclusion.
- Does not cover k-induction relative to changing auxiliary information (for example frames or strengthenings that change with k, as in IC3-style or property-directed k-induction); those checks are not modelled and their monotonicity is not claimed.

**5. `one-induction-fails-two-induction-succeeds`**

- One concrete system, a reference point; the general separation at every depth is fixed-depth-kind-incomplete.
- Does not say 2-induction is always enough when 1-induction fails, and does not characterize when k-induction succeeds.

**6. `fixed-depth-kind-incomplete`**

- Fixed-depth incompleteness applies to the simple-path step as well as to the plain step: the witness chain 1 -> ... -> k+1 in Ladder k is already simple. The simple-path constraint restores completeness on finite systems only when the depth may grow with the number of states (simple-kind-complete-fin: depth n for n states), not at any fixed depth.
- Does not say that k-induction fails at every depth on one system; for plain Step that is plain-kind-incomplete-every-depth (finite), for SimpleStep it needs an infinite state type (simple-kind-incomplete-infinite).
- The systems grow with k (k+2 states). It does not say how the required depth relates to the number of states in general, beyond the bounds of simple-kind-complete-fin and simple-kind-complete-fin-pred-of-init.
- Escape hatches (each proves the invariant of Ladder k): a depth that depends on the system (Base (k+1) and Step (k+1) succeed, ladder_kind_succeeds_at_depth_succ); a 1-inductive strengthening (Q := state = 0, ladder_inductive_strengthening, used with inductive-strengthening); BMC at a reachability-diameter bound (only state 0 is reachable, so BMC 0 suffices, ladder_reachDiameterBound_zero_bmc_zero).

**7. `plain-kind-incomplete-every-depth`**

- Concerns plain Step only. On the same system the simple-path step succeeds at depth 2 (selfLoop_simple_kind_succeeds_at_two), BMC to depth 0 with reachability-diameter bound 0 proves the invariant (selfLoop_reachDiameterBound_zero_bmc_zero), and so does 1-induction with the strengthening Reachable (reachable-strongest-inductive-invariant).
- Finiteness alone does not rescue plain k-induction; adding the simple-path constraint is one standard way to restore completeness on finite systems, inductive strengthening and BMC at a reachability-diameter bound are others.
- Escape hatches: the impossibility needs unreachable states and a cycle. If every state is reachable, every invariant passes Step 0 and hence every Step k (step_zero_of_invariant_of_all_reachable with Step.mono); if the transition relation of an n-state system has no cycle, Step n holds for every property (step_card_of_acyclic). A sharper characterization of when plain k-induction eventually succeeds is not formalized.

**8. `simple-step-vacuous-at-card`**

- Vacuity, not insight: at depth n the step check carries no information, so 'Base n and SimpleStep n' is equivalent to Base n alone, i.e. BMC to depth n-1.
- In practice simple-path k-induction often succeeds far below n; this result says nothing about when.
- Finiteness of the whole state type is what matters: a finite set of reachable states does not suffice (simple-kind-incomplete-infinite).

**9. `simple-kind-complete-fin`**

- The step half is vacuous at depth n (simple-step-vacuous-at-card); the result does not say simple-path k-induction is efficient, only that it terminates by depth n.
- Plain Step is not complete at any depth, even for finite systems (plain-kind-incomplete-every-depth).
- Finiteness of the reachable state space (or a finite reachability diameter or reachability recurrence diameter) is NOT enough when the state type is infinite: NatDescent has exactly one reachable state and both bounds 0, yet SimpleStep fails at every depth (simple-kind-incomplete-infinite).
- Does not model the 'no initial state after position 0' constraint or the termination check of Sheeran et al.

**10. `simple-kind-complete-fin-pred-of-init`**

- The bound n-1 is optimal only as a bound over all n-state systems; individual systems often need much less.
- At depth n-1 the step is not vacuous in general (simple paths with n-1 transitions may exist), but its proof does not use the step's assumption that the first n-1 states satisfy P: it uses only that such a path visits an initial state, so its last state is reachable. Sharper bounds in terms of the number of reachable states are not established here.
- The optimality statement 'not n-2' is meaningful only for n >= 2.
- Finiteness of the reachable state space is not enough when the state type is infinite (simple-kind-incomplete-infinite).

**11. `simple-kind-incomplete-infinite`**

- The obstruction is the infinite unreachable part (the simple paths k+1 -> k -> ... -> 1), not the reachable part: finiteness of the reachable states, a finite reachability diameter, or a finite reachability recurrence diameter does not make simple-path k-induction complete.
- Other methods prove this invariant: BMC at depth 0 (natDescent_bmc_zero_proves_invariant, since 0 bounds the reachability diameter) and 1-induction with the strengthening Q := (state = 0). On a finite system of similar shape simple-path k-induction succeeds (selfLoop_simple_kind_succeeds_at_two; in general simple-kind-complete-fin).
- Does not say that k-induction is useless for infinite-state systems; it says no depth is guaranteed to work without a strengthening.

**12. `bmc-complete-of-diameter-bound`**

- Applies only to safety invariants (always P). The reachability diameter is not a completeness threshold for eventualities (Fp; Kroening and Strichman 2003, Fig. 1) or for general LTL properties, which are not modelled here.
- Uses the reachability diameter (paths from initial states), not the graph-theoretic diameter over all pairs of states; the latter is never smaller, so it is also a valid but possibly wasteful bound. With no initial state, 0 is a reachability-diameter bound (nothing is reachable).
- BMC k here means at most k transitions (k+1 states), i.e. Base (k+1). With 'at most k states' the same claim is false at k equal to the reachability recurrence diameter (base-at-recurrence-diameter-off-by-one).
- Computing or certifying a reachability-diameter bound is not addressed (Biere et al. 1999 note that the diameter needs a quantified formula).
- For a particular property the threshold can be smaller than the reachability diameter.
- On an infinite state type no finite bound need exist, and then no BMC depth is complete in general (bmc_incomplete_every_depth_infinite).

**13. `recurrence-bound-is-diameter-bound`**

- The reachability recurrence diameter can be much larger than the reachability diameter (diameter-below-recurrence-diameter: gap n-2 in an n-state system), so this threshold can be wasteful.
- Initialized notions only (paths from initial states); the uninitialized notions of Biere et al. 1999 are never smaller.
- On an infinite state type a finite reachability diameter does not imply that any reachability recurrence bound exists (starChain_reachDiameter_one_no_reachRecurrenceBound).
- Applies only to safety invariants; for eventualities Kroening and Strichman 2003 use the reachability recurrence diameter for a different reason, not modelled here.

**14. `reach-diameter-le-reach-recurrence-bound`**

- Assumes the reachability diameter exists (some finite bound is least). On an infinite state type a finite reachability diameter can exist while no reachability recurrence bound does (starChain_reachDiameter_one_no_reachRecurrenceBound); then the hypothesis hr cannot be met.
- The inequality can be strict: by up to n-2 in an n-state system when the reachability diameter is at least 1 (diameter-below-recurrence-diameter), and by n-1 when several initial states make the reachability diameter 0 (on the chain 0 -> 1 -> ... -> m with every state initial, rd = 0 and rrd = m; supporting theorem allInitChain_reachDiameter_zero_reachRecurrenceDiameter_pred). It can also be an equality (both are 1 on the single edge 0 -> 1, the m = 0 instance of reachDiameter_lt_reachRecurrenceDiameter_family).
- The proof is short only given reachDiameterBound_of_reachRecurrenceBound, which rests on loop removal (exists_simple_reachIn, card loop-removal, substantive); unlike the zero-axiom definitional cards (bmc-complete-of-diameter-bound, bmc-threshold-characterization) it depends on propext, Classical.choice and Quot.sound.
- Initialized notions only; with no initial state both are 0.

**15. `bmc-complete-fin`**

- n is the number of states, typically exponential in the number of state variables; this is a worst-case bound, not a practical one.
- At n = 0 the depth n - 1 is 0 by truncated subtraction; the statement is then vacuous (no states).
- Only safety invariants; not a threshold for other temporal properties.

**16. `bmc-threshold-characterization`**

- Definitional: Invariant I T (ReachWithin I T k) unfolds to ReachDiameterBound I T k, so both directions are short unfoldings; the content is the choice of the witness property ReachWithin I T k.
- Quantifies over all state predicates P : σ → Prop. For a restricted class of properties (a syntactic fragment, a fixed set of atomic propositions, or a single P) the least uniformly complete depth can be smaller; for example, for the class {True} it is 0.
- Only safety invariants; for eventualities and general LTL the reachability diameter does not suffice (Kroening and Strichman 2003, Fig. 1; Clarke et al. 2004).
- Does not say BMC below the reachability diameter is useless: it is still sound for finding counterexamples and may prove specific properties via other arguments.
- Concrete instance of incompleteness below the reachability diameter: chain_bmc_below_diameter (Chain, reachability diameter 2, BMC 1 holds, P not invariant).

**17. `base-at-recurrence-diameter-off-by-one`**

- Not a flaw in BMC: it shows that a threshold stated in transitions must be checked over paths with that many transitions (k+1 states).
- A reference point for the conventions of this package; the mathematical content is in bmc-complete-of-diameter-bound and recurrence-bound-is-diameter-bound.

**18. `diameter-below-recurrence-diameter`**

- Shows only that the two thresholds can differ by n-2 in an n-state system; that is the largest possible gap when the reachability diameter is at least 1 (the recurrence diameter is at most n-1). It says nothing about typical systems or about the cost of computing either quantity.
- With several initial states the reachability diameter can be 0 and the gap n-1: on the chain 0 -> 1 -> ... -> m (n = m+1 states) with every state initial, rd = 0 and rrd = m = n-1 (supporting theorem allInitChain_reachDiameter_zero_reachRecurrenceDiameter_pred). The family TriangleN has a single initial state.
- Within the family, rd < rrd holds only for n >= 3 (m >= 1). At m = 0 (n = 2; TriangleN 0 is the single edge 0 -> 1) the statement gives IsReachDiameter 1 and IsReachRecurrenceDiameter 1, so both thresholds equal 1 and the gap n-2 is 0.
- Whether computing the reachability diameter (which needs a quantified formula) pays off against using the propositionally checkable recurrence bound is a cost question not addressed here.
- The family is a complete DAG, not the fully connected (complete digraph) example of Biere et al. 1999; both have a longest simple path visiting all states.

**19. `inductive-strengthening`**

- Says nothing about how to find Q; IC3 is cited only as the main algorithmic context.
- Consecution is required of the conjunction only; neither P nor Q needs to be preserved alone.
- Requires plain joint consecution Consecution T (P ∧ Q). It does not model relative inductiveness (Q is inductive relative to G when I => Q and G ∧ Q ∧ T => Q', for a frame G that need not itself be inductive), the notion IC3 works with.

**20. `reachable-strongest-inductive-invariant`**

- Finiteness is not needed: every invariant of every transition system, finite or infinite, has these 1-inductive strengthenings.
- P ∧ Reachable is the strongest (least) and 'every path from here stays in P' the weakest (greatest) 1-inductive strengthening; many others lie in between, and none of them is claimed canonical for proof search.
- These strengthenings may not be expressible in a given assertion language (for example a quantifier-free theory; Jovanović and Dutertre 2016, Lemma III.2, give a k-inductive property with no expressible inductive strengthening); this result is about sets, not formulas.
- Does not say the reachable set or the weakest strengthening is computable.

**21. `k-inductive-has-explicit-1-inductive-strengthening`**

- Depth convention: 'k-inductive' in the card id means passing Base and Step at depth k+1 here, i.e. (k+1)-inductive in the sense of Jovanović and Dutertre; the strengthening looks k steps ahead.
- The converse fails: FutureSafe T P k can be a 1-inductive strengthening of P while SimpleStep (k+1) fails (branch4_futureSafe_inductive_without_simpleStep). More generally, having some 1-inductive strengthening does not make P pass plain k-induction at any depth, even on a finite system (plain-kind-incomplete-every-depth); for the simple-path step it does on finite systems (simple-kind-complete-fin) but not on infinite ones (simple-kind-incomplete-infinite).
- A semantic set. As a formula it unrolls k steps of the transition relation and, unless the assertion language admits quantifier elimination, need not be expressible at all; Jovanović and Dutertre 2016 (Lemmas III.1 and III.2) show that inductive strengthenings can be larger than N for N-inductive properties or inexpressible. No size bound is claimed.
- Not the only explicit strengthening: Batz et al. 2021 give one built from predecessors (the (k-1)-fold iterate of G -> (I ∪ Succs(G)) ∩ P applied to P); it is not formalized here.

**22. `exact-length-base-needs-totality`**

- The counterexample is concrete: in OneEdge (state 1 has no successor) at depth 3, the exact-length base over 2-transition paths and Step 3 both hold vacuously, yet P is not invariant (exact_length_base_unsound_without_totality).
- Even when every state has a successor, the exact-length check must assert P at every position 0 <= i <= k of the path, not only at its last state. Checking only P (π k) is unsound: on the two-state cycle 0 <-> 1 with I = {0} and P = {0}, every path from 0 with exactly 2 transitions ends in 0 and Step 3 holds, yet state 1 is reachable and violates P (supporting theorem endpoint_only_exact_base_unsound_even_when_total).
- The totality hypothesis is not needed at k = 0: Base 1 and the exact-length check over paths with 0 transitions agree for every transition relation (supporting theorem base_one_iff_exactBase_zero). The counterexample for htot is at k = 2, and no theorem here covers any other depth k >= 1. That the exact-length check can be weaker and unsound at every k >= 1 (for example on Stuck, where for k >= 1 no path has k or k + 1 transitions, so the exact-length check and Step (k+1) hold vacuously while Base (k+1) fails at the initial state) is unproved commentary, not a result of this package.
- Incremental formulations that check every length up to k (as k grows) do not need totality; Base in this package is of that kind.
- Making a relation total by adding self-loops to dead ends changes the system; whether that preserves the property of interest is a separate question not addressed here.

### Escape hatches of the impossibility results

The three impossibility results each name the hypotheses or method choices that defeat them; each
escape hatch below is a proved Lean theorem.

* `fixed-depth-kind-incomplete` (Ladder k): a depth chosen per system (`ladder_kind_succeeds_at_depth_succ`:
  Base (k+1) and Step (k+1) hold); a 1-inductive strengthening (`ladder_inductive_strengthening`,
  Q := state = 0, used with `inductive-strengthening`); BMC at a reachability-diameter bound
  (`ladder_reachDiameterBound_zero_bmc_zero`: only state 0 is reachable, BMC 0 suffices).
* `plain-kind-incomplete-every-depth` (SelfLoop): the simple-path step (`selfLoop_simple_kind_succeeds_at_two`);
  all states reachable (`step_zero_of_invariant_of_all_reachable`: every invariant passes Step 0,
  hence every Step k by `Step.mono`); an acyclic transition relation (`step_card_of_acyclic`: Step n
  holds for every property of an n-state acyclic system); BMC with reachability-diameter bound 0
  (`selfLoop_reachDiameterBound_zero_bmc_zero`); 1-induction with the strengthening `Reachable`
  (`reachable-strongest-inductive-invariant`). A sharper characterization of when plain k-induction
  eventually succeeds is not formalized.
* `simple-kind-incomplete-infinite` (NatDescent): a finite state type (`simple-kind-complete-fin`;
  on the finite analogue SelfLoop, `selfLoop_simple_kind_succeeds_at_two`); BMC at depth 0
  (`natDescent_bmc_zero_proves_invariant`, since 0 bounds the reachability diameter); 1-induction
  with the strengthening Q := (state = 0).

### Tightness status

All 38 hypotheses of the 22 results are `tight`, each with a proved counterexample in which the other hypotheses hold and the conclusion fails. No hypothesis is labelled `harmless` or `unknown`. Entries marked "(parameter)" are not Lean hypotheses but parameters of the statement (the finite state type `Fin n`, or a depth such as `n` instead of `n - 1`); for the finiteness parameters the counterexample is an infinite analogue (`NatSucc`, `NatDescent`), on which the finite statement cannot literally be instantiated, and for the depth parameters it is a parametric family that defeats the smaller depth.

### Not examined

* **not examined:** a characterization of when plain k-induction eventually succeeds on finite
  systems (roughly: no cycle of P-states that can reach a non-P state through P-states); only the
  two special cases above (all states reachable; acyclic transition relation) are proved.
* **not examined:** a depth bound for simple-path k-induction in terms of the number of reachable
  states rather than the size of the state type; it would need cardinality reasoning not
  available without a library such as Mathlib.
* **not examined:** the lattice-theoretic inductive invariant obtained by iteration in Batz et al.
  2021 (Lemma 2; cited, not formalized); Sheeran et al.'s forward termination check and a step
  strengthened with "not initial" constraints.
* **not examined:** decidability of the checks; concrete facts about the small systems are proved
  through small-depth characterization lemmas (`step_two_iff`, `simpleStep_two_iff`,
  `reachIn_succ_iff`, `reachWithin_succ_iff`, `bmc_iff_reachWithin`) followed by `decide` or
  `omega`, not by a general decision procedure.

### Disproved or dropped statements

None. Every stated result is proved as stated; no statement was found false or left unproved.

### Stronger readings not established

Attractive stronger conclusions that the package does **not** establish:

* "k-induction is complete for finite systems": only with the simple-path step and a depth that
  may grow to the number of states (`simple-kind-complete-fin`); plain k-induction can fail at every
  depth on a 3-state system (`plain-kind-incomplete-every-depth`), and no fixed depth works for all
  finite systems (`fixed-depth-kind-incomplete`).
* "Finitely many reachable states (or a finite diameter) make simple-path k-induction complete":
  false; the whole state type must be finite (`simple-kind-incomplete-infinite`).
* "Distinctness on some state variables suffices": false in general (`projected_simple_step_unsound`).
* "A base of one exact length suffices": only under totality, and only if every position of the
  path is checked (`exact-length-base-needs-totality`).
* "BMC at the reachability diameter is cheap": no complexity or cost statement is made anywhere;
  the bounds on `n` are worst-case termination bounds.
* Nothing is said about liveness or general LTL properties, property-specific completeness
  thresholds, or the performance of any tool.

## Evidence

### Toolchain and build

- Toolchain: `leanprover/lean4` release `v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (from the GitHub API; `lean --version` of the toolchain used reports the same commit). Pinned in `lean/lean-toolchain`.
- Lake project `lean/` (`lakefile.toml` with one `[[lean_lib]]` named `KInd`, no dependencies; `lake-manifest.json` lists no packages). Modules: `KInd.Basic` (definitions), `KInd.Soundness`, `KInd.Finite`, `KInd.Systems`, `KInd.Completeness`, `KInd.Separation`, `KInd.BMC`, `KInd.Strengthening`, `KInd.Tightness`, `KInd.Examples`, `KInd.Remarks` (supporting theorems that back non-claims). `lean/RevalidationAudit.lean` is outside the library target.
- `lake build` succeeds with no errors and no warnings. No source contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`. All 303 declarations of the library depend only on `propext`, `Classical.choice` and `Quot.sound` (105 depend on no axiom at all); the full per-declaration record is `audit/axioms.json`.
- Observation date of all evidence (build, axiom audit, hashes, citation checks): 2026-11-20.

### Kernel-check record

For every Lean name referenced by `results.json` (results, non-vacuity witnesses, positive controls and counterexamples; roles give the result number), the axioms reported by Lean's `collectAxioms`, the SHA-256 of the statement and the SHA-256 of its definition closure (with the closure size), as recorded in `audit/statements.json`. What is hashed is defined under Revalidation.

| Name | Roles | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.KInd.kind_sound` | 1 result | `Quot.sound`, `propext` | `c0bd4790413538cd485d9b0b52370a52eefcf056d334a4717c32fc2e49e21824` | `e9d0773e1ea543a22c16ed372c2b07d9510f834b513dbc240dfddd28cba4386e` (6) |
| `Toy.KInd.kind_simple_sound` | 2 result | `Classical.choice`, `Quot.sound`, `propext` | `2077a77228df675f3a3abfd5c9b3c61f3b3579806a030fee82c310290bb570a5` | `0db6635085a12dc177254c730484a531bec2a43fd4fc4c7893f0d784c2bfb263` (7) |
| `Toy.KInd.exists_simple_reachIn` | 3 result | `Classical.choice`, `Quot.sound`, `propext` | `4f9040855e457b530721ed593a327ced06dfda9cb9d8e6422c9d4bc4f5229e3c` | `2ab34697e95dfa66c245a978ff56f7db842890ad3a8238b5d574cca2629ae87b` (3) |
| `Toy.KInd.kind_success_mono` | 4 result | `Quot.sound`, `propext` | `26ec98bfcb72073b641f5646aea9d61a36429d160d884ea8f123df16bb55cfba` | `8360902cfd1e5303fc6ac9e17783121e6e82006f2e4f72fc415f30780cfd26aa` (3) |
| `Toy.KInd.Step.mono` | 4 result | `Quot.sound`, `propext` | `607c398950f30b981ea9e3352821777a6f54e257b9ff614d4f76bbd1308f6933` | `4495efe64eb3956ebaaee72eedfc0ae4dc3eddd58dfe8a1087ee49005c1d3534` (2) |
| `Toy.KInd.SimpleStep.mono` | 4 result | `Quot.sound`, `propext` | `3b0f47b3b1242b962921c0ec1b143609757c507f102638cf5ca94a5ce1315159` | `7b56496869d176040284dbab50793b49435941ada2e8196894f1bac657da18d9` (3) |
| `Toy.KInd.one_induction_fails_two_induction_succeeds` | 5 result; 5 non-vacuity | `Quot.sound`, `propext` | `3317e3f99de28acfb64143766e5173cb17aae8864a77866b9035f32e65a69499` | `fc81c2a6abe16550f3f391ef35e3fa909166dfd3c99c8fe80a5e750f10adfc5e` (9) |
| `Toy.KInd.ladder_needs_depth_succ` | 6 result; 6 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `7ade4be8507174b41ffab28d978f5a71471e69e003efd53eecaa5275d26d6c16` | `be4a1788a91fee1f2ea3e1ff4f4b4dfa4adbdc6155f1efd632fe20e9672f0bc6` (11) |
| `Toy.KInd.plain_kind_incomplete_every_depth` | 7 result; 7 non-vacuity | `Quot.sound`, `propext` | `3772583ef0ca4e6001bf024e9face78038c300c54a35465e08afab71a4b5ac53` | `f4c075066eb6a44c8d26a95ad29eba13bb163063a2dee5d2b4a2f76e5c5bc3ea` (8) |
| `Toy.KInd.simpleStep_of_card_le` | 8 result | `Classical.choice`, `Quot.sound`, `propext` | `bc6bba781d82cb5611ee54012f3dc2fb74f60bee251042d70174640bf6b5ba7b` | `7b56496869d176040284dbab50793b49435941ada2e8196894f1bac657da18d9` (3) |
| `Toy.KInd.simple_kind_complete_fin` | 9 result | `Classical.choice`, `Quot.sound`, `propext` | `91cc8ec1ce44e9be52252c7d27f0b3f7c4d333011b8df99696433b367b50babb` | `0db6635085a12dc177254c730484a531bec2a43fd4fc4c7893f0d784c2bfb263` (7) |
| `Toy.KInd.simple_kind_complete_fin_pred_of_init` | 10 result | `Classical.choice`, `Quot.sound`, `propext` | `8bce9d118bf4d4b48269540515be9f543fcf8a5b2a63fb03f0f262745bc99fee` | `0db6635085a12dc177254c730484a531bec2a43fd4fc4c7893f0d784c2bfb263` (7) |
| `Toy.KInd.simple_kind_incomplete_every_depth_infinite` | 8 counterexample; 9 counterexample; 10 counterexample; 11 result; 11 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `911f2f32a474e078f658f9c12a5e941259efa76da36254db042a52732a4a31dc` | `5d41f8152be1d884fbb43b6294fc597793cd72bbd29b89bae04ff566cdaac730` (13) |
| `Toy.KInd.bmc_complete_of_reachDiameterBound` | 12 result | none | `1876f361b6764a9356f08c9b0537cdbfe064bb325f80199171242a054e6d9cc0` | `2ce9ae3127f77abf03d08699273fd1768112659058a306fe75ec1d88b4864636` (8) |
| `Toy.KInd.bmc_complete_of_reachRecurrenceBound` | 13 result | `Classical.choice`, `Quot.sound`, `propext` | `426e1d79a51f2e08fa178c21cad60beb878d019e363bdf31d8a0727e962b10ce` | `f16d85518dce6c4cf5f582647e9223ae08d529903ba94278e51707477b939858` (8) |
| `Toy.KInd.reachDiameterBound_of_reachRecurrenceBound` | 13 result | `Classical.choice`, `Quot.sound`, `propext` | `4573b91a9bd7b9aaa1dc567f633653879623e04638f8e1bdf15930b45c4bca9c` | `3721bbb7596a47c4c3f576af3a26213443b95afe21892f8ce8c9379633816c40` (7) |
| `Toy.KInd.isReachDiameter_le_of_reachRecurrenceBound` | 14 result | `Classical.choice`, `Quot.sound`, `propext` | `9899a527f06b0b1482c17a0dd4132e91efe411cb60311ef6c6e0cea4a5d09372` | `547c23278222480c194cb08bf18afef75328d120af8c6eb2bc404c770294abc9` (8) |
| `Toy.KInd.bmc_complete_fin` | 15 result | `Classical.choice`, `Quot.sound`, `propext` | `f59686da6ff766530fb245b4562cadcf4ac9db37755e44355ce8f34271c25645` | `f6821d51d35ddc3ea5969041f5ef835cbc7e125536501de153fb614f2a4d6a18` (6) |
| `Toy.KInd.bmc_complete_all_props_iff_reachDiameterBound` | 16 result | none | `f79367816492c7c4ff79a16f66493d6578a9ac7b19e5bfd3ce270688575ea7a4` | `2ce9ae3127f77abf03d08699273fd1768112659058a306fe75ec1d88b4864636` (8) |
| `Toy.KInd.bmc_incomplete_of_not_reachDiameterBound` | 16 result | none | `64238c74f7a357bb6df83d8625451a1cee0776fb9db4866e7775c0445a9186a2` | `2ce9ae3127f77abf03d08699273fd1768112659058a306fe75ec1d88b4864636` (8) |
| `Toy.KInd.base_at_recurrence_diameter_unsound` | 17 result; 17 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `fff301fe1b1e3c703179af66d5e1cee710c6a447ac854c0696978e7632b79160` | `11d6b9d59aafc14aa5058bb5d816cf9b6cb1499b49f6a5bea0cbd39e305a3477` (12) |
| `Toy.KInd.reachDiameter_lt_reachRecurrenceDiameter_family` | 18 result; 18 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `0468f4b2afaa2daeb84e48c419f39ea9eb742aa2cfdae8d59f2e1824101e3aee` | `72f49cfc3a13f5ff3df2bfebb2cd5cb003fab1cdd79579af91b132593c91a536` (11) |
| `Toy.KInd.invariant_of_inductive_strengthening` | 19 result | `Quot.sound`, `propext` | `73121faebe8bfc5ebe71504d3da7345f156823748bd35a0eab537c897d6fe361` | `91d19b33274298ce188da38a0e5ee9c72c482495571b04183a770843fe9837a0` (6) |
| `Toy.KInd.reachable_strongest_inductive_invariant` | 20 result | `Quot.sound`, `propext` | `d443a16fa70fdea72b57b31aa14275b30aa4e569be2922844d3bf066ce1bfb14` | `afbe77be74bfa0076e76cdac1d6eba116ecc6c43e6085b0b6e368bdc6b159446` (5) |
| `Toy.KInd.invariant_iff_reachable_strengthening_inductive` | 20 result | `Quot.sound`, `propext` | `dbe031c994d9d5f1621f4a955be2f6cdbe91849dc6a9c9c20b57cfadd80ca223` | `91d19b33274298ce188da38a0e5ee9c72c482495571b04183a770843fe9837a0` (6) |
| `Toy.KInd.invariant_iff_exists_inductive_strengthening` | 20 result | `Quot.sound`, `propext` | `4544a0aac269a44d068c17ab114619887640fd8d6e54da3a74363800432e3b70` | `91d19b33274298ce188da38a0e5ee9c72c482495571b04183a770843fe9837a0` (6) |
| `Toy.KInd.futureSafe_forever_weakest_inductive_strengthening` | 20 result | `Quot.sound`, `propext` | `c9ca87f25f40b46f5b92a2b9bd7e98e12e9f176ac738e5a37e89e901c129e4e3` | `87cf408630c428d8cd863ea830eaa12956fddaed3e36816d160c64c6f59ee3d9` (7) |
| `Toy.KInd.simple_kinductive_futureSafe_strengthening` | 21 result | `Classical.choice`, `Quot.sound`, `propext` | `4c43c8ae4981da89bc5d5459e8014972d613e9e918641fce323335d1b5e7ed1e` | `396d64f672dffc35daea49aca6fec8235ce7abe40104adcb55cc22afa0cb8272` (7) |
| `Toy.KInd.base_iff_exactBase_of_total` | 22 result | `Classical.choice`, `Quot.sound`, `propext` | `92b9136ae5e2fc9015acd6f00fb7a59d02346d2c751d4c94c40f3205659cd66b` | `916131da4e2c57b2ece6e5a798e2eb70fa0095f553c51fb13a61b3a60556f69c` (2) |
| `Toy.KInd.bmc_complete_fin_depth_tight` | 15 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `23ce4ce279e75589f11ab05b1128c85f5873ae399e16236ad11eb57d5187b9f2` | `b6d65b0c5f785494b3d421279fbaba96f8746edec60062f5cfb132e1964969a7` (9) |
| `Toy.KInd.bmc_complete_fin_depth_tight_all` | 15 counterexample | `Quot.sound`, `propext` | `fc30ac51f1bf7863880d3efea9e13c64f8218b4c33c05141be0d79745060cc95` | `da7016313aac2f6b8380f9e66eeb5641d62fe2e6b5d6bc897b6979c8cb5be878` (9) |
| `Toy.KInd.bmc_incomplete_every_depth_infinite` | 15 counterexample | `Quot.sound`, `propext` | `d320586045b5f385b487aac8948b286aa4136483a6f38ec5adab67c5884892fc` | `cd7f2080767d214eac01d3df8790502781bb4e79a7e8fdfe042961a75b8214b8` (10) |
| `Toy.KInd.bmc_incomplete_needs_not_reachDiameterBound` | 16 counterexample | `Quot.sound`, `propext` | `23cd48956c4675639ff40e9116ffd132bf863ba0b6f8dd6e7195b1ec957440f1` | `4617512cbef535ae00a8b8edab69724e9a8b80bbe522f9b1762924a4f8eef414` (10) |
| `Toy.KInd.bmc_reachDiameter_needs_hb` | 12 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `f408510f66b7a709eea17db12f92e6b33762c109136c2116c719b856010632de` | `4fe600acd6cb534efd80c3573b0c4ec7f8b6539dd678c720a5925fcae5573734` (11) |
| `Toy.KInd.bmc_reachDiameter_needs_hd` | 12 counterexample | `Quot.sound`, `propext` | `84ee9c14b2eb03fdbda6b9acfa266226937375294566190166846093bc956fcb` | `4fe600acd6cb534efd80c3573b0c4ec7f8b6539dd678c720a5925fcae5573734` (11) |
| `Toy.KInd.bmc_reachDiameter_needs_hk` | 12 counterexample | `Quot.sound`, `propext` | `f66f31d095c79e5a4605cb86fda717c1cd8727f2cb54c1d938a7f2fd06d7b885` | `4fe600acd6cb534efd80c3573b0c4ec7f8b6539dd678c720a5925fcae5573734` (11) |
| `Toy.KInd.bmc_reachRecurrence_needs_hb` | 13 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `2e13f6cf57a23cf7b5cdad8e45067e93ad98e8df38069b7e3a3512cd2070afe5` | `6af5667e7015a95522cc0cfcf24349499fa1427849c85c50221f25463a48e878` (11) |
| `Toy.KInd.bmc_reachRecurrence_needs_hk` | 13 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `7f1c81fa32fd5566e05825a27c2b4b6eb0f4d2fa2606e019bedca2f5688a9c73` | `6af5667e7015a95522cc0cfcf24349499fa1427849c85c50221f25463a48e878` (11) |
| `Toy.KInd.bmc_reachRecurrence_needs_hr` | 13 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `e640e94764591c5f1b7ddc95e7364dd36796cd800fc2cd82aba2be4c57d6369d` | `6af5667e7015a95522cc0cfcf24349499fa1427849c85c50221f25463a48e878` (11) |
| `Toy.KInd.chain_not_reachDiameterBound_one` | 16 non-vacuity | `Quot.sound`, `propext` | `296fb1e842c5b89bfe16b08968b082eebbc340bab5801ec95a22325c8f037b66` | `e0035dc172ecee5f18e0f343ffa806d3f4f8c456af7efd6a3a7243fdbb175b8c` (7) |
| `Toy.KInd.chain_reachDiameterBound_two` | 16 non-vacuity | `Quot.sound`, `propext` | `604c346393f6ee2af8150548c0435a6270c994ce7141002d67fc7913f4a06cf0` | `e0035dc172ecee5f18e0f343ffa806d3f4f8c456af7efd6a3a7243fdbb175b8c` (7) |
| `Toy.KInd.chain_reachWithin_two_invariant` | 16 positive control | `Quot.sound`, `propext` | `6d9b997a926d7b6de73db84d708c60c3ed878a3bd734e28a488e931753f9d5b3` | `6536087980e5322203d4c8321070b1dd0bb085d693f1688943647e750faca272` (7) |
| `Toy.KInd.exact_length_base_unsound_without_totality` | 22 counterexample | `Quot.sound`, `propext` | `6154224c0eff9a211962a3d3b28312c32b15d25b116a8e9c6709990001e08b5b` | `fd580d25d3b844c820f25115a3f12f96d18f2a47e867d15fd865b21c7f1946d0` (9) |
| `Toy.KInd.futureSafe_strengthening_needs_base` | 21 counterexample | `Quot.sound`, `propext` | `9a901f83cb41d6f61c389696cffff408270cb4f54de0f86687ced2c75b389c2e` | `47e378f9cb30b1bf97b08796886fa8114eb00f49c0d12b14136094c5bc39d742` (9) |
| `Toy.KInd.futureSafe_strengthening_needs_base_k1` | 21 counterexample | `Quot.sound`, `propext` | `2af35ac0ed222059365d7597e1121bdbb9fe8a59ff6819ba6a13fc6f2375bf6f` | `47e378f9cb30b1bf97b08796886fa8114eb00f49c0d12b14136094c5bc39d742` (9) |
| `Toy.KInd.futureSafe_strengthening_needs_step` | 21 counterexample | `Quot.sound`, `propext` | `784afed66fe931b69007ca8f4c56b5eb2653b786c4d8cca97dd2900809771d5e` | `cde591dd0d43cb922ddbe1c0f72874c0cc7cbeb6e7757b29f5cb576c2675fa99` (8) |
| `Toy.KInd.futureSafe_strengthening_needs_step_k1` | 21 counterexample | `Quot.sound`, `propext` | `a94ac780d3df89011fe7f5a9674f4937102bc564a81dc0f98e1163a4b70cec1d` | `eaa9c529226978c70e6f4ea1d67b3bc73bbb3c815b3bcf49e05aeb14849a6c15` (8) |
| `Toy.KInd.isReachDiameter_le_needs_hd` | 14 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `bdb281c4658802dd94781abfdfdb4cf49716ddb84b5911467159c3fe1aa53c3b` | `4b6afe1896710c2d73ebe32caa35d0fa1b970ac880257b36dfb1be0e0c42fdd2` (5) |
| `Toy.KInd.isReachDiameter_le_needs_hr` | 14 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `e83d977474701993ea055176183433bd3c9e22ba9dfa9f5aabbaa9623ba75f2e` | `8fea0988bc78ef874429fc3ef29732c305bc4b950aebf68eeaf3bea32f5fe947` (8) |
| `Toy.KInd.kind_simple_sound_base_depth_tight` | 2 counterexample | `Quot.sound`, `propext` | `da5914b6d973c7a6ed1655d793fedbd2f6f09f082b767de7a5ee204b85b9356a` | `be51d25fec0f033f1a20d4cbbbed131e349c92343c887b08200a13b867db2da0` (10) |
| `Toy.KInd.kind_simple_sound_needs_base` | 2 counterexample | `Quot.sound`, `propext` | `142e23e300048f2e202d6513990c40e91f908736fdcf593403e123b52c45a51a` | `a983ebd882bd1174cd8dc311a44c19fb1952ed6c1fc059fa924efe1fa03f1363` (9) |
| `Toy.KInd.kind_simple_sound_needs_base_k2` | 2 counterexample | `Quot.sound`, `propext` | `d2dffdf08ef35433dddb5e3af6f7a67a9940695aefc51137d2283557c0f2a140` | `9a9c5d333e31ca6db5806846234f374f83e411c4c8a1a682aef14807dea5f0ec` (9) |
| `Toy.KInd.kind_simple_sound_needs_step_k2` | 2 counterexample | `Quot.sound`, `propext` | `701214d36d52821d552286a4eb25b014af21d0f0ce536b412e98775c794a7a76` | `8cef0249b499072dbdb1b3b2720a4de969d4ac9aa4930bc7510f89c3a51a2bf9` (8) |
| `Toy.KInd.kind_sound_base_depth_tight` | 1 counterexample | `Quot.sound`, `propext` | `b8749c963628d27862afdbef14406c82ace93da0f99b0df175b3ffbaa2d58764` | `fd580d25d3b844c820f25115a3f12f96d18f2a47e867d15fd865b21c7f1946d0` (9) |
| `Toy.KInd.kind_sound_needs_base` | 1 counterexample | `Quot.sound`, `propext` | `12604cb5343835091c46bc04e343c8090f70fd480af4a0319b57b3ab96e4d119` | `89893f98593d07e090efb269e90183a2763840f06d6b4bde29aaf0b5e70eec4c` (8) |
| `Toy.KInd.kind_sound_needs_step` | 1 counterexample; 2 counterexample | `Quot.sound`, `propext` | `32052f1342e6cf7c71f542282209e5d0eb69f5633f776b78e468fc9ace6bedeb` | `49aac795f0394b5c039a683ebaed8c47b2d96f968e100633aa45878fc74f2608` (8) |
| `Toy.KInd.kind_success_mono_needs_base` | 4 counterexample | `Quot.sound`, `propext` | `1d08d52cd0545141832da5a21dbdf77e29e039ed7f1845bfda7f08b018c22ede` | `609af6f6b73905a44f5e9f1e940bc12b626ae5889f44756c32f7ad28341265ee` (6) |
| `Toy.KInd.kind_success_mono_needs_le` | 4 counterexample | `Quot.sound`, `propext` | `d8e17ff8385b666793e43486918152721d3cb2b5871ab62648d7387deed3ffba` | `bf0edfeeef5bdd4d3a8c5c8dd9f0edc6b2f75e9aedd10efc56ed727d5db4c43d` (6) |
| `Toy.KInd.kind_success_mono_needs_step` | 4 counterexample | `Quot.sound`, `propext` | `1daa1087ae4d8ef4adbdc6f7c2a019f679a58df507a5f12bbeb0d7aba2126003` | `3d27d1a96f8b810f0312a6da8775dd8fcf609ee615b252f59a13b7d58ad0b516` (6) |
| `Toy.KInd.kind_success_mono_needs_step_invariant` | 4 counterexample | `Quot.sound`, `propext` | `b2505c0a113af2742015254d276a55c741652691bce5941c8d35d5303f5961ce` | `811b2426bb5995c07ede9cb83c4148caa62515d06ec88b8941d1d7686ed6152f` (9) |
| `Toy.KInd.ladder_inductive_strengthening` | 6 positive control | `Quot.sound`, `propext` | `3e74615788a72c47e396a9ce59bebbc093fa6d51804ac29be77748f5795f41e4` | `417457ef6001b332060b242bca29eca0f2210aeecb95489bd192bfb1fcf8c2fb` (5) |
| `Toy.KInd.ladder_kind_succeeds_at_depth_succ` | 6 positive control | `Classical.choice`, `Quot.sound`, `propext` | `c4c12078c8d225b6ca8f9016072cfee5c890548445fd27a210b920a4483f5ce6` | `bcd73c84c75069aae0b55fae3cd8288c0ff77cc8d4d9295114f758cf9aed92d2` (6) |
| `Toy.KInd.ladder_reachDiameterBound_zero_bmc_zero` | 6 positive control | `Quot.sound`, `propext` | `3709d30acd6e489b7b87509777468696e581a7d7531cc77fcb47fa5dce5f4314` | `d58cf02a17434883e7b77e4e8ecbe1c92c160166707ebb3779eeb354c307e132` (10) |
| `Toy.KInd.loop_removal_needs_reachIn` | 3 counterexample | `Quot.sound`, `propext` | `9c21d01c9a03f8d604691e773a302ca97c9d406f02602e4e4cc9f8f5db31b2b2` | `b5857c76410569839104f8f36920d1c122412c00038d969692f19aead085fea5` (4) |
| `Toy.KInd.natDescent_bmc_zero_proves_invariant` | 11 positive control | `Classical.choice`, `Quot.sound`, `propext` | `d5e34f7b933bc43d8173abcc278fae5ab18c29887e73eed61f375b91a12f525a` | `e92a0d36ea956fad2788183f422b80baad3f09c819ce959a515bf15ff8e99b01` (11) |
| `Toy.KInd.nonvacuity_base_iff_exactBase_of_total` | 22 non-vacuity | none | `1d8e5998f6407d493894b6740c213ea5d135187043895c2e6974c7d0c88de4d2` | `fe1e89b44656d6bc35a0a1bcf0b375fff2ea32522aaaf06222abb47b5609e8c1` (1) |
| `Toy.KInd.nonvacuity_bmc_complete_fin` | 15 non-vacuity | `Quot.sound`, `propext` | `058c52d96664ffdf4aa0b3d45fca79a93557c82d26b8b5f7106c3760c1d1d0a4` | `701d58a46ebd35958351a9a283bec0b45e4ec228131589782a2fba962b7e3377` (6) |
| `Toy.KInd.nonvacuity_bmc_complete_of_reachDiameterBound` | 12 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `b4d6e44a8eefb4d75fec32c441e6d36e698c0d382c845a2784de87658df2c12a` | `bab0609a5dd39a528d43a79abf3b9ea50ec2f1c7ba40c14292b2909d316f5466` (9) |
| `Toy.KInd.nonvacuity_bmc_complete_of_reachRecurrenceBound` | 13 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `a4edbf037a3469413221b6ae5f05fdc929572031fbbfa7db2df9e5b9226e22e1` | `9dc2e23664d2bcb89e286eb35a8ef47252e7f6e8f372f62c75a69ff1486c2d96` (7) |
| `Toy.KInd.nonvacuity_exists_simple_reachIn` | 3 non-vacuity | `Quot.sound`, `propext` | `1fcf00f0051112e09cb3065a5f8e75a8a6fdbaa86792f3d593230e31287f3b02` | `30a7f7e28e60e8b923e05825ea320eada6c2d9140a6eb893ca2866d7f6372ad2` (4) |
| `Toy.KInd.nonvacuity_inductive_strengthening` | 19 non-vacuity | none | `66fe996e1483f47f1cd1974cd5552f52eb466ad1265697056fb44d161638d739` | `a7fe285880b7b75deb6dbbe627ef8e56547dfd8272cd757381877012a43a2bd8` (5) |
| `Toy.KInd.nonvacuity_isReachDiameter_le_of_reachRecurrenceBound` | 14 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `8c02f33560bfcb9275fe704eba0966e2e93dd2e0b8a025d0c3b7ff3a2aea7489` | `26b7c0b48364ff7e88596c87c2183e4a0d745c9a228b9ec6e6546a6aab674d15` (10) |
| `Toy.KInd.nonvacuity_kind_simple_sound` | 2 non-vacuity | `Quot.sound`, `propext` | `c2938e4fa7f306b508759e36cc6707f4980674869b6bcef2a4d753836f3dcaf6` | `f2d826f3913e90991f459593c16384d4e742163874997267653de2d9d5695ceb` (8) |
| `Toy.KInd.nonvacuity_kind_sound` | 1 non-vacuity; 21 non-vacuity | `Quot.sound`, `propext` | `019dea03a670e4f0aaaa69bc3aa5dbf113f3f23b2e3b146d12bb11c9c62ef5d4` | `bf0edfeeef5bdd4d3a8c5c8dd9f0edc6b2f75e9aedd10efc56ed727d5db4c43d` (6) |
| `Toy.KInd.nonvacuity_kind_success_mono` | 4 non-vacuity | `Quot.sound`, `propext` | `2f6c5158b7cf427a1fe1188882cab2d03ecfcf038a102d7f13e205eefa9972f0` | `bf0edfeeef5bdd4d3a8c5c8dd9f0edc6b2f75e9aedd10efc56ed727d5db4c43d` (6) |
| `Toy.KInd.nonvacuity_simpleStep_mono` | 4 non-vacuity | `Quot.sound`, `propext` | `7c12c983b6b6b119bf3adb84f180241c5fef49b0a4ca829d9bd607c057a4bfc8` | `2a33d7971b812cd1660b40347e098949485ff60106049a3694f92cb314f83706` (6) |
| `Toy.KInd.nonvacuity_simpleStep_of_card_le` | 8 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `4f1df479e7dde62cbc2a4dba6bb38ed6329f525f15998680e3f3465ed409a5c6` | `bc3d7f82e2550bd14f87147a6f6524870f508f6e0aa516ef3a7df2faf31fe37e` (5) |
| `Toy.KInd.nonvacuity_simple_kind_complete_fin` | 9 non-vacuity; 10 non-vacuity | `Quot.sound`, `propext` | `16408de4684e031b250b3dddf000273ef365526fb1647b0882cc808050650acf` | `61508747b947454d8c02024de88d05d7607fe53eea851a8b55b03e20e77275d1` (7) |
| `Toy.KInd.nonvacuity_simple_kinductive_futureSafe_strengthening` | 21 non-vacuity | `Quot.sound`, `propext` | `c2938e4fa7f306b508759e36cc6707f4980674869b6bcef2a4d753836f3dcaf6` | `f2d826f3913e90991f459593c16384d4e742163874997267653de2d9d5695ceb` (8) |
| `Toy.KInd.nonvacuity_step_mono` | 4 non-vacuity | `Quot.sound`, `propext` | `19aaf97a9236e9cb8f0ac70c95226c3baf8ebcc39863130253598a159c214e96` | `9379104a3420c6c0c2edf325443db08a24bfbcc96f20310beb7c89489a4109ae` (4) |
| `Toy.KInd.reachDiameterBound_of_reachRecurrenceBound_needs_hr` | 13 counterexample | `Quot.sound`, `propext` | `296fb1e842c5b89bfe16b08968b082eebbc340bab5801ec95a22325c8f037b66` | `e0035dc172ecee5f18e0f343ffa806d3f4f8c456af7efd6a3a7243fdbb175b8c` (7) |
| `Toy.KInd.selfLoop_reachDiameterBound_zero_bmc_zero` | 12 non-vacuity | `Quot.sound`, `propext` | `4b8abad7d85379cc6849696b7d48ecd9c7f9dcf1d4ae646ae7658d1e4a4167c1` | `8d4cd23a7dad6ff5c3dbcf3d789c7f5be54f1917da296d7f6f27b1596966145d` (10) |
| `Toy.KInd.selfLoop_reachable_iff` | 20 non-vacuity | `Quot.sound`, `propext` | `aae968bf7c2be42688959b22f81805d833eb8f702c24326b5103d57c79c319dd` | `caa17d18db8012366ee5f42eda9ecd6a5b1e0ba506edb8b2f401334f4d1187d1` (5) |
| `Toy.KInd.selfLoop_simple_kind_succeeds_at_two` | 7 positive control; 11 positive control | `Quot.sound`, `propext` | `efc380b5e6bc39becddf33e79b14259ce34e3eeba8ded5f358b5b10fa62b16fa` | `d5b34068ee5c72dd0e3801b9dd208c136b0b479a01c32ef80fe2237338e51244` (7) |
| `Toy.KInd.simpleStep_mono_needs_le` | 4 counterexample | `Quot.sound`, `propext` | `91e7a277a2594b8669f390fb68c617a704ac06d8d237ef2daf7e8c69e0ffbe7d` | `bc3d7f82e2550bd14f87147a6f6524870f508f6e0aa516ef3a7df2faf31fe37e` (5) |
| `Toy.KInd.simpleStep_mono_needs_step` | 4 counterexample | `Quot.sound`, `propext` | `45f61fa506410245ad0af03a5af82fc97d891f7e45f1509bb34c8f2225043a6b` | `7200a93bdda6d396a258dca99642d591d98d5fcecaf77b4c4326da706e6d2edd` (5) |
| `Toy.KInd.simple_kind_complete_fin_needs_invariant` | 9 counterexample | `Quot.sound`, `propext` | `096e9baea4c74110afc26a13e646ccdd883ef4fe8d7bab746d90016c55d9f455` | `6be305ea2cc986c0fe18227d39f0ee88e0c68cc19936dd0dff685f09da985572` (7) |
| `Toy.KInd.simple_kind_complete_fin_pred_of_init_needs_invariant` | 10 counterexample | `Quot.sound`, `propext` | `73fff744ce0d9cfd65b0f9367722993ddb3677bae0d65a78637620263fb5f265` | `acc0a9f29d66d72d4da7529b828c0ec2a84dbce34f08b4ad1439908eeec4ebab` (6) |
| `Toy.KInd.simple_kind_depth_card_optimal_without_init` | 8 counterexample; 9 counterexample; 10 counterexample | `Quot.sound`, `propext` | `e105e3f65f7b54a63beb3773f4db95227aac3b1a7654fcdeea5da7ea538e292d` | `8cc7d30638fa52387313e1ce34c38148e3e464437a60a420bdb3965164d75bd5` (9) |
| `Toy.KInd.simple_kind_depth_pred_optimal_with_init` | 10 counterexample | `Classical.choice`, `Quot.sound`, `propext` | `2b3c271319db91dedecd15e7deb637c4dd02612944451232d9740de3be83e981` | `de3f74385e927428244c11d5de37ef58dd773520b1c344a69c131f47255f78fa` (9) |
| `Toy.KInd.step_card_of_acyclic` | 7 positive control | `Classical.choice`, `Quot.sound`, `propext` | `4e7c8e674de449d35d0894a02da957684d1a9156ccf15d0b4de143f725fc2f31` | `4495efe64eb3956ebaaee72eedfc0ae4dc3eddd58dfe8a1087ee49005c1d3534` (2) |
| `Toy.KInd.step_mono_needs_le` | 4 counterexample | `Quot.sound`, `propext` | `0910298361192583eae2da07eca407c0e89a8d8de17810040c42afd66b1c426b` | `9379104a3420c6c0c2edf325443db08a24bfbcc96f20310beb7c89489a4109ae` (4) |
| `Toy.KInd.step_mono_needs_step` | 4 counterexample | `Quot.sound`, `propext` | `bff0aef69ca4daaa44be23c9a0ff03c8dd10e33c8cc6c2e66873a700454d32af` | `3109471aa479404e94448de8fc832de30d921edbba4d471cf991589bb4fc5b5c` (4) |
| `Toy.KInd.step_zero_of_invariant_of_all_reachable` | 7 positive control | none | `637ed79c6b38e6c1dc76db74abbcb0520997d4629718d3cdb86333d6f0e387a0` | `20aebf299343d2f4026988eb1a4b44ca8701c672c5cea8fc4ea98fcc453f460f` (5) |
| `Toy.KInd.strengthening_needs_consecution` | 19 counterexample | `Quot.sound`, `propext` | `fdde0d633165c4f03eeb86ddb8b053dcfbdf7242038e55aecf113d34ba778b86` | `c199766f3cecf7b29eebfea28b8c3183bb361ee6676db90390e755d041a40c27` (8) |
| `Toy.KInd.strengthening_needs_init_P` | 19 counterexample | none | `1319c822b4d7fc6ffa9652e484d732fbab90d6956f80167fb88d8881127cb218` | `5ae3d24b0cba56a8e528f85f047b897fa19d7009ccc4aa732353aebb6878d419` (9) |
| `Toy.KInd.strengthening_needs_init_Q` | 19 counterexample | `Quot.sound`, `propext` | `1774c957fe7f026ed3e14648794343d561c57c102c68d27f092a75f582c619af` | `809ac97eaf3ec1d94a4d08cdc8096dd4be3c092633851cb0af92bd7a6b119dc8` (9) |
| `Toy.KInd.triangle_reachDiameter_one_reachRecurrenceDiameter_two` | 18 non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `1aadc9c58769d08ad2a19d8264212042a004ba89d432ccf109a817e6b7dc0db6` | `f111dfa595b35f9c893e78968fd5a1b980be4680481b75786be1eb4de8675a5b` (11) |

### Supporting declarations named in prose

These declarations are named in prose (findings, non-claims, escape hatches) but are not card-referenced names, so they carry no recorded statement hash; they are built and axiom-audited with the library (`audit/axioms.json`). The three theorems in `KInd/Remarks.lean` back non-claims of results 14, 18 and 22.

| Name | Module | Axioms |
| :--- | :--- | :--- |
| `Toy.KInd.ReachDiameterBound.mono` | `KInd/BMC.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.allInitChain_reachDiameter_zero_reachRecurrenceDiameter_pred` | `KInd/Remarks.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.base_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.base_one_iff_exactBase_zero` | `KInd/Remarks.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.base_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.base_zero_vacuous` | `KInd/Examples.lean` | none |
| `Toy.KInd.bmc_iff_reachWithin` | `KInd/BMC.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.bmc_neg` | `KInd/Examples.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.bmc_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.branch4_futureSafe_inductive_without_simpleStep` | `KInd/Strengthening.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.chain_bmc_below_diameter` | `KInd/BMC.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.consecution_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.consecution_pos` | `KInd/Examples.lean` | none |
| `Toy.KInd.endpoint_only_exact_base_unsound_even_when_total` | `KInd/Remarks.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.futureSafe_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.futureSafe_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.initiation_neg` | `KInd/Examples.lean` | none |
| `Toy.KInd.initiation_pos` | `KInd/Examples.lean` | none |
| `Toy.KInd.invariant_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.invariant_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.isPath_neg` | `KInd/Examples.lean` | `propext` |
| `Toy.KInd.isPath_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.isReachDiameter_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.isReachDiameter_no_init` | `KInd/Examples.lean` | none |
| `Toy.KInd.isReachDiameter_pos` | `KInd/Examples.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.isReachRecurrenceDiameter_neg` | `KInd/Examples.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.isReachRecurrenceDiameter_no_init` | `KInd/Examples.lean` | none |
| `Toy.KInd.isReachRecurrenceDiameter_pos` | `KInd/Examples.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.isSimple_neg` | `KInd/Examples.lean` | `propext` |
| `Toy.KInd.isSimple_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.kinductive_futureSafe_strengthening` | `KInd/Strengthening.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.le_of_reachDiameter_lower_bound_of_reachRecurrenceBound` | `KInd/BMC.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.projected_simple_step_unsound` | `KInd/Tightness.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachDiameterBound_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachDiameterBound_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachIn_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachIn_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachIn_succ_iff` | `KInd/Basic.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachRecurrenceBound_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachRecurrenceBound_pos` | `KInd/Examples.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.reachWithin_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachWithin_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachWithin_succ_iff` | `KInd/BMC.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachable_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.reachable_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.selfLoop_reach_diameters_zero` | `KInd/Examples.lean` | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.KInd.simpleStep_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.simpleStep_not_step` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.simpleStep_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.simpleStep_two_iff` | `KInd/Basic.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.starChain_reachDiameter_one_no_reachRecurrenceBound` | `KInd/BMC.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.step_neg` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.step_pos` | `KInd/Examples.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.step_two_iff` | `KInd/Basic.lean` | `Quot.sound`, `propext` |
| `Toy.KInd.twoInd_futureSafe_one_iff` | `KInd/Strengthening.lean` | `Quot.sound`, `propext` |

### Primary sources

Each record below was checked on the observation date: every DOI resolves through the DOI handle system, both Archive of Formal Proofs entry pages and the Coq repository are reachable, and title, authors, venue, year and pages of the papers listed as subjects in `REPORT.json` were cross-checked against dblp. The status says how much of each source was read; claims about a source in the findings are limited accordingly.

- M. Sheeran, S. Singh, G. Stålmarck, 'Checking Safety Properties Using Induction and a SAT-Solver', FMCAD 2000, LNCS 1954, pp. 127-144 (pages as on the publisher's page; the dblp record conf/fmcad/SheeranSS00 lists pp. 108-125), doi:10.1007/3-540-40922-X_8. *Text read. Page-range conflict: the publisher's page for this DOI gives pp. 127–144 and the dblp record conf/fmcad/SheeranSS00 gives pp. 108–125 (both rechecked on the observation date); this report quotes the publisher's range and records both.*
- D. Jovanović, B. Dutertre, 'Property-Directed k-Induction', FMCAD 2016, pp. 85-92, doi:10.1109/FMCAD.2016.7886665. *Text read (authors' copy), including Definition II.2, footnote 3 and Lemmas III.1–III.2.*
- N. Eén, N. Sörensson, 'Temporal Induction by Incremental SAT Solving', BMC 2003 (workshop), ENTCS 89(4), pp. 543-560, doi:10.1016/S1571-0661(05)82542-3 (content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis). *Content read from its reprint as Chapter 4 of N. Sörensson's 2008 doctoral thesis; the ENTCS original was not consulted, so wording may differ.*
- D. Ishii, S. Fujii, 'Formalizing the Soundness of the Encoding Methods of SAT-based Model Checking', TASE 2020, pp. 105-112, doi:10.1109/TASE49443.2020.00023 (arXiv:2006.13613; Coq development at https://github.com/dsksh/coq-smc). *Text read (arXiv:2006.13613), together with `src/KInduction.v`, `src/Forward.v` and `README.md` of the Coq repository https://github.com/dsksh/coq-smc (the revision consulted was not recorded; on the observation date the default branch `master` is at commit `60e63dc612eeffe7ed5ad4a658fdacf30709b19a`, committed 2022-03-10, and the repository's last push is the same day).*
- K. Batz, B. L. Kaminski, L. Kehrer, G. Klein, H. Urbat, T. Schmid, 'The Algebra of Iterative Constructions', Archive of Formal Proofs, April 29, 2026, https://www.isa-afp.org/entries/Iteration_Algebra.html. *Entry page and abstract only.*
- A. Gurfinkel, A. Ivrii, 'K-Induction without Unrolling', FMCAD 2017, pp. 148-155, doi:10.23919/FMCAD.2017.8102253. *Text read (conference preprint).*
- P. Bjesse, K. Claessen, 'SAT-Based Verification without State Space Traversal', FMCAD 2000, LNCS 1954, pp. 372-389, doi:10.1007/3-540-40922-X_23. *Bibliographic data only; text not consulted.*
- L. de Moura, H. Rueß, M. Sorea, 'Bounded Model Checking and Induction: From Refutation to Verification', CAV 2003, LNCS 2725, pp. 14-26, doi:10.1007/978-3-540-45069-6_2. *Abstract and bibliographic data only.*
- A. F. Donaldson, L. Haller, D. Kroening, P. Rümmer, 'Software Verification Using k-Induction', SAS 2011, LNCS 6887, pp. 351-368, doi:10.1007/978-3-642-23702-7_26. *Bibliographic data only; text not consulted.*
- A. Biere, A. Cimatti, E. M. Clarke, Y. Zhu, 'Symbolic Model Checking without BDDs', TACAS 1999, LNCS 1579, pp. 193-207, doi:10.1007/3-540-49059-0_14. *Text read in the technical-report version (CMU-CS-99-101); statement numbers are the report's and may differ in the published version.*
- D. Kroening, O. Strichman, 'Efficient Computation of Recurrence Diameters', VMCAI 2003, LNCS 2575, pp. 298-309, doi:10.1007/3-540-36384-X_24. *Text read (copy with the LNCS page numbers).*
- A. Biere, A. Cimatti, E. M. Clarke, O. Strichman, Y. Zhu, 'Bounded Model Checking', Advances in Computers 58, pp. 117-148, 2003, doi:10.1016/S0065-2458(03)58003-2. *Bibliographic data only; text not consulted.*
- A. Biere, 'Bounded Model Checking', in Handbook of Satisfiability, 2nd ed., FAIA 336, pp. 739-764, IOS Press, 2021, doi:10.3233/FAIA201002 (1st ed. 2009, FAIA 185, pp. 457-481, doi:10.3233/978-1-58603-929-5-457). *Bibliographic data only; text not consulted.*
- F. Kurz, M. Abdulaziz, 'Upper Bounding Diameters of State Spaces of Factored Transition Systems', Archive of Formal Proofs, October 12, 2018, https://www.isa-afp.org/entries/Factored_Transition_System_Bounding.html. *Entry page and abstract only.*
- E. M. Clarke, D. Kroening, J. Ouaknine, O. Strichman, 'Completeness and Complexity of Bounded Model Checking', VMCAI 2004, LNCS 2937, pp. 85-96, doi:10.1007/978-3-540-24622-0_9. *Abstract and bibliographic data only.*
- A. R. Bradley, 'SAT-Based Model Checking without Unrolling', VMCAI 2011, LNCS 6538, pp. 70-87, doi:10.1007/978-3-642-18275-4_7. *Text read (Section 3 in full).*
- Z. Manna, A. Pnueli, 'Temporal Verification of Reactive Systems: Safety', Springer, 1995, ISBN 978-0-387-94459-3, doi:10.1007/978-1-4612-4222-2. *Bibliographic data only; text not consulted.*
- K. Batz, M. Chen, B. L. Kaminski, J.-P. Katoen, C. Matheja, P. Schröer, 'Latticed k-Induction with an Application to Probabilistic Programs', CAV 2021, LNCS 12760, pp. 524-549, doi:10.1007/978-3-030-81688-9_25. *Text read (publisher's open-access HTML, which has no page numbers).*

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`, on first use) and `python3`. The Lean project has no dependencies, so no other download is needed.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, scans every Lean source for `sorry`, `admit`, `native_decide` and `axiom` declarations, and then runs an inline Lean audit program that (1) computes `collectAxioms` for every declaration of the `KInd` library and fails if any axiom other than `propext`, `Classical.choice`, `Quot.sound` appears, and (2) recomputes the statement and closure hashes of every name referenced by `results.json` or recorded in `audit/statements.json` and compares them with the recorded values. Exactly what is hashed:

- **statement hash:** SHA-256 of the UTF-8 text of `repr` of the declaration's type (the elaborated Lean `Expr`, not the source text);
- **closure hash:** SHA-256 of the newline-joined, sorted list of entries `name : repr(type)` (followed by ` := repr(value)` for definitions; theorem bodies are excluded) for every constant of the `KInd` modules reachable from the statement's type through types and definition values, including constructors of inductive types; the closure size is the number of entries.

Expected result: `ok   lake build`, `ok   axioms (303 declarations)`, `ok   statement hashes (98 hashed names; 0 referenced names exist but carry no recorded hash)`, then `REVALIDATED`; exit status 0.

**Manual check of the axioms.** From `lean/`:

```sh
lake build
lake env lean RevalidationAudit.lean
```

`RevalidationAudit.lean` imports the library and runs `#print axioms` for every card-referenced name; each line must report a subset of `propext`, `Classical.choice`, `Quot.sound` (or no axioms).

**What the checks do and do not establish.** A pass shows that the stated theorems are proved by the Lean kernel from the standard axioms and that their statements and the definitions they depend on are byte-for-byte those recorded here (as Lean `repr` text under this toolchain). It does not re-check the prose, the citations or the modeling bridges. Changing a proof leaves both hashes unchanged; changing a definition in `KInd/Basic.lean` or a concrete system changes the closure hash of every dependent name. The `repr` text, and therefore the hashes, can change across Lean releases: under a different toolchain, a hash mismatch alone does not show a changed statement, and the statements must be compared by reading `lean/KInd/*.lean` against the quotations in Findings.
