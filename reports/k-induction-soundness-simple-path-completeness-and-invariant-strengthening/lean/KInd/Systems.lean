/-!
# Small concrete transition systems used as examples and counterexamples

Most systems here are finite (state type `Fin n`) with decidable components, so concrete facts
about them reduce to `decide` after the path checks are unfolded to finitely many states. The
families `FinChain m` and `TriangleN m` are parametric in the number of states; `NatSucc` and
`StarChain` are infinite (state type `Nat`).
-/

namespace Toy.KInd

/- `Chain`: states `Fin 3`; initial state `0`; transitions `0 → 1 → 2`; `P` excludes `2`.
Its reachability diameter and reachability recurrence diameter are both `2`, and `P` is not
invariant. -/
namespace Chain
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t => t.val = s.val + 1
abbrev P : Fin 3 → Prop := fun s => s.val ≠ 2
end Chain

/- `OneEdge`: states `Fin 2`; initial state `0`; one transition `0 → 1`; `P` is `{0}`.
Its reachability recurrence diameter is `1`, and `P` is not invariant. -/
namespace OneEdge
abbrev I : Fin 2 → Prop := fun s => s.val = 0
abbrev T : Fin 2 → Fin 2 → Prop := fun s t => s.val = 0 ∧ t.val = 1
abbrev P : Fin 2 → Prop := fun s => s.val = 0
end OneEdge

/- `Triangle`: states `Fin 3`; initial state `0`; transitions `s → t` for `s < t`.
Its reachability diameter is `1` (every state is one step from `0`) but its reachability
recurrence diameter is `2`
(the simple path `0 → 1 → 2`). -/
namespace Triangle
abbrev I : Fin 3 → Prop := fun s => s.val = 0
abbrev T : Fin 3 → Fin 3 → Prop := fun s t => s.val < t.val
end Triangle

/- `Stuck`: one state `0`, which is initial; no transitions; `P` is empty. -/
namespace Stuck
abbrev I : Fin 1 → Prop := fun _ => True
abbrev T : Fin 1 → Fin 1 → Prop := fun _ _ => False
abbrev P : Fin 1 → Prop := fun _ => False
end Stuck

/- `TriangleN m`: states `Fin (m + 2)`; initial state `0`; transitions `s → t` for `s < t` (a
transitive tournament, i.e. a complete DAG). Every state is one step from `0`, so its
reachability diameter is `1`, but the simple path `0 → 1 → ⋯ → m + 1` has `m + 1` transitions.
`Triangle` is the case `m = 1`. -/
namespace TriangleN
abbrev I (m : Nat) : Fin (m + 2) → Prop := fun s => s.val = 0
abbrev T (m : Nat) : Fin (m + 2) → Fin (m + 2) → Prop := fun s t => s.val < t.val
end TriangleN

/- `FinChain m`: states `Fin (m + 2)`; initial state `0`; transitions `i → i + 1`; `P` excludes
the last state `m + 1`, which is reachable only in `m + 1` transitions. -/
namespace FinChain
abbrev I (m : Nat) : Fin (m + 2) → Prop := fun s => s.val = 0
abbrev T (m : Nat) : Fin (m + 2) → Fin (m + 2) → Prop := fun s t => t.val = s.val + 1
abbrev P (m : Nat) : Fin (m + 2) → Prop := fun s => s.val ≠ m + 1
end FinChain

/- `NatSucc`: the infinite counter on `Nat`; initial state `0`; transitions `s → s + 1`. -/
namespace NatSucc
abbrev I : Nat → Prop := fun s => s = 0
abbrev T : Nat → Nat → Prop := fun s t => t = s + 1
end NatSucc

/- `StarChain`: states `Nat`; initial state `0`; transitions `0 → t` for every `t ≥ 1` and
`s → s + 1` for every `s ≥ 1`. Every state is reachable in at most one transition, but simple
paths from `0` are arbitrarily long. -/
namespace StarChain
abbrev I : Nat → Prop := fun s => s = 0
abbrev T : Nat → Nat → Prop := fun s t => (s = 0 ∧ 1 ≤ t) ∨ (1 ≤ s ∧ t = s + 1)
end StarChain

/- `Branch4`: states `Fin 4`; initial state `0` with a self-loop; unreachable transitions
`1 → 2`, `2 → 3`, `1 → 3`; `P` excludes `3`. -/
namespace Branch4
abbrev I : Fin 4 → Prop := fun s => s.val = 0
abbrev T : Fin 4 → Fin 4 → Prop := fun s t =>
  (s.val = 0 ∧ t.val = 0) ∨ (s.val = 1 ∧ t.val = 2) ∨ (s.val = 2 ∧ t.val = 3) ∨
    (s.val = 1 ∧ t.val = 3)
abbrev P : Fin 4 → Prop := fun s => s.val ≠ 3
end Branch4

end Toy.KInd
