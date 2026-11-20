import Toy.Obs.Defs

/-!
# Concrete Reference Moore Machines

Concrete finite and parametric Moore machines used as witnesses,
positive/negative definition examples, hypothesis-tightness counterexamples,
and positive controls across the package.
-/

namespace Toy.Obs

/-- Two-state alternating machine over `Bool`: outputs its current bit and
flips it on every input. Reachable from `false` and behavior-injective. -/
def toggleMachine : Moore Unit Bool Bool where
  step b _ := !b
  out b := b

/-- Dual of `toggleMachine`: flips its state on every input and outputs the
negation of its state. Isomorphic to `toggleMachine` via `Bool.not`. -/
def dualToggleMachine : Moore Unit Bool Bool where
  step b _ := !b
  out b := !b

/-- Single-state machine that always outputs `false`. -/
def constFalseMachine : Moore Unit Bool Unit where
  step _ _ := ()
  out _ := false

/-- Single-state machine that always outputs `true`. -/
def constTrueMachine : Moore Unit Bool Unit where
  step _ _ := ()
  out _ := true

/-- Two-state identity-transition machine: outputs its current bit and never
changes state. Behavior-injective, but not all-reachable from `false`. -/
def idBoolMachine : Moore Unit Bool Bool where
  step b _ := b
  out b := b

/-- Two-state toggling machine with constant `false` output. All-reachable
from `false`, but not behavior-injective since both states share constant
`false` behavior. -/
def redundantToggleMachine : Moore Unit Bool Bool where
  step b _ := !b
  out _ := false

/-- Three-state carrier used to separate reachability, observability,
immediate-output equality, and bisimulation. -/
inductive ThreeState where
  | s0
  | s1
  | s2
  deriving DecidableEq

/-- Three-state reachable non-minimal toggle machine:
`s0 → s2 → s1 → s2 → s1 …` with `out s0 = false`, `out s1 = false`,
`out s2 = true`. Every state is reachable from `s0`, yet `s0` and `s1` are
distinct states with identical alternating behavior matching `toggleMachine`
from `false`. -/
def threeStateToggle : Moore Unit Bool ThreeState where
  step
    | .s0, _ => .s2
    | .s1, _ => .s2
    | .s2, _ => .s1
  out
    | .s0 => false
    | .s1 => false
    | .s2 => true

/-- Three-state machine whose states `s0` and `s1` share the same immediate
output (`false`) but diverge after one step (`s0 → s0` emitting `false`,
`s1 → s2` emitting `true`). -/
def delayedDiffMachine : Moore Unit Bool ThreeState where
  step
    | .s0, _ => .s0
    | .s1, _ => .s2
    | .s2, _ => .s2
  out
    | .s0 => false
    | .s1 => false
    | .s2 => true

/-- Split-state machine on `Bool × Nat` satisfying both code-level syntactic
and extensional stepwise non-dependence (`OutIgnoresHidden` and
`StepFstIgnoresHidden`): the observable bit toggles on each input while the
hidden counter increments independently without affecting `out` or the
observable transition. -/
def syntacticIndependentMachine : Moore Unit Bool (Bool × Nat) where
  step p _ := (!p.1, p.2 + 1)
  out p := p.1

/-- Split-state machine on `Unit × Bool` whose output directly reads the
hidden bit `h` while its observable component `Unit` is trivially independent
of `h`. -/
def leakyOutMachine : Moore Unit Bool (Unit × Bool) where
  step p _ := p
  out p := p.2

/-- Split-state machine on `Bool × Bool` whose immediate output ignores `h`,
but whose first step copies `h` directly into the observed bit so that `h`
leaks after a single step. -/
def oneStepLeakMachine : Moore Unit Bool (Bool × Bool) where
  step p _ := (p.2, p.2)
  out p := p.1

/-- Split-state machine on `(Bool × Bool) × Bool` demonstrating that syntactic
non-dependence is not necessary for erasability: `A = Bool × Bool` pairs an
observable toggling bit `x` with an unobserved tag bit `t`, while `H = Bool`
tracks the previous input and writes itself into `t` on every step. Thus `H`
actively influences the `A`-component of `step` (even on reachable states),
yet `H` is globally erasable because `t` never affects future outputs. -/
def redundantTagMachine : Moore Bool Bool ((Bool × Bool) × Bool) where
  step p i := ((!p.1.1, p.2), i)
  out p := p.1.1

/-- Two-slot delayed-channel machine on `(Bool × Bool) × Bool`:
`out` reads only the first observable bit `x`, while each step shifts the
buffer bit `y` into `x` and copies the hidden bit `h` into `y` (`h` itself
never changes). Consequently `out` and 1-step `out` completely ignore `h`,
yet `h` reaches `out` after two steps. -/
def delayedChannel2 : Moore Unit Bool ((Bool × Bool) × Bool) where
  step p _ := ((p.1.2, p.2), p.2)
  out p := p.1.1

/-- Parametric `(k + 2)`-slot shift-register channel with observable state
`Fin (k + 2) → Bool` and hidden bit `Bool`. Output reads only slot `0`; each
step shifts slot `j + 1` into slot `j` and loads `h` into slot `k + 1`.
Every bounded-horizon check of length `< k + 2` passes, while word length
`k + 2` exposes `h`. -/
def delayedChannel (k : Nat) : Moore Unit Bool ((Fin (k + 2) → Bool) × Bool) where
  step p _ :=
    (fun j => if hlt : j.val + 1 < k + 2 then p.1 ⟨j.val + 1, hlt⟩ else p.2, p.2)
  out p := p.1 ⟨0, Nat.zero_lt_succ _⟩

/-- Positive-control counterpart to `delayedChannel k`: identical `(k + 2)`-slot
shift register except that the incoming slot `k + 1` loads the constant `false`
instead of `h`, restoring `StepFstIgnoresHidden` and eliminating the hidden
channel for all word lengths. -/
def delayedChannelFixed (k : Nat) : Moore Unit Bool ((Fin (k + 2) → Bool) × Bool) where
  step p _ :=
    (fun j => if hlt : j.val + 1 < k + 2 then p.1 ⟨j.val + 1, hlt⟩ else false, p.2)
  out p := p.1 ⟨0, Nat.zero_lt_succ _⟩

/-- Degenerate split-state machine with empty hidden state `H = Empty` and
empty output `O = Empty`: satisfies every universal hidden-state law vacuously,
yet admits no reduced machine on `A = Unit` because `Unit → Empty` is empty. -/
def emptyHiddenMachine : Moore Unit Empty (Unit × Empty) where
  step p _ := nomatch p.2
  out p := nomatch p.2

/-- Split-state machine on `Bool × Bool` whose hidden bit is invisible from
every state reachable from `(false, h)` (since `a = false` is preserved by
`step`), yet fails global `BehIgnoresHidden` at the unreachable state
`a = true`. Separates reachable-only erasability from global `BehIgnoresHidden`. -/
def gatedLeak : Moore Unit Bool (Bool × Bool) where
  step p _ := p
  out p := p.1 && p.2

end Toy.Obs
