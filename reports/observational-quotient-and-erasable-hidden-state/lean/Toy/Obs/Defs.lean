/-!
# Core Definitions: Deterministic Moore Machines, Bisimulation, Minimal Realization, and Hidden State

This module defines a self-contained model of deterministic Moore machines,
their observable input-output behaviors, bisimulations, homomorphisms,
isomorphisms, the final coalgebra of behaviors, the reachable minimal
realization from an initial state, and state-splitting predicates for
erasable hidden state (`Q = A × H`).

Each law or structural property is defined as a separate named `Prop` so
that every theorem states the exact hypotheses it depends on.
-/

namespace Toy.Obs

universe u u₁ u₂ v w

/-! ## Deterministic Moore Machines and Observable Behavior -/

/-- A deterministic Moore machine with input alphabet `I`, output alphabet `O`,
and state space `Q`. Models a total, deterministic transition system whose
externally visible observation `out q` depends only on the current state `q`
and whose next state `step q i` (often written `δ(q, i)`) is determined by
the current state and a single input symbol. -/
structure Moore (I : Type v) (O : Type w) (Q : Type u) where
  /-- Single-step state transition function `δ : Q → I → Q`. -/
  step : Q → I → Q
  /-- State observation function `out : Q → O`. -/
  out : Q → O

/-- Multi-step transition function of a Moore machine, folding inputs from left
to right: `M.run q (i :: w) = M.run (M.step q i) w`. Captures the state reached
after executing a finite input trace `w` starting from `q`. -/
def Moore.run {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) : Q → List I → Q
  | q, [] => q
  | q, i :: w => M.run (M.step q i) w

@[simp]
theorem Moore.run_nil {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) : M.run q [] = q := rfl

@[simp]
theorem Moore.run_cons {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) (i : I) (w : List I) :
    M.run q (i :: w) = M.run (M.step q i) w := rfl

theorem Moore.run_append {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) (u w : List I) :
    M.run q (u ++ w) = M.run (M.run q u) w := by
  induction u generalizing q with
  | nil => rfl
  | cons i u ih => exact ih (M.step q i)

theorem Moore.run_append_singleton {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) (u : List I) (i : I) :
    M.run q (u ++ [i]) = M.step (M.run q u) i := by
  rw [Moore.run_append]
  rfl

/-- Observable behavior of a state `q`: maps every finite input word `w` to the
output emitted after running `w` from `q`. Captures the complete black-box
extensional semantics of `q`. -/
def Moore.beh {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) : List I → O :=
  fun w => M.out (M.run q w)

@[simp]
theorem Moore.beh_nil {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) : M.beh q [] = M.out q := rfl

@[simp]
theorem Moore.beh_cons {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) (i : I) (w : List I) :
    M.beh q (i :: w) = M.beh (M.step q i) w := rfl

theorem Moore.beh_run {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q : Q) (u w : List I) :
    M.beh (M.run q u) w = M.beh q (u ++ w) := by
  simp only [Moore.beh, Moore.run_append]

/-! ## Observational Equivalence and Bisimulation -/

/-- Observational equivalence of two states in a Moore machine: `q₁` and `q₂`
produce identical outputs on every finite input sequence. Captures behavioral
indistinguishability to an external observer. -/
def ObsEq {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₁ q₂ : Q) : Prop :=
  M.beh q₁ = M.beh q₂

/-- Output-preservation law for a state relation `R`: related states emit the
same immediate output. Corresponds to output consistency in unwinding
theories and the head condition of a coalgebraic bisimulation. -/
def RelPreservesOut {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (R : Q → Q → Prop) : Prop :=
  ∀ q₁ q₂, R q₁ q₂ → M.out q₁ = M.out q₂

/-- Step-closure law for a state relation `R`: stepping any pair of related
states by the same input yields a related pair of successor states.
Corresponds to step consistency in unwinding theories and the transition
closure condition of a deterministic bisimulation. -/
def RelStepClosed {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (R : Q → Q → Prop) : Prop :=
  ∀ q₁ q₂, R q₁ q₂ → ∀ i, R (M.step q₁ i) (M.step q₂ i)

/-- A bisimulation on a Moore machine `M` is a state relation that both
preserves immediate outputs and is closed under every single-step transition.
Captures a local, coinductive witness of behavioral equivalence without
requiring `R` to be an equivalence relation. -/
def IsBisim {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (R : Q → Q → Prop) : Prop :=
  RelPreservesOut M R ∧ RelStepClosed M R

/-! ## Homomorphisms, Isomorphisms, and the Final Machine -/

/-- Output-preservation law for a state map `f : Q₁ → Q₂` between two Moore
machines over the same alphabets: `M₂.out (f q) = M₁.out q` for all `q`. -/
def PreservesOut {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂) (f : Q₁ → Q₂) : Prop :=
  ∀ q, M₂.out (f q) = M₁.out q

/-- Transition-commutation law for a state map `f : Q₁ → Q₂` between two Moore
machines: `f (M₁.step q i) = M₂.step (f q) i` for all `q` and `i`. -/
def PreservesStep {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂) (f : Q₁ → Q₂) : Prop :=
  ∀ q i, f (M₁.step q i) = M₂.step (f q) i

/-- A Moore machine homomorphism (coalgebra morphism for the Moore functor
`Q ↦ O × (I → Q)`): a state map preserving both immediate outputs and
single-step transitions. -/
def IsHom {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂) (f : Q₁ → Q₂) : Prop :=
  PreservesOut M₁ M₂ f ∧ PreservesStep M₁ M₂ f

/-- Initial-state preservation law for a state map `f : Q₁ → Q₂` between
pointed Moore machines with distinguished initial states `q₁` and `q₂`. -/
def PreservesInit {Q₁ : Type u₁} {Q₂ : Type u₂}
    (q₁ : Q₁) (q₂ : Q₂) (f : Q₁ → Q₂) : Prop :=
  f q₁ = q₂

/-- Surjectivity of a function `f : α → β`: every target element has at least
one preimage. Used to state that every reachable machine maps onto the
canonical minimal quotient. -/
def Surjective {α : Type u₁} {β : Type u₂} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- A Moore machine isomorphism witnessed by explicit forward and inverse maps
`toFun : Q₁ → Q₂` and `invFun : Q₂ → Q₁`: both maps are homomorphisms and
they are two-sided inverses. Captures structural identity of state spaces up
to renaming of states. -/
def IsIso {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂)
    (toFun : Q₁ → Q₂) (invFun : Q₂ → Q₁) : Prop :=
  IsHom M₁ M₂ toFun ∧
  IsHom M₂ M₁ invFun ∧
  (∀ q₁, invFun (toFun q₁) = q₁) ∧
  (∀ q₂, toFun (invFun q₂) = q₂)

/-- The final Moore machine over input alphabet `I` and output alphabet `O`:
states are all total behavior functions `List I → O`, immediate output is
evaluation on the empty word `f []`, and stepping by `i` takes the left
Brzozowski derivative `fun w => f (i :: w)`. Captures the canonical semantic
domain of all observable behaviors. -/
def finalMachine (I : Type v) (O : Type w) : Moore I O (List I → O) where
  step f i := fun w => f (i :: w)
  out f := f []

/-! ## Reachability, Observability, and Minimal Realization -/

/-- Reachability of state `q` from initial state `q₀` in machine `M`: there
exists a finite input word `w` driving `q₀` to `q`. Captures which states
can actually be visited during execution from `q₀`. -/
def Reachable {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ q : Q) : Prop :=
  ∃ w : List I, M.run q₀ w = q

/-- Global reachability of a pointed Moore machine `(M, q₀)`: every state of
`Q` is reachable from `q₀` (no dead/unreachable states). -/
def AllReachable {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) : Prop :=
  ∀ q : Q, Reachable M q₀ q

/-- Observability (also called reducedness or behavior injectivity) of a Moore
machine `M`: distinct states always have distinct observable behaviors
(`M.beh q₁ = M.beh q₂ → q₁ = q₂`). Captures the absence of observationally
redundant states. -/
def BehInjective {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) : Prop :=
  ∀ q₁ q₂ : Q, M.beh q₁ = M.beh q₂ → q₁ = q₂

/-- The carrier type of the canonical minimal realization of `(M, q₀)`: the
subtype of behaviors `List I → O` lying in the reachable image of `M.beh`
starting from `q₀`. Equivalently, the set of left derivatives of `M.beh q₀`. -/
abbrev ReachableBeh {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) : Type (max v w) :=
  { f : List I → O // ∃ w : List I, M.beh (M.run q₀ w) = f }

/-- The canonical minimal Moore machine associated with `(M, q₀)`, whose states
are the reachable image `ReachableBeh M q₀` of `M.beh` equipped with the
restriction of the final machine's `out` and derivative `step`. -/
def minimalMachine {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) : Moore I O (ReachableBeh M q₀) where
  step s i :=
    ⟨(finalMachine I O).step s.1 i, by
      rcases s.2 with ⟨w, hw⟩
      refine ⟨w ++ [i], ?_⟩
      funext u
      rw [← hw, Moore.run_append_singleton]
      rfl⟩
  out s := s.1 []

/-- Distinguished initial state of `minimalMachine M q₀`, namely `M.beh q₀`
reached by the empty word `[]`. -/
def minimalInit {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) : ReachableBeh M q₀ :=
  ⟨M.beh q₀, ⟨[], rfl⟩⟩

/-- The canonical quotient map from any all-reachable machine `(M', q₀')` with
the same initial behavior as `(M, q₀)` onto `minimalMachine M q₀`, sending
each state `q'` to its observable behavior `M'.beh q'`. -/
def toMinimalQuotient
    {I : Type v} {O : Type w} {Q : Type u₁} {Q' : Type u₂}
    (M : Moore I O Q) (q₀ : Q)
    (M' : Moore I O Q') (q₀' : Q')
    (hReach : AllReachable M' q₀')
    (hInitBeh : M'.beh q₀' = M.beh q₀)
    (q' : Q') : ReachableBeh M q₀ :=
  ⟨M'.beh q', by
    rcases hReach q' with ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    funext u
    rw [Moore.beh_run, Moore.beh_run, hInitBeh]⟩

/-- The canonical state map between two reachable machines `(M₁, q₁)` and
`(M₂, q₂)`: chooses a reaching word `w` for `q : Q₁` from `q₁` and runs `w`
in `M₂` from `q₂`. When both machines are also behavior-injective and share
the same initial behavior, this map is independent of the chosen word and
defines the unique machine isomorphism. -/
noncomputable def minimalIsoFun
    {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    (M₁ : Moore I O Q₁) (q₁ : Q₁)
    (M₂ : Moore I O Q₂) (q₂ : Q₂)
    (hReach₁ : AllReachable M₁ q₁) : Q₁ → Q₂ :=
  fun q => M₂.run q₂ (Classical.choose (hReach₁ q))

/-! ## Split State `Q = A × H` and Hidden-State Erasability -/

/-- Zero-step extensional non-dependence on the hidden component `H`: `M.out`
returns the same output for all hidden values at a fixed observable state `a`
(output consistency with respect to `SameFst`). Captures that immediate
observations are extensionally independent of hidden bookkeeping; code-level
syntactic checks forbidding `out` from reading `H` are a strictly stronger
special case. -/
def OutIgnoresHidden {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂, M.out (a, h₁) = M.out (a, h₂)

/-- Single-step extensional non-dependence of the observable transition
component on `H`: `(M.step (a, h) i).1` returns the same next `A`-state for all
`h` (von Oheimb's functional independence; step consistency with respect to
`SameFst`). Captures that hidden bookkeeping does not extensionally affect the
next observable state component; code-level syntactic checks forbidding
`step.1` from reading `H` are a strictly stronger special case. -/
def StepFstIgnoresHidden {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂ i, (M.step (a, h₁) i).1 = (M.step (a, h₂) i).1

/-- Observational injectivity (reducedness) of the observable state component
`A` at each hidden state `h`: distinct observable states `a₁ ≠ a₂` never induce
identical observable behaviors at a common hidden state `h`. Captures that `A`
itself contains no observationally redundant states. -/
def ObsInjectiveFst {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) : Prop :=
  ∀ a₁ a₂ h, M.beh (a₁, h) = M.beh (a₂, h) → a₁ = a₂

/-- One-step output non-dependence on `H`: after taking any single transition
step from `(a, h)`, the emitted output does not depend on `h`. Captures a
1-step lookahead check that tests whether `H` affects output after one step. -/
def OneStepOutIgnoresHidden {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂ i, M.out (M.step (a, h₁) i) = M.out (M.step (a, h₂) i)

/-- Bounded-horizon output non-dependence on `H` up to word length `< k`:
no input sequence of length strictly less than `k` can distinguish `(a, h₁)`
from `(a, h₂)`. Captures finite-depth observational checking. -/
def BoundedBehIgnoresHidden {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) (k : Nat) : Prop :=
  ∀ a h₁ h₂ w, w.length < k → M.beh (a, h₁) w = M.beh (a, h₂) w

/-- Exact behavioral non-dependence on `H` (two-level deterministic nonleakage
of `H`): for every observable state `a`, the complete input-output behavior
`M.beh (a, h)` is independent of `h`. Captures uniform, global semantic
erasability of the hidden component `H` across all states `A × H`. -/
def BehIgnoresHidden {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)

/-- The observable-projection equivalence relation on `A × H`: relates two
split states iff they have identical observable components `A`. As shown in
`isBisim_sameFst_iff`, `SameFst` covers `H` and its bisimulation conditions
coincide with `OutIgnoresHidden M ∧ StepFstIgnoresHidden M`. -/
def SameFst {A : Type u₁} {H : Type u₂} (p₁ p₂ : A × H) : Prop :=
  p₁.1 = p₂.1

/-- Coverage condition for an inductive unwinding relation `R` on `A × H`:
`R` relates every pair of states sharing the same observable component `a`
(equivalently, `SameFst` is contained in `R`). -/
def CoversHidden {A : Type u₁} {H : Type u₂} (R : (A × H) → (A × H) → Prop) : Prop :=
  ∀ a h₁ h₂, R (a, h₁) (a, h₂)

/-- The reduced Moore machine on `A` obtained by erasing `H` and evaluating
`M.out` and the `A`-component of `M.step` at a fixed dummy hidden state
`h₀ : H`. Captures deleting execution-only bookkeeping by replacing it with
an arbitrary constant placeholder. -/
def eraseHidden {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) (h₀ : H) : Moore I O A where
  step a i := (M.step (a, h₀) i).1
  out a := M.out (a, h₀)

end Toy.Obs
